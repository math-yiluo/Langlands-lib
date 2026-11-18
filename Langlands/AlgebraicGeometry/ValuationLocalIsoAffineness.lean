import Langlands.AlgebraicGeometry.ValuationAffinenessGeometry
import Langlands.AlgebraicGeometry.EtaleGeometricLifts
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Affineness of quasi-compact separated local isomorphisms over valuation domains -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- An affine nonempty open inside a valuation spectrum is a local scheme. -/
theorem isLocalRing_of_openImmersion_to_valuationSpectrum
    (R B : CommRingCat.{u}) [IsDomain R] [ValuationRing R] [Nontrivial B]
    (f : Spec B ⟶ Spec R) [IsOpenImmersion f] : IsLocalRing B := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m, hm, fun n hn => ?_⟩
  let p : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  let q : PrimeSpectrum B := ⟨n, hn.isPrime⟩
  have htotal : f p ⤳ f q ∨ f q ⤳ f p := by
    rcases le_total (f p).asIdeal (f q).asIdeal with h | h
    · exact Or.inl ((PrimeSpectrum.le_iff_specializes (f p) (f q)).mp h)
    · exact Or.inr ((PrimeSpectrum.le_iff_specializes (f q) (f p)).mp h)
  rcases htotal with h | h
  · have hpq : p ⤳ q := f.isOpenEmbedding.isInducing.specializes_iff.mp h
    exact (hm.eq_of_le hn.ne_top ((PrimeSpectrum.le_iff_specializes p q).mpr hpq)).symm
  · have hqp : q ⤳ p := f.isOpenEmbedding.isInducing.specializes_iff.mp h
    exact hn.eq_of_le hm.ne_top ((PrimeSpectrum.le_iff_specializes q p).mpr hqp)

/-- A local isomorphism to a valuation spectrum admits a local-spectrum open
chart containing every specified source point. -/
theorem exists_localSpectrum_chart_of_localIso_to_valuationSpectrum
    (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsLocalIso f] (x : X) :
    ∃ (B : CommRingCat.{u}) (_ : IsLocalRing B) (v : Spec B ⟶ X),
      IsOpenImmersion v ∧ x ∈ Set.range v := by
  obtain ⟨U, hxU, hU⟩ := IsLocalIso.exists_isOpenImmersion (f := f) x
  let : IsOpenImmersion (U.ι ≫ f) := hU
  let xU : (U : Scheme) := ⟨x, hxU⟩
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := (U : Scheme)) (U := ⊤) (x := xU) trivial
  let : Nonempty V := ⟨⟨xU, hxV⟩⟩
  let v : Spec Γ((U : Scheme), V) ⟶ X := hV.fromSpec ≫ U.ι
  let : IsOpenImmersion v := inferInstance
  let : IsOpenImmersion (v ≫ f) := by
    dsimp only [v]
    rw [Category.assoc]
    infer_instance
  let : IsLocalRing Γ((U : Scheme), V) :=
    isLocalRing_of_openImmersion_to_valuationSpectrum R _ (v ≫ f)
  refine ⟨_, inferInstance, v, inferInstance, ?_⟩
  obtain ⟨y, hy⟩ : xU ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hxV
  refine ⟨y, ?_⟩
  change U.ι (hV.fromSpec y) = x
  rw [hy]
  rfl

/-- A quasi-compact separated local isomorphism over a valuation domain is affine. -/
theorem isAffineHom_of_localIso_to_valuationSpectrum
    (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R)
    [QuasiCompact f] [IsSeparated f] [IsLocalIso f] : IsAffineHom f := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : Etale f := IsLocalIso.le_of_isZariskiLocalAtSource @Etale _ _ f inferInstance
  let : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  let : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  let : X.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion f.toNormalization
  choose B hB v hv hx using exists_localSpectrum_chart_of_localIso_to_valuationSpectrum R f
  let (x : X) : IsLocalRing (B x) := hB x
  let (x : X) : IsOpenImmersion (v x) := hv x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (v x))
    (fun x => (v x).isOpenEmbedding.isOpen_range)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have : IsAffine X := by
    apply isAffine_of_finite_localSpectrum_family X (fun i : t => B i) (fun i => v i)
    intro x
    obtain ⟨i, hi, y, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨⟨i, hi⟩, y, hy⟩
  infer_instance

/-- The canonical actual affine model in the valuation local-isomorphism case. -/
def valuationLocalIsoAffineIso
    (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R)
    [QuasiCompact f] [IsSeparated f] [IsLocalIso f] : X ≅ Spec Γ(X, ⊤) :=
  have := isAffineHom_of_localIso_to_valuationSpectrum R f
  have := isAffine_of_isAffineHom f
  X.isoSpec

end Langlands.AlgebraicGeometry
