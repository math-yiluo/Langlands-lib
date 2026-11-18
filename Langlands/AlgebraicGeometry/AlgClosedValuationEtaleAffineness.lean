import Langlands.AlgebraicGeometry.SplitStandardEtaleLocalIso
import Langlands.AlgebraicGeometry.ValuationLocalIsoAffineness
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Valuation.Integral

/-! # Etale affineness over valuation subrings of algebraically closed fields -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

private theorem localIso_of_open_neighbourhood_maps
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, ∃ (V : Scheme.{u}) (p : V ⟶ X),
      IsOpenImmersion p ∧ x ∈ Set.range p ∧ IsLocalIso (p ≫ f)) : IsLocalIso f := by
  classical
  choose V p hp hx hf using h
  let (x : X) : IsOpenImmersion (p x) := hp x
  let C : X.OpenCover := Scheme.Cover.mkOfCovers X V p
    (fun x => by obtain ⟨y, hy⟩ := hx x; exact ⟨x, y, hy⟩) hp
  exact IsZariskiLocalAtSource.of_openCover (P := @IsLocalIso) C hf

/-- If every monic polynomial over the base domain splits, every etale
algebra gives a local isomorphism on spectra. -/
theorem isLocalIso_spec_of_etale_of_allMonic_split
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.Etale R B]
    (hsplit : ∀ p : R[X], p.Monic → p.Splits) :
    IsLocalIso (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  apply localIso_of_open_neighbourhood_maps f
  intro x
  let : Algebra.FormallyEtale B (Localization.AtPrime x.asIdeal) :=
    .of_isLocalization x.asIdeal.primeCompl
  let : Algebra.IsEtaleAt R x.asIdeal :=
    Algebra.FormallyEtale.comp R B (Localization.AtPrime x.asIdeal)
  obtain ⟨b, hb, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) x.asIdeal
  let : Algebra.IsStandardEtale R (Localization.Away b) := hstd
  let P : StandardEtalePresentation R (Localization.Away b) :=
    Classical.choice (Algebra.IsStandardEtale.nonempty_standardEtalePresentation)
  let v := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))
  let : IsOpenImmersion v := inferInstance
  have hx : x ∈ Set.range v := by
    change x ∈ v.opensRange
    dsimp only [v]
    erw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) b]
    exact hb
  have he : v ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b))) := by
    rw [← Spec.map_comp]
    congr 1
  refine ⟨_, v, inferInstance, hx, ?_⟩
  rw [he]
  exact SplitStandardEtale.isLocalIso_of_splits P (hsplit P.f P.monic_f)

/-- Over an integrally closed domain with algebraically closed fraction field,
every etale morphism is a Zariski local isomorphism. -/
theorem isLocalIso_etale_of_isAlgClosed_fractionField
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Etale f] : IsLocalIso f := by
  apply IsZariskiLocalAtSource.of_openCover (P := @IsLocalIso) X.affineOpenCover.openCover
  intro i
  let B := X.affineOpenCover.X i
  let g := X.affineOpenCover.f i ≫ f
  let β : CommRingCat.of R ⟶ B := Spec.preimage g
  let : Algebra R B := β.hom.toAlgebra
  have he : Spec.map (CommRingCat.ofHom (algebraMap R B)) = g := Spec.map_preimage g
  have hg : Etale (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    rw [he]
    infer_instance
  let : Algebra.Etale R B := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hg)
  change IsLocalIso g
  rw [← he]
  exact isLocalIso_spec_of_etale_of_allMonic_split R B
    (fun p hp => monic_splits_of_isAlgClosed_fractionField (K := K) hp)

/-- A quasi-compact separated etale scheme over a valuation subring of an
algebraically closed field is affine, with no rank or noetherian condition. -/
theorem isAffineHom_etale_algClosedValuation
    (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [IsSeparated f] [Etale f] : IsAffineHom f := by
  let : IsLocalIso f := isLocalIso_etale_of_isAlgClosed_fractionField A K f
  exact isAffineHom_of_localIso_to_valuationSpectrum (CommRingCat.of A) f

/-- The actual canonical affine model of an etale scheme over an
algebraically closed valuation subring. -/
def algClosedValuationEtaleAffineIso
    (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [IsSeparated f] [Etale f] : X ≅ Spec Γ(X, ⊤) :=
  have := isAffineHom_etale_algClosedValuation K A f
  have := isAffine_of_isAffineHom f
  X.isoSpec

end Langlands.AlgebraicGeometry
