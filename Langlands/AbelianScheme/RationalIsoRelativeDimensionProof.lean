import Langlands.AbelianScheme.RationalIsoRelativeDimensionStatement
import Langlands.AbelianScheme.FieldMultiplicationIsogenyProof
import Langlands.CategoryTheory.RationalizationDenominators
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionProof
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Relative dimension under rational isomorphism of abelian schemes -/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.RationalIsoRelativeDimension

/-- Over a field, a nonempty scheme has at most one standard-smooth relative dimension. -/
theorem relDim_unique_of_field {K : Type u} [Field K] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of K)) {m g : ℕ} (hm : SmoothOfRelativeDimension m q)
    (hg : SmoothOfRelativeDimension g q) [Nonempty Y] : m = g := by
  have : Smooth q := hm.smooth
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨y, -, hy⟩ := nonempty_inter_closedPoints (X := Y) Set.univ_nonempty
    isClosed_univ.isLocallyClosed
  have h1 := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension K Y q m hm y hy
  have h2 := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension K Y q g hg y hy
  exact_mod_cast h1.symm.trans h2

/-- Over a field, a locally quasi-finite morphism from a nonempty proper scheme to a
separated scheme does not decrease the standard-smooth relative dimension. -/
theorem relDim_le_of_locallyQuasiFinite {K : Type u} [Field K] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ Y)
    (hφ : φ ≫ q = p) [LocallyQuasiFinite φ] [IsProper p] [IsSeparated q]
    {a b : ℕ} (ha : SmoothOfRelativeDimension a p) (hb : SmoothOfRelativeDimension b q)
    [Nonempty X] : a ≤ b := by
  have : Smooth p := ha.smooth
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (X := X) Set.univ_nonempty
    isClosed_univ.isLocallyClosed
  have : IsProper (φ ≫ q) := by rw [hφ]; infer_instance
  have : IsProper φ := IsProper.of_comp φ q
  have hφx : IsClosed ({φ x} : Set Y) := by
    simpa using φ.isClosedMap _ hx
  have h1 := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension K X p a ha x hx
  have h2 := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension K Y q b hb
    (φ x) hφx
  have h3 := Langlands.AlgebraicGeometry.quasiFiniteAtStalkDimension X Y φ inferInstance x
    (φ.quasiFiniteAt x)
  rw [h1, h2] at h3
  exact_mod_cast h3

/-- An affine standard-smooth chart of relative dimension `m` makes the restricted morphism
smooth of relative dimension `m`. -/
theorem smoothOfRelativeDimension_resLE {X S : Scheme.{u}} (f : X ⟶ S) (U : S.affineOpens)
    (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) {m : ℕ}
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m) :
    SmoothOfRelativeDimension m (f.resLE U V e) := by
  have hQi := RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := m)
  simp only [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension m),
    Scheme.Hom.appLE, homOfLE_leOfHom] at h ⊢
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp <|
      (HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension m)).respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m)))
      (arrowResLEAppIso f U V e)).mpr (RingHom.locally_of hQi _ h)

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism whose restriction to an open neighbourhood of a point of the fibre over `s`
has relative dimension `m` must have relative dimension `m = g` if the residue-field fibre
over `s` has relative dimension `g`. -/
theorem relDim_eq_of_open {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens) (x : X) (hx : x ∈ V)
    {m g : ℕ} (hm : SmoothOfRelativeDimension m (V.ι ≫ f))
    (hg : SmoothOfRelativeDimension g (pullback.snd f (S.fromSpecResidueField (f x)))) :
    m = g := by
  set ι := S.fromSpecResidueField (f x)
  have hT : SmoothOfRelativeDimension m (pullback.snd (V.ι ≫ f) ι) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension m) _ _ hm
  have hW : SmoothOfRelativeDimension (0 + g)
      (pullback.snd V.ι (pullback.fst f ι) ≫ pullback.snd f ι) := inferInstance
  have hW' : SmoothOfRelativeDimension (0 + m)
      ((pullbackRightPullbackFstIso f ι V.ι).hom ≫ pullback.snd (V.ι ≫ f) ι) := inferInstance
  rw [pullbackRightPullbackFstIso_hom_snd] at hW'
  obtain ⟨z, hz⟩ : x ∈ Set.range (pullback.fst f ι) := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    rfl
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.ι)
    (g := pullback.fst f ι) ⟨x, hx⟩ z (by simp [hz])
  have : Nonempty _ := ⟨w⟩
  have := relDim_unique_of_field (K := S.residueField (f x)) _ hW' hW
  omega

/-- The relative dimension of a smooth morphism is detected on its residue-field fibres. -/
theorem smoothOfRelativeDimension_of_fibres {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (g : ℕ)
    (h : ∀ s : S, SmoothOfRelativeDimension g (pullback.snd f (S.fromSpecResidueField s))) :
    SmoothOfRelativeDimension g f := by
  rw [smoothOfRelativeDimension_iff]
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨m, hm⟩ : ∃ m, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
    algebraize [(f.appLE U V e).hom]
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth _ _›
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  suffices hmg : m = g by
    subst hmg
    exact ⟨U, hU, V, hV, hx, e, hm⟩
  have hres := smoothOfRelativeDimension_resLE f ⟨U, hU⟩ ⟨V, hV⟩ e hm
  have : SmoothOfRelativeDimension (m + 0) (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    infer_instance
  have := relDim_eq_of_open f V x hx this (h (f x))
  omega

section Assembly

open scoped CategoryTheory.MonObj CategoryTheory.Obj

/-- Clear both rational denominators and their integral torsion discrepancies, then
normalize the common nonzero integer multiplier to a positive natural number. -/
theorem exists_positive_integral_inverse
    {S : Scheme.{u}} {B B' : AbelianScheme S}
    (e : (rationalization S).obj B ≅ (rationalization S).obj B') :
    ∃ n : ℕ, 0 < n ∧ ∃ (f : B ⟶ B') (h : B' ⟶ B),
      f ≫ h = n • 𝟙 B ∧ h ≫ f = n • 𝟙 B' := by
  let d := Rationalization.integralIsoData e
  let m := d.homDenom * d.invDenom
  have hm : m ≠ 0 := mul_ne_zero d.homDenom_ne_zero d.invDenom_ne_zero
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm, d.hom, m.sign • d.inv, ?_, ?_⟩
  · rw [Preadditive.comp_zsmul, d.hom_inv, smul_smul]
    change (m.sign * m) • 𝟙 B = m.natAbs • 𝟙 B
    rw [Int.sign_mul_self_eq_natAbs]
    simp only [natCast_zsmul]
  · rw [Preadditive.zsmul_comp, d.inv_hom, smul_smul]
    change (m.sign * m) • 𝟙 B' = m.natAbs • 𝟙 B'
    rw [Int.sign_mul_self_eq_natAbs]
    simp only [natCast_zsmul]

open Langlands.GroupScheme in
/-- In the additive Hom group of an abelian scheme, `n • 𝟙` is multiplication by `n`. -/
theorem groupHom_nsmul_id {S : Scheme.{u}} (B : AbelianScheme S) (n : ℕ) :
    groupHom (n • 𝟙 B) = multiplication B.toGrp (n : ℤ) := by
  change Additive.toMul (n • Additive.ofMul (𝟙 B.toGrp)) = _
  rw [toMul_nsmul, toMul_ofMul, multiplication, zpow_natCast]

open Langlands.GroupScheme in
/-- The base change of `n • 𝟙` has underlying scheme morphism multiplication by `n` on the
base-changed abelian scheme. -/
theorem hom_baseChange_nsmul_id {S T : Scheme.{u}} (j : T ⟶ S) (B : AbelianScheme S) (n : ℕ) :
    hom ((baseChange j).map (n • 𝟙 B)) =
      (multiplication ((baseChange j).obj B).toGrp (n : ℤ)).hom.hom.left := by
  change ((Over.pullback j).mapGrp.map (groupHom (n • 𝟙 B))).hom.hom.left = _
  rw [groupHom_nsmul_id, multiplication_baseChange]
  rfl

/-- Integral maps `f`, `h` whose composites in both orders are multiplication by a positive
`n` transport a specified relative dimension, assuming that positive multiplication on
abelian varieties over fields is an isogeny. -/
theorem hasRelativeDimension_of_integral
    (hmul : GroupScheme.FieldMultiplicationIsogenyStatement.{u})
    {S : Scheme.{u}} {B B' : AbelianScheme S} (n : ℕ) (hn : 0 < n) (f : B ⟶ B') (h : B' ⟶ B)
    (hfh : f ≫ h = n • 𝟙 B) (hhf : h ≫ f = n • 𝟙 B') (g : ℕ)
    (hB : B.HasRelativeDimension g) : B'.HasRelativeDimension g := by
  apply smoothOfRelativeDimension_of_fibres B'.X.hom g
  intro s
  let j := S.fromSpecResidueField s
  let A := (baseChange j).obj B
  let A' := (baseChange j).obj B'
  have hA : SmoothOfRelativeDimension g A.X.hom := hasRelativeDimension_baseChange B g hB j
  have : ConnectedSpace A'.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := A'.X.hom)
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension A'.X.left _
    A'.X.hom inferInstance inferInstance
  have hfin : ∀ C : AbelianScheme S, IsFinite (hom ((baseChange j).map (n • 𝟙 C))) := by
    intro C
    rw [hom_baseChange_nsmul_id]
    exact (hmul (S.residueField s) ((baseChange j).obj C).toGrp inferInstance inferInstance
      inferInstance n hn).1
  have hφ : LocallyQuasiFinite (hom ((baseChange j).map f)) := by
    have : LocallyQuasiFinite (hom ((baseChange j).map f) ≫ hom ((baseChange j).map h)) := by
      rw [← hom_comp, ← Functor.map_comp, hfh]
      have := hfin B
      infer_instance
    exact LocallyQuasiFinite.of_comp _ (hom ((baseChange j).map h))
  have hψ : LocallyQuasiFinite (hom ((baseChange j).map h)) := by
    have : LocallyQuasiFinite (hom ((baseChange j).map h) ≫ hom ((baseChange j).map f)) := by
      rw [← hom_comp, ← Functor.map_comp, hhf]
      have := hfin B'
      infer_instance
    exact LocallyQuasiFinite.of_comp _ (hom ((baseChange j).map f))
  have hpt : Nonempty (Spec (S.residueField s)) := inferInstance
  obtain ⟨t⟩ := hpt
  have : Nonempty A.X.left := ⟨(A.X.hom.surjective t).choose⟩
  have : Nonempty A'.X.left := ⟨(A'.X.hom.surjective t).choose⟩
  have h1 : g ≤ d := relDim_le_of_locallyQuasiFinite (K := S.residueField s) A.X.hom A'.X.hom
    (hom ((baseChange j).map f)) (Over.w _) hA hd
  have h2 : d ≤ g := relDim_le_of_locallyQuasiFinite (K := S.residueField s) A'.X.hom A.X.hom
    (hom ((baseChange j).map h)) (Over.w _) hd hA
  obtain rfl : d = g := le_antisymm h2 h1
  exact hd

/-- The target follows from positive multiplication isogenies over fields, using
published integral denominator clearing. -/
theorem rationalIsoRelativeDimension_of
    (hmul : GroupScheme.FieldMultiplicationIsogenyStatement.{u}) :
    RationalIsoRelativeDimensionStatement.{u} := by
  intro S B B' e g
  obtain ⟨n, hn, f, h, hfh, hhf⟩ := exists_positive_integral_inverse e
  exact ⟨hasRelativeDimension_of_integral hmul n hn f h hfh hhf g,
    hasRelativeDimension_of_integral hmul n hn h f hhf hfh g⟩

end Assembly

end Langlands.AbelianScheme.RationalIsoRelativeDimension

namespace Langlands.AbelianScheme

/-- A rational isomorphism of abelian schemes preserves each specified geometric
relative dimension over an arbitrary base scheme. -/
theorem rationalIsoRelativeDimension : RationalIsoRelativeDimensionStatement.{u} :=
  RationalIsoRelativeDimension.rationalIsoRelativeDimension_of
    GroupScheme.fieldMultiplicationIsogeny

end Langlands.AbelianScheme
