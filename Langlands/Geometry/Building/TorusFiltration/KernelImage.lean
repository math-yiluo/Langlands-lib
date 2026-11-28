import Langlands.Geometry.Building.TorusFiltration.CongruenceProof
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Kernels and images of the special-fibre maps between minimal congruent torus models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

section Comparison

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  (hT : IsTorus T.toGrp)

/-- For depths `a ≤ b`, the homomorphism from the minimal congruent model at depth `b`
to the one at depth `a` extending the identity of `T` (KP Corollary 2.10.10). The integral
points at depth `b` lie in those at depth `a` by `minimalCongruentPoints_antitone`, and the
smooth source extends the identity by `exists_hom_of_map_integralPoints_le`. -/
def minimalCongruentModelHom {a b : ℝ≥0} (hab : a ≤ b) :
    (minimalCongruentModel F T hT b).val.Hom (minimalCongruentModel F T hT a).val
      (𝟙 T.toGrp) :=
  letI : IsAffine T.X.left :=
    Langlands.GroupScheme.SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  Classical.choice <| exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F
    (minimalCongruentModel F T hT b).property.1 rfl <| by
      rintro _ ⟨x, hx, rfl⟩
      have hb := (minimalCongruentModel F T hT b).property.2.2
      have ha := (minimalCongruentModel F T hT a).property.2.2
      rw [hb] at hx
      rw [ha]
      simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
        minimalCongruentPoints_antitone F T hT hab hx

/-- For depths `a ≤ b`, the special-fibre map `𝒯̄_b ⟶ 𝒯̄_a` over the residue field of
`fixedFieldIntegers F` induced by `minimalCongruentModelHom`. -/
abbrev minimalCongruentFibreMap {a b : ℝ≥0} (hab : a ≤ b) :
    (minimalCongruentModel F T hT b).val.specialFibre ⟶
      (minimalCongruentModel F T hT a).val.specialFibre :=
  (minimalCongruentModelHom F T hT hab).specialFibreMap

end Comparison

/-- KP Proposition B.10.15 over `K = inertiaFixedField F`. For depths `0 ≤ r < s`, put
`t = max s (r + 1)`, let `f : 𝒯̄_s ⟶ 𝒯̄_r` and `g : 𝒯̄_t ⟶ 𝒯̄_s` be the special-fibre maps of
the minimal congruent models, and let `J = kernel f` be the full scheme-theoretic kernel.
Then `J` is smooth, connected and unipotent, and it is the scheme-theoretic image of `g`:
`kernelι f` is a closed subgroup and `g` factors through it by an fppf quotient map whose
kernel is that of `g`. -/
def MinimalCongruentKernelImageStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    (hT : IsTorus T.toGrp) (r s : ℝ≥0) (hrs : r < s),
    let f := minimalCongruentFibreMap F T hT hrs.le
    let g := minimalCongruentFibreMap F T hT (le_max_left s (r + 1))
    Smooth (kernel f).X.hom ∧ ConnectedSpace (kernel f).X.left ∧ IsUnipotent (kernel f) ∧
      IsClosedSubgroup (kernelι f) ∧
      ∃ q : (minimalCongruentModel F T hT (max s (r + 1))).val.specialFibre ⟶ kernel f,
        q ≫ kernelι f = g ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι g)) q

end Langlands.Geometry.Building
