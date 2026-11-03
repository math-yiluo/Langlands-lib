import Langlands.GroupScheme.Rational.ActionCharacterWeights
import Langlands.GroupScheme.Rational.KernelCentralizerStructureProof
import Langlands.GroupScheme.Rational.QuotientActionComparisonProof
import Langlands.GroupScheme.Dynamic.LieProof

/-! # The exact cyclic Lie image of the intrinsic relative root functor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Under a monomorphic homomorphism, taking the all-test image commutes
with taking the intrinsic tangent submodule. -/
theorem tangentSubmodule_map (j : H ⟶ G) [Mono j.hom.hom]
    (F : SubgroupFunctor H) :
    tangentSubmodule (F.map j) =
      (tangentSubmodule F).map (Lie.targetMapLinear j k) := by
  ext X
  constructor
  · intro hX
    obtain ⟨Y, hY, hYX⟩ :=
      (mem_map_lieKernel_iff j inferInstance F X.toMul).mp hX
    exact ⟨Additive.ofMul Y, hY, Additive.toMul.injective hYX⟩
  · rintro ⟨Y, hY, rfl⟩
    exact ⟨Y.toMul.val, hY, rfl⟩

section Root

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (a : characterLattice S)

omit [IsAffineHom H.X.hom] in
/-- For every smooth affine group and nonzero split-torus character, the
intrinsic root functor has exactly the first cyclic weight span as tangent image. -/
theorem tangentSubmodule_subgroup [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) :
    tangentSubmodule (subgroup i a) =
      semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) := by
  obtain ⟨C, j, hj, hclosed, hC, hLie⟩ :=
    kernelCentralizerStructure k G inferInstance inferInstance S hS i a ha
  let : Smooth C.X.hom := hC
  let : IsClosedImmersion j.hom.hom.left := hclosed
  let : Mono j.hom.hom := hj.1
  let : IsAffineHom C.X.hom := by
    have h : IsAffineHom (j.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k S hS a ha
  let := hqc
  let := hflat
  let := hsurj
  have hequiv : (centralizerAction i a j hj).IsEquivariant
      (AutomorphicAction.conjugation i) j :=
    centralizerAction_act_comp i a j hj
  have hrange : LinearMap.range (Lie.targetMapLinear j k) =
      integralWeightSpan i a := by
    rw [← tangentSubmodule_range j, hj.2]
    exact (hasLieImage_iff_tangentSubmodule_eq _ _).mp hLie
  have hcyclic : semigroupWeightSpan (AutomorphicAction.conjugation i)
      (cyclicTail a 1) ≤ LinearMap.range (Lie.targetMapLinear j k) := by
    rw [hrange]
    refine iSup_le fun χ => ?_
    obtain ⟨n, _, _, hn⟩ := χ.property
    rw [← hn, actionWeightSpace_conjugation]
    exact le_iSup_of_le (n : ℤ) (by rw [natCast_zsmul])
  have hmap :
      (semigroupWeightSpan (centralizerAction i a j hj) (cyclicTail a 1)).map
          (Lie.targetMapLinear j k) =
        semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) := by
    rw [semigroupWeightSpan, Submodule.map_iSup]
    apply iSup_congr
    intro χ
    rw [hequiv.map_actionWeightSpace_eq_inf_range]
    exact inf_eq_left.mpr ((le_iSup _ χ).trans hcyclic)
  rw [quotientActionComparison _ _ _ _ i a j hj hclosed,
    tangentSubmodule_map, AutomorphicAction.tangentSubmodule_unipotent _ dynamicLie,
    ← semigroupWeightSpan_restrict_character_cyclicTail
      (quotientAction i a j hj) hS a ha,
    quotientAction_restrict]
  exact hmap

omit [IsAffineHom H.X.hom] in
/-- The exact cyclic Lie image of the all-test relative root functor, with no
connectedness or root-occurrence assumption. -/
theorem hasLieImage_subgroup [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) :
    HasLieImage (subgroup i a)
      (semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1)) :=
  (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
    (tangentSubmodule_subgroup i a hS ha)

omit [IsAffineHom H.X.hom] in
/-- The canonical unchanged-vector identification of the intrinsic root tangent
with its positive cyclic weight span. -/
def subgroupTangentEquiv [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) :
    tangentSubmodule (subgroup i a) ≃ₗ[k]
      semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) :=
  LinearEquiv.ofEq _ _ (tangentSubmodule_subgroup i a hS ha)

omit [IsAffineHom H.X.hom] in
@[simp] theorem subgroupTangentEquiv_apply_coe [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (X : tangentSubmodule (subgroup i a)) :
    (subgroupTangentEquiv i a hS ha X : Additive (lieKernel G k)) = X := rfl

end Root

end Langlands.GroupScheme.RelativeRoot
