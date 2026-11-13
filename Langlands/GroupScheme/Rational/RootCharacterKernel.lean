import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Dynamic.ActionConjugation
import Langlands.GroupScheme.Dynamic.ActionUniqueness
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Character-kernel factorization of intrinsic root subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0)

include hS ha

/-- A nonzero character of a split torus admits a strictly positive cocharacter pairing. -/
theorem exists_positive_pairing :
    ∃ ν : cocharacterLattice S, 0 < latticePairing S a ν := by
  obtain ⟨ν, hν⟩ := hS.exists_pairings_ne_zero ({a} : Set (characterLattice S))
    (Set.finite_singleton a) (by
      intro b hb
      have hb' : b = a := Set.mem_singleton_iff.mp hb
      simpa only [hb'] using ha)
  have hne := hν a (Set.mem_singleton a)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact ⟨-ν, by simpa only [map_neg] using neg_pos.mpr hneg⟩
  · exact ⟨ν, hpos⟩

/-- Every map to a separated commutative group kills the actual intrinsic
root subgroup, on every scheme test. -/
theorem comp_eq_one_of_mem_subgroup
    {H : CommGroupScheme (Spec (CommRingCat.of k))} [IsSeparated H.X.hom]
    (f : G ⟶ H.toGrp) {T : Over (Spec (CommRingCat.of k))} {g : T ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier T) : g ≫ f.hom.hom = 1 := by
  obtain ⟨ν, hν⟩ := exists_positive_pairing hS a ha
  let χ := CommGroupScheme.groupHom ν ≫ i
  have hgU : g ∈ (AutomorphicAction.cocharacterAction χ).unipotent.carrier T := by
    rw [AutomorphicAction.cocharacterAction_unipotent]
    exact subgroup_le_dynamicUnipotent i ν hν T hg
  apply (AutomorphicAction.cocharacterAction χ).comp_eq_one_of_mem_unipotent_of_invariant
    f ?_ hgU
  intro V t x
  rw [AutomorphicAction.cocharacterAction_act, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp]
  simp [mul_comm, mul_assoc]

/-- In particular every rational character is one on all intrinsic root points. -/
theorem characterEval_eq_one_of_mem_subgroup (ψ : rationalCharacters G)
    {T : Over (Spec (CommRingCat.of k))} {g : T ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier T) : characterEval ψ T g = 1 := by
  let : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom := isSplitTorus_gm.isAffineHom
  rw [characterEval_apply, comp_eq_one_of_mem_subgroup hS i a ha ψ.toMul hg, map_one]

variable {U : GroupScheme (Spec (CommRingCat.of k))}
    (j : U ⟶ G) (hj : (subgroup i a).IsRepresentedBy j)
    (ψ : rationalCharacters G)

include hj

/-- The actual represented root group lies in the scheme-theoretic kernel of
any rational character. -/
theorem range_le_characterKernel :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range (kernelι ψ.toMul) := by
  intro T g hg
  have hroot : g ∈ (subgroup i a).carrier T := by rwa [← hj.2]
  let : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom := isSplitTorus_gm.isAffineHom
  have hg0 := comp_eq_one_of_mem_subgroup hS i a ha ψ.toMul hroot
  let z : T ⟶ (kernel ψ.toMul).X :=
    (kernelPointsEquiv ψ.toMul T).symm ⟨g, hg0⟩
  refine ⟨z, ?_⟩
  exact congrArg Subtype.val ((kernelPointsEquiv ψ.toMul T).apply_symm_apply ⟨g, hg0⟩)

/-- The canonical actual morphism from a root representative into the kernel
of a rational character, preserving its ambient inclusion. -/
def characterKernelFactor : U ⟶ kernel ψ.toMul :=
  (show (SubgroupFunctor.range (kernelι ψ.toMul)).IsRepresentedBy
      (kernelι ψ.toMul) from ⟨inferInstance, rfl⟩).factorHom j
    (range_le_characterKernel hS i a ha j hj ψ)

/-- Composing the factor with the kernel inclusion recovers the original root inclusion. -/
theorem characterKernelFactor_comp :
    characterKernelFactor hS i a ha j hj ψ ≫ kernelι ψ.toMul = j :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp
    (show (SubgroupFunctor.range (kernelι ψ.toMul)).IsRepresentedBy
      (kernelι ψ.toMul) from ⟨inferInstance, rfl⟩) j
    (range_le_characterKernel hS i a ha j hj ψ)

end Langlands.GroupScheme.RelativeRoot
