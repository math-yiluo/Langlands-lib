import Langlands.GroupScheme.Rational.RelativeTitsSystemStatement
import Langlands.GroupScheme.Rational.TitsStandardParabolic
import Langlands.GroupScheme.Rational.AnisotropicRootSystem

/-! # The actual relative Tits system with full torus centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)

/-- If every rational point centralizes the torus, the actual Weyl quotient is trivial. -/
theorem subsingleton_relativeWeylGroup_of_centralizerPoints_eq_top
    (hZ : centralizerPoints i = ⊤) : Subsingleton (relativeWeylGroup i) := by
  change Subsingleton
    (normalizerPoints i ⧸ (centralizerPoints i).subgroupOf (normalizerPoints i))
  rw [hZ, Subgroup.top_subgroupOf]
  exact QuotientGroup.subsingleton_quotient_top

/-- The explicit identification of the actual Weyl quotient with the trivial group
when every rational point centralizes the torus. -/
def relativeWeylEquivPUnitOfCentralizerEqTop (hZ : centralizerPoints i = ⊤) :
    relativeWeylGroup i ≃* PUnit.{u + 1} := by
  let := subsingleton_relativeWeylGroup_of_centralizerPoints_eq_top i hZ
  exact MulEquiv.ofBijective (1 : relativeWeylGroup i →* PUnit.{u + 1})
    (Function.bijective_of_subsingleton' _)

variable [IsAffineHom G.X.hom] (ν : cocharacterLattice T)

/-- An empty actual root set has no simple relative roots. -/
theorem simpleRelativeRoots_eq_empty_of_relativeRoots_eq_empty
    (hroots : relativeRoots i = ∅) : simpleRelativeRoots i ν = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro α hα
  have hαr := hα.1.1
  rw [hroots] at hαr
  exact hαr

variable [Mono i.hom.hom.left]

/-- The actual relative Tits-system predicate holds with empty roots and a full
torus centralizer. No structural theorem or genericity premise is needed. -/
theorem hasRelativeTitsSystem_of_centralizerPoints_eq_top
    (hZ : centralizerPoints i = ⊤) (hroots : relativeRoots i = ∅) :
    HasRelativeTitsSystem i ν := by
  let := subsingleton_relativeWeylGroup_of_centralizerPoints_eq_top i hZ
  have hB : standardParabolicPoints i ν ∅ = ⊤ := by
    apply top_unique
    intro g _
    apply centralizerPoints_le_standardParabolicPoints i ν ∅
    rw [hZ]
    exact Subgroup.mem_top g
  have hsimple := simpleRelativeRoots_eq_empty_of_relativeRoots_eq_empty i ν hroots
  have hS : simpleRelativeReflections i ν = ∅ :=
    simpleRelativeReflections_eq_empty hsimple
  refine ⟨?_, ?_, ?_⟩
  · refine
      { surjective := QuotientGroup.mk'_surjective _
        ker_eq := ?_
        sup_eq := by rw [hB, top_sup_eq]
        closure_eq := ?_
        ne_one := ?_
        mul_self := ?_
        mul_mem_cell := ?_
        conj_not_le := ?_ }
    · rw [QuotientGroup.ker_mk', hZ, hB]
    · apply top_unique
      intro w _
      have hw : w = 1 := Subsingleton.elim _ _
      rw [hw]
      exact Subgroup.one_mem _
    all_goals
      intro s hs
      rw [hS] at hs
      exact False.elim hs
  · intro α hα
    rw [hsimple] at hα
    exact False.elim hα
  · intro α hα
    rw [hsimple] at hα
    exact False.elim hα

omit [Mono i.hom.hom.left] in
/-- An anisotropic affine group has the actual trivial relative Tits system for
each split subtorus and every cocharacter. -/
theorem IsAnisotropic.hasRelativeTitsSystem (hG : IsAnisotropic G)
    (hi : IsSplitSubtorus i) :
    haveI := hi.mono
    HasRelativeTitsSystem i ν := by
  have := hi.mono
  exact hasRelativeTitsSystem_of_centralizerPoints_eq_top i ν
    (hG.centralizerPoints_eq_top hi) (hG.relativeRoots_eq_empty hi)

end Langlands.GroupScheme
