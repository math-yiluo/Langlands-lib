import Langlands.GroupScheme.NormalQuotientExistenceReduction
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.AffineHomImageProof

/-! # Existence of unrestricted affine normal quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every normal closed subgroup of an affine algebraic group over an arbitrary
field is the full kernel of an fppf projection onto an affine algebraic group. -/
theorem normalSubgroupQuotientExistence :
    NormalSubgroupQuotientExistenceStatement.{u} :=
  normalQuotientExistence_with_structural_inputs affineCartierSmooth affineHomImage

/-- An actual quotient group and projection, with affineness, local finite type
and the prescribed full kernel retained in the chosen data. -/
def normalSubgroupQuotientData
    {k : Type u} [Field k]
    {G N : GroupScheme (Spec (CommRingCat.of k))} (i : N ⟶ G)
    (ha : IsAffineHom G.X.hom) (hl : LocallyOfFiniteType G.X.hom)
    (hi : IsClosedSubgroup i) (hn : (SubgroupFunctor.range i).IsNormal) :
    Σ (Q : GroupScheme (Spec (CommRingCat.of k))), {q : G ⟶ Q //
      IsAffineHom Q.X.hom ∧ LocallyOfFiniteType Q.X.hom ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q} := by
  let h := normalSubgroupQuotientExistence k G N i ha hl hi hn
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

end Langlands.GroupScheme
