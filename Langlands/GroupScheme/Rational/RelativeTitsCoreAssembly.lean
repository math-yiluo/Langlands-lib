import Langlands.GroupScheme.Rational.SimpleRootParabolicFactorization
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial

/-! # The relative Tits system from seven structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Nonidentity rational points of the simple-root subgroups of a smooth affine group with a
split torus, chosen by `RelativeRoot.exists_rootPoint_actual`. No structural statement is
used. -/
def RelativeSimpleRootPointData.ofActual [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    RelativeSimpleRootPointData i ν where
  point a := Classical.choose (RelativeRoot.exists_rootPoint_actual hT i a.property.1.1)
  mem a := (Classical.choose_spec (RelativeRoot.exists_rootPoint_actual hT i a.property.1.1)).1
  ne_one a :=
    (Classical.choose_spec (RelativeRoot.exists_rootPoint_actual hT i a.property.1.1)).2

/-- **The relative Tits system from seven published structural statements.** The
nondegeneracy field `conj_not_le` comes from `RelativeSimpleRootPointData.ofActual`, so the
root-subgroup realization and vector statements are not needed. -/
theorem relativeTitsSystemStatement_of_coreStatements
    (hcox : RelativeWeylCoxeterStatement.{u}) (hE : StandardParabolicEndpointsStatement.{u})
    (hBr : RationalBruhatStatement.{u}) (hrank : RootRankOneFactorizationStatement.{u})
    (hroot : RelativeRootSystemStatement.{u}) (hZ : GenericCentralizerStatement.{u})
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u}) :
    RelativeTitsSystemStatement.{u} :=
  relativeTitsSystemStatement_of_rootProduct hcox hE hBr hrank hroot hZ hprod
    fun _ _ _ hG _ i hi ν _ =>
      haveI := hG.isAffineHom
      haveI := hG.smooth
      haveI := hi.isSplitSubtorus.mono
      (RelativeSimpleRootPointData.ofActual hi.isSplitSubtorus.1 i ν).conj_not_le i ν
        hi.isSplitSubtorus.1

end Langlands.GroupScheme
