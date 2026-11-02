import Langlands.GroupScheme.Lie.FiniteDimensional
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Finiteness of actual relative roots from the Lie weight decomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : T.toGrp ⟶ G)

/-- A split-torus action on the actual Lie kernel has finitely many nonzero
character weight spaces. -/
theorem IsSplitTorus.finite_weightSupport (hT : IsSplitTorus T.toGrp) :
    Set.Finite {χ : characterLattice T | weightSpace i χ ≠ ⊥} := by
  classical
  have := Lie.finiteDimensional_lieKernel G
  exact Submodule.finite_ne_bot_of_iSupIndep
    (R := k) (M := Additive (lieKernel G k))
    (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSupIndep

/-- The actual relative roots are finite without a root-system premise. -/
theorem IsSplitTorus.finite_relativeRoots (hT : IsSplitTorus T.toGrp) :
    (relativeRoots i).Finite :=
  (hT.finite_weightSupport i).subset (fun _ hχ => hχ.2)

/-- Positive relative roots form a finite set for any cocharacter. -/
theorem IsSplitTorus.finite_positiveRelativeRoots (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) : (positiveRelativeRoots i ν).Finite :=
  (hT.finite_relativeRoots i).subset (positiveRelativeRoots_subset_relativeRoots i ν)

/-- The actual simple relative roots are finite for any cocharacter. -/
theorem IsSplitTorus.finite_simpleRelativeRoots (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) : (simpleRelativeRoots i ν).Finite :=
  (hT.finite_positiveRelativeRoots i ν).subset (simpleRelativeRoots_subset_positive i ν)

/-- A finite enumeration of the actual relative roots, using only splitness
and the affine locally finite type hypotheses. -/
@[instance_reducible]
def relativeRootFintypeOfIsSplitTorus (hT : IsSplitTorus T.toGrp) :
    Fintype (relativeRoots i) :=
  (hT.finite_relativeRoots i).fintype

/-- A finite enumeration of the actual simple roots, with no root-system
premise. -/
@[instance_reducible]
def simpleRelativeRootFintypeOfIsSplitTorus (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) : Fintype (simpleRelativeRoots i ν) :=
  (hT.finite_simpleRelativeRoots i ν).fintype

end Langlands.GroupScheme
