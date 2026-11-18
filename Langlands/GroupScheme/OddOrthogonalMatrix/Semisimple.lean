import Langlands.GroupScheme.OddOrthogonalMatrix.Reductive
import Langlands.GroupScheme.OddOrthogonalMatrix.Roots
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitSemisimplicity

/-! # Semisimplicity and full integral root span of the odd identity component -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {K : Type u} [Field K]

local notation "𝔗" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)

/-- The actual roots span the entire integral character lattice: the short
roots already contain a coordinate basis. -/
theorem span_roots_eq_top :
    Submodule.span ℤ (roots (diagonalTorus l K)) = ⊤ := by
  let φ := GeneralLinear.characterCoordEquiv l K
  rw [eq_top_iff, ← ((Pi.basisFun ℤ l).map φ.symm).span_eq, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  apply Submodule.subset_span
  apply (mem_roots_iff _).mpr
  refine Or.inl ⟨Sum.inl a, ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply, SymplecticMatrix.weightCoord_inl]
  exact φ.apply_symm_apply _

/-- Any actual root datum of the identity torus has full integral root span. -/
theorem rootSpan_eq_top {J : Type*}
    (P : RootDatum J (characterLattice 𝔗) (cocharacterLattice 𝔗))
    (hP : Set.range P.root = roots (identityTorus l K)) : P.rootSpan ℤ = ⊤ := by
  change Submodule.span ℤ (Set.range P.root) = ⊤
  rw [hP, roots_identityTorus]
  exact span_roots_eq_top

variable (l K)

set_option linter.defProp false in
/-- The actual odd norm-one identity component is semisimple over every
field, with at least two hyperbolic indices. -/
def identitySemisimple [Nontrivial l] : IsSemisimple (identityComponent (groupScheme l K)) := by
  let hRed := identityReductive l K
  let hT := (isSplitSubtorus_diagonalTorus l K).1
  obtain ⟨J, _, P, hP, -⟩ := rootDatumExistence K _ hRed 𝔗 hT (identityTorus l K)
    (isMaximalTorus_identityTorus l K)
  refine ((splitSemisimpleRootDatum K _ hRed 𝔗 hT (identityTorus l K)
    (isMaximalTorus_identityTorus l K) J P hP).1).2 ?_
  rw [rootSpan_eq_top P hP.2.1]
  infer_instance

end Langlands.GroupScheme.OddOrthogonalMatrix
