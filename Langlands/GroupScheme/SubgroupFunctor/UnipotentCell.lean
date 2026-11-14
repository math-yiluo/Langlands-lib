import Langlands.GroupScheme.Rational.SplitUnipotentProductGeometric
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Topology.Connected.Clopen

/-! # Open multiplication cells with unipotent factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G U P : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left]
    [Smooth U.X.hom] [IsAffineHom U.X.hom]
    [Smooth P.X.hom] [IsAffineHom P.X.hom]
    (i : U ⟶ G) (j : P ⟶ G)

omit [ConnectedSpace G.X.left] in
/-- Multiplication of two smooth affine unipotent subgroups has closed image,
even when their product is not a subgroup. -/
theorem isClosed_range_cellMultiplication
    (hU : IsUnipotent U) (hP : IsUnipotent P) :
    IsClosed (Set.range (cellMultiplication i j).left) := by
  let e := RelativeRoot.ProductGeometry.secondFactorInversionIso U P
  have he : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hs : Function.Surjective e.hom.left := (inferInstance : Surjective e.hom.left).1
  have hc : e.hom ≫ (SubgroupProductOrbit.action i j).orbitMap 1 =
      cellMultiplication i j :=
    RelativeRoot.ProductGeometry.secondFactorInversionIso_hom_comp_orbitMap i j
  have hr : Set.range (cellMultiplication i j).left =
      Set.range ((SubgroupProductOrbit.action i j).orbitMap 1).left := by
    rw [← hc]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.hom.left y, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := hs y
      exact ⟨z, rfl⟩
  rw [hr]
  exact SubgroupProductOrbit.isClosed_range_orbitMap i j hU hP

/-- An open multiplication cell with smooth unipotent factors covers every
connected affine ambient group over an algebraically closed field. -/
theorem isIso_cellMultiplication_of_unipotent
    (hU : IsUnipotent U) (hP : IsUnipotent P)
    (hopen : IsOpenImmersion (cellMultiplication i j).left) :
    IsIso (cellMultiplication i j) := by
  have : IsOpenImmersion (cellMultiplication i j).left := hopen
  have hc : IsClopen (Set.range (cellMultiplication i j).left) :=
    ⟨isClosed_range_cellMultiplication i j hU hP,
      IsOpenImmersion.isOpen_range _⟩
  have hn : (Set.range (cellMultiplication i j).left).Nonempty := by
    let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X ⊗ P.X :=
      lift 1 1
    exact ⟨(cellMultiplication i j).left
      (a.left (IsLocalRing.closedPoint k)), ⟨_, rfl⟩⟩
  have : Surjective (cellMultiplication i j).left :=
    ⟨Set.range_eq_univ.mp (hc.eq_univ hn)⟩
  have : IsIso (cellMultiplication i j).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget _).map (cellMultiplication i j)) :=
    ‹IsIso (cellMultiplication i j).left›
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The actual scheme isomorphism supplied by an open unipotent product cell. -/
def unipotentCellIso
    (hU : IsUnipotent U) (hP : IsUnipotent P)
    (hopen : IsOpenImmersion (cellMultiplication i j).left) :
    U.X ⊗ P.X ≅ G.X := by
  have := isIso_cellMultiplication_of_unipotent i j hU hP hopen
  exact asIso (cellMultiplication i j)

@[simp] theorem unipotentCellIso_hom
    (hU : IsUnipotent U) (hP : IsUnipotent P)
    (hopen : IsOpenImmersion (cellMultiplication i j).left) :
    (unipotentCellIso i j hU hP hopen).hom = cellMultiplication i j := rfl

end Langlands.GroupScheme.SubgroupFunctor
