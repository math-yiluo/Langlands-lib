import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Torus.Diagonalizable

/-! # A diagonalizable presentation of the same opposite-parabolic intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A finite free diagonalizable presentation of the supplied group scheme. -/
structure SplitTorusDiagonalizableModel (R : CommRingCat.{u})
    (T : GroupScheme (Spec R)) where
  index : Type u
  finite : Finite index
  iso : (Diagonalizable.groupScheme R (index → ℤ)).toGrp ≅ T

namespace IsSplitTorus

/-- Choose a diagonalizable model of the original split torus over the original base. -/
def diagonalizableModel {R : CommRingCat.{u}} {T : GroupScheme (Spec R)}
    (hT : IsSplitTorus T) : SplitTorusDiagonalizableModel R T := by
  classical
  apply Classical.choice
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  exact ⟨⟨I, hI, Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ e.symm⟩⟩

end IsSplitTorus

namespace SplitTorusDiagonalizableModel

variable {R : CommRingCat.{u}} {T G : GroupScheme (Spec R)}
    (model : SplitTorusDiagonalizableModel R T)

/-- Present the supplied subgroup map by the actual diagonalizable model. -/
def embedding (j : T ⟶ G) :
    (Diagonalizable.groupScheme R (model.index → ℤ)).toGrp ⟶ G :=
  model.iso.hom ≫ j

/-- Transport an arbitrary test point of the same torus to its diagonalizable model. -/
def pointLift {V : Over (Spec R)} (t : V ⟶ T.X) :
    V ⟶ (Diagonalizable.groupScheme R (model.index → ℤ)).toGrp.X :=
  t ≫ model.iso.inv.hom.hom

/-- The transported point has the identical image in the ambient group. -/
theorem pointLift_comp (j : T ⟶ G) {V : Over (Spec R)} (t : V ⟶ T.X) :
    model.pointLift t ≫ (model.embedding j).hom.hom = t ≫ j.hom.hom := by
  change (t ≫ model.iso.inv.hom.hom) ≫ (model.iso.hom.hom.hom ≫ j.hom.hom) = _
  have h :
      model.iso.inv.hom.hom ≫ model.iso.hom.hom.hom = 𝟙 T.X :=
    congrArg (fun f => f.hom.hom) model.iso.inv_hom_id
  rw [Category.assoc, ← Category.assoc model.iso.inv.hom.hom, h, Category.id_comp]

/-- The model has exactly the same subgroup functor, on every relative test scheme. -/
theorem range_embedding (j : T ⟶ G) :
    SubgroupFunctor.range (model.embedding j) = SubgroupFunctor.range j := by
  ext V g
  constructor
  · intro hg
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    apply SubgroupFunctor.mem_range.mpr
    exact ⟨t ≫ model.iso.hom.hom.hom, Category.assoc _ _ _⟩
  · intro hg
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    apply SubgroupFunctor.mem_range.mpr
    exact ⟨model.pointLift t, model.pointLift_comp j t⟩

variable [IsAffine G.X.left]
    {P Q : GroupScheme (Spec R)} {iP : P ⟶ G} {iQ : Q ⟶ G}
    (coch : (Gm (Spec R)).toGrp ⟶ G) (j : T ⟶ G)
    (hP : (Dynamic.parabolic coch).IsRepresentedBy iP)
    (hQ : (Dynamic.parabolic (Dynamic.oppositeCocharacter coch)).IsRepresentedBy iQ)
    (hT : (Dynamic.centralizer coch).IsRepresentedBy j)

include hP hQ hT

/-- Opposite-parabolic equality factors through this presentation of the same torus. -/
theorem exists_point_of_opposite_parabolic_eq
    {V : Over (Spec R)} (a : V ⟶ P.X) (b : V ⟶ Q.X)
    (he : a ≫ iP.hom.hom = b ≫ iQ.hom.hom) :
    ∃ t : V ⟶ (Diagonalizable.groupScheme R (model.index → ℤ)).toGrp.X,
      a ≫ iP.hom.hom = t ≫ (model.embedding j).hom.hom := by
  obtain ⟨t, ht⟩ := Dynamic.exists_centralizer_point_of_opposite_parabolic_eq
    coch hP hQ hT a b he
  exact ⟨model.pointLift t, ht.trans (model.pointLift_comp j t).symm⟩

end SplitTorusDiagonalizableModel

end Langlands.GroupScheme
