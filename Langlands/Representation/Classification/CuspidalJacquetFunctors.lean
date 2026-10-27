import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Category.Basic

/-! Functor structures on the actual upper and opposite Jacquet objects. -/

noncomputable section

open CategoryTheory

namespace Langlands.CuspidalJacquetMultiplicity

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Descend an ambient intertwiner to the existing normalized opposite quotient,
then restrict the Levi-subgroup action along the product Levi equivalence. -/
def oppositeMap {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)}
    {C : Rep.{uW} ℂ (GeneralLinear n F.Carrier)} (f : A.ρ.IntertwiningMap C.ρ) :
    (oppositeJacquet T B A).ρ.IntertwiningMap (oppositeJacquet T B C).ρ where
  toLinearMap := (Jacquet.normalizedMapOfModulus
    (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹ f).toLinearMap
  isIntertwining' m := (Jacquet.normalizedMapOfModulus
    (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹ f).isIntertwining'
      (B.leviEquiv F.Carrier m)

@[simp]
theorem oppositeMap_mk {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)}
    {C : Rep.{uW} ℂ (GeneralLinear n F.Carrier)} (f : A.ρ.IntertwiningMap C.ρ)
    (v : A) :
    oppositeMap T B f (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v) =
      Jacquet.mk C.ρ (B.oppositeUnipotentSubgroup F.Carrier) (f v) := rfl

/-- The actual upper normalized Jacquet quotient as a functor into algebraic
representations. Its object is exactly the published `upperJacquet`. -/
def upperFunctor :
    letI := T.generalLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      Rep.{uV} ℂ (B.Levi F.Carrier) := by
  letI := T.generalLinearTopology n
  exact {
    obj := fun A => upperJacquet T B A.obj
    map := fun f => Rep.ofHom (T.normalizedJacquetMap B (SmoothRep.hom f))
    map_id := by intros; ext v; rfl
    map_comp := by intros; ext v; rfl }

/-- The actual opposite normalized Jacquet quotient as a functor into algebraic
representations. Its object is exactly the published `oppositeJacquet`. -/
def oppositeFunctor :
    letI := T.generalLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      Rep.{uV} ℂ (B.Levi F.Carrier) := by
  letI := T.generalLinearTopology n
  exact {
    obj := fun A => oppositeJacquet T B A.obj
    map := fun f => Rep.ofHom (oppositeMap T B (SmoothRep.hom f))
    map_id := by intros; ext v; rfl
    map_comp := by intros; ext v; rfl }

@[simp]
theorem upperFunctor_obj :
    letI := T.generalLinearTopology n
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      (upperFunctor T B).obj A = upperJacquet T B A.obj := by
  intros
  rfl

@[simp]
theorem oppositeFunctor_obj :
    letI := T.generalLinearTopology n
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      (oppositeFunctor T B).obj A = oppositeJacquet T B A.obj := by
  intros
  rfl

@[simp]
theorem upperFunctor_map_mk :
    letI := T.generalLinearTopology n
    ∀ {A C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
      (f : A ⟶ C) (v : A),
      ((upperFunctor T B).map f).hom (B.jacquetMk A.representation v) =
        B.jacquetMk C.representation (SmoothRep.hom f v) := by
  intros
  rfl

@[simp]
theorem oppositeFunctor_map_mk :
    letI := T.generalLinearTopology n
    ∀ {A C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
      (f : A ⟶ C) (v : A),
      ((oppositeFunctor T B).map f).hom
        (Jacquet.mk A.representation (B.oppositeUnipotentSubgroup F.Carrier) v) =
      Jacquet.mk C.representation (B.oppositeUnipotentSubgroup F.Carrier)
        (SmoothRep.hom f v) := by
  intros
  rfl

end Langlands.CuspidalJacquetMultiplicity
