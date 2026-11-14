import Langlands.Geometry.FormalGroup.BasicAtlas

/-! # Transport between equal coefficient algebra structures -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] {α : Algebra O R}
variable {σ : Type} [Finite σ]

/-- Change only the proof of the scalar tangent condition along equal algebra structures. -/
def reAlgebra (M : @ModuleLaw O _ R _ α σ _) (β : Algebra O R) (e : α = β) :
    @ModuleLaw O _ R _ β σ _ where
  groupLaw := letI := α; M.groupLaw
  action := letI := α; M.action
  linear_natural a i j := by
    cases e
    exact M.linear_natural a i j

/-- Algebra transport leaves the actual commutative formal group law unchanged. -/
@[simp]
theorem reAlgebra_groupLaw (M : @ModuleLaw O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) :
    (letI := β; (M.reAlgebra β e).groupLaw) = (letI := α; M.groupLaw) := rfl

/-- Algebra transport leaves every actual scalar action unchanged. -/
@[simp]
theorem reAlgebra_action (M : @ModuleLaw O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) (a : O) :
    (letI := β; (M.reAlgebra β e).action a) = (letI := α; M.action a) := rfl

/-- Transport along reflexivity returns the original formal module. -/
@[simp]
theorem reAlgebra_refl (M : @ModuleLaw O _ R _ α σ _) :
    M.reAlgebra α rfl = M := rfl

/-- Successive transports agree with transport along the composed equality. -/
theorem reAlgebra_trans (M : @ModuleLaw O _ R _ α σ _)
    (β γ : Algebra O R) (e : α = β) (d : β = γ) :
    (M.reAlgebra β e).reAlgebra γ d = M.reAlgebra γ (e.trans d) := by
  cases e
  cases d
  rfl

namespace BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Equality of the base algebra structures induces equality on every localization. -/
theorem localizationAlgebra_eq (β : Algebra O R) (e : α = β) (a : R) :
    (letI := α; inferInstance : Algebra O (Localization.Away a)) =
      (letI := β; inferInstance : Algebra O (Localization.Away a)) := by
  cases e
  rfl

/-- Retype an atlas along equal algebra structures, retaining all actual coordinate data. -/
def reAlgebra (X : @BasicAtlas O _ R _ α σ _) (β : Algebra O R) (e : α = β) :
    @BasicAtlas O _ R _ β σ _ where
  opens := letI := α; X.opens
  covers := letI := α; X.covers
  chart a := letI := α; (X.chart a).reAlgebra _ (localizationAlgebra_eq β e a.val)
  transition A a b ha hb := by
    cases e
    exact X.transition A a b ha hb
  transition_self A a ha := by
    cases e
    apply ModuleLaw.Iso.ext_hom
    apply ModuleLaw.Hom.ext
    exact congrArg (fun f => f.hom.toHom) (X.transition_self A a ha)
  transition_cocycle A a b c ha hb hc := by
    cases e
    apply ModuleLaw.Iso.ext_hom
    apply ModuleLaw.Hom.ext
    exact congrArg (fun f => f.hom.toHom) (X.transition_cocycle A a b c ha hb hc)
  transition_natural φ a b ha hb ha' hb' := by
    cases e
    exact X.transition_natural φ a b ha hb ha' hb'

/-- The same principal generators are used after algebra transport. -/
@[simp]
theorem reAlgebra_opens (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) :
    (letI := β; (X.reAlgebra β e).opens) = (letI := α; X.opens) := rfl

/-- Each transported chart has exactly its original commutative formal group law. -/
@[simp]
theorem reAlgebra_chart_groupLaw (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) (a : (letI := α; X.opens)) :
    (letI := β; ((X.reAlgebra β e).chart a).groupLaw) =
      (letI := α; (X.chart a).groupLaw) := rfl

/-- Each transported chart has exactly its original formal scalar actions. -/
@[simp]
theorem reAlgebra_chart_action (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) (a : (letI := α; X.opens)) (c : O) :
    (letI := β; ((X.reAlgebra β e).chart a).action c) =
      (letI := α; (X.chart a).action c) := rfl

/-- Transport retains the forward formal transition series on every test algebra. -/
@[simp]
theorem reAlgebra_transition_coordinates (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (a b : (letI := α; X.opens))
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val)) :
    (letI := β; ((X.reAlgebra β e).transition A a b ha hb).hom.toHom.toCoordinateMap) =
      (letI := α; (X.transition A a b ha hb).hom.toHom.toCoordinateMap) := by
  cases e
  rfl

/-- Transport also retains the inverse formal transition series. -/
@[simp]
theorem reAlgebra_transition_inv_coordinates (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (a b : (letI := α; X.opens))
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val)) :
    (letI := β; ((X.reAlgebra β e).transition A a b ha hb).inv.toHom.toCoordinateMap) =
      (letI := α; (X.transition A a b ha hb).inv.toHom.toCoordinateMap) := by
  cases e
  rfl

/-- Reflexive transport returns the original actual atlas. -/
@[simp]
theorem reAlgebra_refl (X : @BasicAtlas O _ R _ α σ _) :
    X.reAlgebra α rfl = X := rfl

/-- Actual atlas transport is coherent under composition of algebra equalities. -/
theorem reAlgebra_trans (X : @BasicAtlas O _ R _ α σ _)
    (β γ : Algebra O R) (e : α = β) (d : β = γ) :
    (X.reAlgebra β e).reAlgebra γ d = X.reAlgebra γ (e.trans d) := by
  cases e
  cases d
  rfl

end BasicAtlas
end Langlands.FormalGroup.ModuleLaw
