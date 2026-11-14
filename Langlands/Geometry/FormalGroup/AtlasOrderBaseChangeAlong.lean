import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeMorphism

/-! # Supplied scalar coefficient extension with the full acting order -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section AlgebraTransport

variable {α : Algebra O R}
variable {X : @BasicAtlas O _ R _ α σ _}
variable {Y : @BasicAtlas O _ R _ α τ _}
variable {Z : @BasicAtlas O _ R _ α υ _}
variable {E : (letI := α; OrderAction D X)}
variable {E' : (letI := α; OrderAction D Y)}
variable {E'' : (letI := α; OrderAction D Z)}
variable {h : (letI := α; X.opens = Y.opens)}
variable {k : (letI := α; Y.opens = Z.opens)}

/-- Retype the actual order action along equality of the scalar algebra structures. -/
def reAlgebra (E : (letI := α; OrderAction D X)) (β : Algebra O R) (e : α = β) :
    (letI := β; OrderAction D (X.reAlgebra β e)) := by
  cases e
  exact E

/-- Every formal order-action series is retained after scalar algebra transport. -/
@[simp]
theorem reAlgebra_chart_coordinates (E : (letI := α; OrderAction D X))
    (β : Algebra O R) (e : α = β) (a : (letI := α; X.opens)) (d : D) :
    (letI := β; (((E.reAlgebra β e).chart a).action d).toHom.toCoordinateMap) =
      (letI := α; ((E.chart a).action d).toHom.toCoordinateMap) := by
  cases e
  rfl

/-- Every order-action series on a coefficient test is retained by scalar transport. -/
@[simp]
theorem reAlgebra_testChart_coordinates (E : (letI := α; OrderAction D X))
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (a : (letI := α; X.opens)) (ha : IsUnit (algebraMap R A a.val)) (d : D) :
    (letI := β; ((((E.reAlgebra β e).chart a).map
      (coefficientLift (O := O) a.val A ha)).action d).toHom.toCoordinateMap) =
      (letI := α; (((E.chart a).map
        (coefficientLift (O := O) a.val A ha)).action d).toHom.toCoordinateMap) := by
  cases e
  rfl

/-- Reflexive transport returns the original full order action. -/
@[simp]
theorem reAlgebra_refl (E : (letI := α; OrderAction D X)) :
    E.reAlgebra α rfl = E := rfl

/-- Scalar algebra transport identifies the entire order-module compatible families. -/
def reAlgebraPointEquiv (E : (letI := α; OrderAction D X))
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R) :
    (letI := α; E.Point A) ≃ₗ[D] (letI := β; (E.reAlgebra β e).Point A) := by
  cases e
  exact LinearEquiv.refl D _

/-- Forgetting the order gives exactly the existing full-family transport. -/
theorem reAlgebraPointEquiv_eq (E : (letI := α; OrderAction D X))
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (x : (letI := α; E.Point A)) :
    E.reAlgebraPointEquiv β e A x = X.reAlgebraPointEquiv β e A x := by
  cases e
  rfl

/-- Every tuple at every further test is retained by order-linear scalar transport. -/
@[simp]
theorem reAlgebraPointEquiv_apply (E : (letI := α; OrderAction D X))
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (x : (letI := α; E.Point A)) (B : CommAlgCat.{v} R) (φ : A ⟶ B)
    (a : (letI := α; X.opens)) (ha : IsUnit (algebraMap R B a.val)) :
    (letI := β; (E.reAlgebraPointEquiv β e A x).val ⟨B, φ, a, ha⟩) =
      (letI := α; x.val ⟨B, φ, a, ha⟩) := by
  cases e
  rfl

/-- Order-linear scalar transport commutes with every coefficient map. -/
theorem reAlgebraPointEquiv_natural (E : (letI := α; OrderAction D X))
    (β : Algebra O R) (e : α = β) {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : (letI := α; E.Point A)) :
    (letI := β; (E.reAlgebra β e).mapPoints φ (E.reAlgebraPointEquiv β e A x)) =
      E.reAlgebraPointEquiv β e B (letI := α; E.mapPoints φ x) := by
  cases e
  rfl

namespace Hom

/-- Retype an actual formal map with commutation for every element of the order. -/
def reAlgebra (g : (letI := α; Hom E E' h)) (β : Algebra O R) (e : α = β) :
    (letI := β; Hom (E.reAlgebra β e) (E'.reAlgebra β e) h) := by
  cases e
  exact g

/-- The transported order-linear map retains exactly its transported basic formal map. -/
@[simp]
theorem reAlgebra_val (g : (letI := α; Hom E E' h))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (g.reAlgebra β e).val) = (letI := α; g.val.reAlgebra β e) := by
  cases e
  rfl

/-- Scalar transport preserves the identity full-order formal map. -/
@[simp]
theorem reAlgebra_id (E : (letI := α; OrderAction D X))
    (β : Algebra O R) (e : α = β) :
    (letI := α; (Hom.id E).reAlgebra β e) =
      (letI := β; Hom.id (E.reAlgebra β e)) := by
  cases e
  rfl

/-- Scalar transport preserves composition of full-order formal maps. -/
@[simp]
theorem reAlgebra_comp (q : (letI := α; Hom E' E'' k))
    (g : (letI := α; Hom E E' h)) (β : Algebra O R) (e : α = β) :
    (letI := α; (q.comp g).reAlgebra β e) =
      (letI := β; (q.reAlgebra β e).comp (g.reAlgebra β e)) := by
  cases e
  rfl

/-- The transported full-order formal map realizes the entire-family transport square. -/
theorem reAlgebra_onPoints (g : (letI := α; Hom E E' h))
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (x : (letI := α; E.Point A)) :
    (letI := β; (g.reAlgebra β e).onPoints A (E.reAlgebraPointEquiv β e A x)) =
      E'.reAlgebraPointEquiv β e A (letI := α; g.onPoints A x) := by
  cases e
  rfl

end Hom

namespace Iso

/-- Transport both order-linear formal maps and both formal inverse equations. -/
def reAlgebra (g : (letI := α; Iso E E' h)) (β : Algebra O R) (e : α = β) :
    (letI := β; Iso (E.reAlgebra β e) (E'.reAlgebra β e) h) := by
  cases e
  exact g

/-- The transported forward map is exactly the transported original forward map. -/
@[simp]
theorem reAlgebra_hom (g : (letI := α; Iso E E' h))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (g.reAlgebra β e).hom) = (letI := α; g.hom.reAlgebra β e) := by
  cases e
  rfl

/-- The transported inverse map is exactly the transported original inverse map. -/
@[simp]
theorem reAlgebra_inv (g : (letI := α; Iso E E' h))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (g.reAlgebra β e).inv) = (letI := α; g.inv.reAlgebra β e) := by
  cases e
  rfl

end Iso
end AlgebraTransport

variable [Algebra O R] [Algebra O S]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Extend the actual full-order action to the supplied target scalar algebra. -/
def baseChangeAlong (E : OrderAction D X) (f : R →ₐ[O] S) :
    OrderAction D (X.baseChangeAlong f) :=
  (E.baseChange (coefficientTest f)).reAlgebra _ (coefficientAlgebraAlong_eq f)

/-- The extended order-action series is the series of the chosen original chart. -/
theorem baseChangeAlongOrderChart_coordinates (E : OrderAction D X) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : (X.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) (d : D) :
    ((((E.baseChangeAlong f).chart b).map
      (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
      (((E.chart (X.baseSource (coefficientTest f) b)).map
        (coefficientLift (O := O) (X.baseSource (coefficientTest f) b).val
          (restrictCoefficientAlgebra f A)
          (X.baseSource_unit (coefficientTest f) A b hb))).action d).toHom.toCoordinateMap :=
  ((E.baseChange (coefficientTest f)).reAlgebra_testChart_coordinates _
    (coefficientAlgebraAlong_eq f) A b hb d).trans
      (E.baseOrderChart_coordinates (coefficientTest f) A b hb d)

/-- The supplied-target comparison of complete families is linear over the whole order. -/
def baseChangeAlongPointEquiv (E : OrderAction D X) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) :
    E.Point (restrictCoefficientAlgebra f A) ≃ₗ[D] (E.baseChangeAlong f).Point A :=
  (E.baseChangePointEquiv (coefficientTest f) A).trans
    ((E.baseChange (coefficientTest f)).reAlgebraPointEquiv _
      (coefficientAlgebraAlong_eq f) A)

/-- Forgetting the order gives exactly the existing supplied-target family comparison. -/
theorem baseChangeAlongPointEquiv_eq (E : OrderAction D X) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (x : E.Point (restrictCoefficientAlgebra f A)) :
    E.baseChangeAlongPointEquiv f A x = X.baseChangeAlongPointEquiv f A x :=
  (E.baseChange (coefficientTest f)).reAlgebraPointEquiv_eq _
    (coefficientAlgebraAlong_eq f) A _

/-- Supplied-target extension of full-order families is natural in every test map. -/
theorem baseChangeAlongPointEquiv_natural (E : OrderAction D X) (f : R →ₐ[O] S)
    {A B : CommAlgCat.{v} S} (φ : A ⟶ B)
    (x : E.Point (restrictCoefficientAlgebra f A)) :
    (E.baseChangeAlong f).mapPoints φ (E.baseChangeAlongPointEquiv f A x) =
      E.baseChangeAlongPointEquiv f B (E.mapPoints (restrictCoefficientMap f φ) x) :=
  ((E.baseChange (coefficientTest f)).reAlgebraPointEquiv_natural _
    (coefficientAlgebraAlong_eq f) φ (E.toBaseChangePoints (coefficientTest f) A x)).trans
      (congrArg
        ((E.baseChange (coefficientTest f)).reAlgebraPointEquiv _
          (coefficientAlgebraAlong_eq f) B)
        (E.toBaseChangePoints_natural (coefficientTest f) φ x))

/-- Natural isomorphism of the full order-module point functors after scalar extension. -/
def baseChangeAlongPointFunctorIso (E : OrderAction D X) (f : R →ₐ[O] S) :
    restrictCoefficientFunctor f ⋙ E.pointFunctor ≅ (E.baseChangeAlong f).pointFunctor :=
  NatIso.ofComponents
    (fun A => (E.baseChangeAlongPointEquiv f A).toModuleIso)
    (by
      intro A B φ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (E.baseChangeAlongPointEquiv_natural f φ x).symm)

namespace Hom

/-- Extend an actual full-order formal map to the supplied target scalar structure. -/
def baseChangeAlong (g : Hom E E' h) (f : R →ₐ[O] S) :
    Hom (E.baseChangeAlong f) (E'.baseChangeAlong f)
      (baseOpens_eq (coefficientTest f) h) :=
  (g.baseChange (coefficientTest f)).reAlgebra _ (coefficientAlgebraAlong_eq f)

/-- Forgetting the order retains exactly the original supplied-target formal map. -/
@[simp]
theorem baseChangeAlong_val (g : Hom E E' h) (f : R →ₐ[O] S) :
    (g.baseChangeAlong f).val = g.val.baseChangeAlong f :=
  (g.baseChange (coefficientTest f)).reAlgebra_val _ (coefficientAlgebraAlong_eq f)

/-- Supplied-target extension preserves the identity full-order formal map. -/
@[simp]
theorem baseChangeAlong_id (E : OrderAction D X) (f : R →ₐ[O] S) :
    (Hom.id E).baseChangeAlong f = Hom.id (E.baseChangeAlong f) := by
  unfold Hom.baseChangeAlong
  rw [Hom.baseChange_id, Hom.reAlgebra_id]
  rfl

/-- Supplied-target extension preserves composition of full-order formal maps. -/
@[simp]
theorem baseChangeAlong_comp (q : Hom E' E'' k) (g : Hom E E' h) (f : R →ₐ[O] S) :
    (q.comp g).baseChangeAlong f = (q.baseChangeAlong f).comp (g.baseChangeAlong f) := by
  unfold Hom.baseChangeAlong
  rw [Hom.baseChange_comp, Hom.reAlgebra_comp]
  rfl

/-- Extended full-order formal maps realize the complete supplied-target family square. -/
theorem baseChangeAlong_onPoints (g : Hom E E' h) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (x : E.Point (restrictCoefficientAlgebra f A)) :
    (g.baseChangeAlong f).onPoints A (E.baseChangeAlongPointEquiv f A x) =
      E'.baseChangeAlongPointEquiv f A (g.onPoints (restrictCoefficientAlgebra f A) x) :=
  ((g.baseChange (coefficientTest f)).reAlgebra_onPoints _
    (coefficientAlgebraAlong_eq f) A (E.toBaseChangePoints (coefficientTest f) A x)).trans
      (congrArg
        ((E'.baseChange (coefficientTest f)).reAlgebraPointEquiv _
          (coefficientAlgebraAlong_eq f) A)
        (g.baseChange_onPoints (coefficientTest f) A x))

/-- The inverse family comparisons realize the reverse square for the same formal map. -/
theorem baseChangeAlong_fromPoints (g : Hom E E' h) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (y : (E.baseChangeAlong f).Point A) :
    g.onPoints (restrictCoefficientAlgebra f A) ((E.baseChangeAlongPointEquiv f A).symm y) =
      (E'.baseChangeAlongPointEquiv f A).symm ((g.baseChangeAlong f).onPoints A y) := by
  apply (E'.baseChangeAlongPointEquiv f A).injective
  rw [← g.baseChangeAlong_onPoints, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end Hom

namespace Iso

/-- Extend both order-linear formal maps and both inverse equations to supplied scalars. -/
def baseChangeAlong (g : Iso E E' h) (f : R →ₐ[O] S) :
    Iso (E.baseChangeAlong f) (E'.baseChangeAlong f)
      (baseOpens_eq (coefficientTest f) h) :=
  (g.baseChange (coefficientTest f)).reAlgebra _ (coefficientAlgebraAlong_eq f)

/-- The extended forward map is exactly the supplied-target extension of the original. -/
@[simp]
theorem baseChangeAlong_hom (g : Iso E E' h) (f : R →ₐ[O] S) :
    (g.baseChangeAlong f).hom = g.hom.baseChangeAlong f :=
  (g.baseChange (coefficientTest f)).reAlgebra_hom _ (coefficientAlgebraAlong_eq f)

/-- The extended inverse map is exactly the supplied-target extension of the original. -/
@[simp]
theorem baseChangeAlong_inv (g : Iso E E' h) (f : R →ₐ[O] S) :
    (g.baseChangeAlong f).inv = g.inv.baseChangeAlong f :=
  (g.baseChange (coefficientTest f)).reAlgebra_inv _ (coefficientAlgebraAlong_eq f)

/-- The full-order formal isomorphism realizes the complete-family comparison square. -/
theorem baseChangeAlong_onPoints (g : Iso E E' h) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (x : E.Point (restrictCoefficientAlgebra f A)) :
    (g.baseChangeAlong f).onPoints A (E.baseChangeAlongPointEquiv f A x) =
      E'.baseChangeAlongPointEquiv f A (g.onPoints (restrictCoefficientAlgebra f A) x) := by
  change (g.baseChangeAlong f).hom.onPoints A _ = _
  rw [baseChangeAlong_hom]
  exact g.hom.baseChangeAlong_onPoints f A x

/-- The inverse comparisons realize the reverse full-order isomorphism square. -/
theorem baseChangeAlong_fromPoints (g : Iso E E' h) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (y : (E.baseChangeAlong f).Point A) :
    g.onPoints (restrictCoefficientAlgebra f A) ((E.baseChangeAlongPointEquiv f A).symm y) =
      (E'.baseChangeAlongPointEquiv f A).symm ((g.baseChangeAlong f).onPoints A y) := by
  change g.hom.onPoints _ _ = (E'.baseChangeAlongPointEquiv f A).symm
    ((g.baseChangeAlong f).hom.onPoints A y)
  rw [baseChangeAlong_hom]
  exact g.hom.baseChangeAlong_fromPoints f A y

end Iso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
