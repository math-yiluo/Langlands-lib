import Langlands.Geometry.FormalGroup.AtlasAlgebraTransport
import Langlands.Geometry.FormalGroup.AtlasBaseChangeMorphism

/-! # Coefficient extension to a supplied scalar algebra structure -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section AlgebraTransport

variable {α : Algebra O R}
variable {X : @BasicAtlas O _ R _ α σ _}
variable {Y : @BasicAtlas O _ R _ α τ _}
variable {Z : @BasicAtlas O _ R _ α υ _}
variable {h : (letI := α; X.opens = Y.opens)} {k : (letI := α; Y.opens = Z.opens)}

/-- Algebra transport identifies the entire compatible-family modules. -/
def reAlgebraPointEquiv (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R) :
    (letI := α; X.Point A) ≃ₗ[O] (letI := β; (X.reAlgebra β e).Point A) := by
  cases e
  exact LinearEquiv.refl O _

/-- The transported family has its original tuple at each corresponding test. -/
@[simp]
theorem reAlgebraPointEquiv_apply (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (x : (letI := α; X.Point A)) (B : CommAlgCat.{v} R) (φ : A ⟶ B)
    (a : (letI := α; X.opens)) (ha : IsUnit (algebraMap R B a.val)) :
    (letI := β; (X.reAlgebraPointEquiv β e A x).val ⟨B, φ, a, ha⟩) =
      (letI := α; x.val ⟨B, φ, a, ha⟩) := by
  cases e
  rfl

/-- Algebra transport commutes with every coefficient map on whole families. -/
theorem reAlgebraPointEquiv_natural (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : (letI := α; X.Point A)) :
    (letI := β; (X.reAlgebra β e).mapPoints φ (X.reAlgebraPointEquiv β e A x)) =
      X.reAlgebraPointEquiv β e B (letI := α; X.mapPoints φ x) := by
  cases e
  rfl

namespace Hom

/-- Transport an actual formal atlas map along equality of scalar structures. -/
def reAlgebra (f : (letI := α; Hom X Y h)) (β : Algebra O R) (e : α = β) :
    (letI := β; Hom (X.reAlgebra β e) (Y.reAlgebra β e) h) := by
  cases e
  exact f

/-- The actual formal series of a transported map are unchanged. -/
@[simp]
theorem reAlgebra_coordinates (f : (letI := α; Hom X Y h))
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (b : (letI := α; Y.opens)) (hb : IsUnit (algebraMap R A b.val)) :
    (letI := β; ((f.reAlgebra β e).hom A b hb).toHom.toCoordinateMap) =
      (letI := α; (f.hom A b hb).toHom.toCoordinateMap) := by
  cases e
  rfl

/-- Transport preserves the identity formal atlas map. -/
@[simp]
theorem reAlgebra_id (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) :
    (letI := α; (Hom.id X).reAlgebra β e) =
      (letI := β; Hom.id (X.reAlgebra β e)) := by
  cases e
  rfl

/-- Transport preserves composition of actual formal atlas maps. -/
@[simp]
theorem reAlgebra_comp (g : (letI := α; Hom Y Z k)) (f : (letI := α; Hom X Y h))
    (β : Algebra O R) (e : α = β) :
    (letI := α; (g.comp f).reAlgebra β e) =
      (letI := β; (g.reAlgebra β e).comp (f.reAlgebra β e)) := by
  cases e
  rfl

/-- Transported formal maps realize the full compatible-family square. -/
theorem reAlgebra_onPoints (f : (letI := α; Hom X Y h))
    (β : Algebra O R) (e : α = β) (A : CommAlgCat.{v} R)
    (x : (letI := α; X.Point A)) :
    (letI := β; (f.reAlgebra β e).onPoints A (X.reAlgebraPointEquiv β e A x)) =
      Y.reAlgebraPointEquiv β e A (letI := α; f.onPoints A x) := by
  cases e
  rfl

end Hom

namespace Iso

/-- Transport both formal maps and both inverse equations. -/
def reAlgebra (f : (letI := α; Iso X Y h)) (β : Algebra O R) (e : α = β) :
    (letI := β; Iso (X.reAlgebra β e) (Y.reAlgebra β e) h) := by
  cases e
  exact f

/-- The forward transported isomorphism is exactly the transported formal map. -/
@[simp]
theorem reAlgebra_hom (f : (letI := α; Iso X Y h)) (β : Algebra O R) (e : α = β) :
    (letI := β; (f.reAlgebra β e).hom) = (letI := α; f.hom.reAlgebra β e) := by
  cases e
  rfl

/-- The inverse transported isomorphism is exactly the transported inverse map. -/
@[simp]
theorem reAlgebra_inv (f : (letI := α; Iso X Y h)) (β : Algebra O R) (e : α = β) :
    (letI := β; (f.reAlgebra β e).inv) = (letI := α; f.inv.reAlgebra β e) := by
  cases e
  rfl

end Iso

end AlgebraTransport

variable [Algebra O R] [Algebra O S]

/-- The coefficient algebra defined by an O-algebra homomorphism. -/
abbrev coefficientTest (f : R →ₐ[O] S) : CommAlgCat.{v} R :=
  letI := f.toRingHom.toAlgebra
  CommAlgCat.of R S

/-- Its structural composite O-algebra equals the supplied target structure. -/
theorem coefficientAlgebraAlong_eq (f : R →ₐ[O] S) :
    coefficientAlgebra (O := O) (coefficientTest f) = (inferInstance : Algebra O S) := by
  apply Algebra.algebra_ext
  intro a
  exact f.commutes a

/-- Extend an atlas to the independently supplied target O-algebra. -/
def baseChangeAlong (X : BasicAtlas O R σ) (f : R →ₐ[O] S) : BasicAtlas O S σ :=
  (X.baseChange (coefficientTest f)).reAlgebra _ (coefficientAlgebraAlong_eq f)

/-- The actual principal generators are the images under the given map. -/
@[simp]
theorem baseChangeAlong_opens (X : BasicAtlas O R σ) (f : R →ₐ[O] S) :
    (X.baseChangeAlong f).opens = f '' X.opens := rfl

/-- The full family equivalence for extension to a supplied O-algebra. -/
def baseChangeAlongPointEquiv (X : BasicAtlas O R σ) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) :
    X.Point (restrictCoefficientAlgebra f A) ≃ₗ[O] (X.baseChangeAlong f).Point A :=
  (X.baseChangePointEquiv (coefficientTest f) A).trans
    ((X.baseChange (coefficientTest f)).reAlgebraPointEquiv _
      (coefficientAlgebraAlong_eq f) A)

/-- The supplied-target family comparison commutes with all test maps. -/
theorem baseChangeAlongPointEquiv_natural (X : BasicAtlas O R σ) (f : R →ₐ[O] S)
    {A B : CommAlgCat.{v} S} (φ : A ⟶ B)
    (x : X.Point (restrictCoefficientAlgebra f A)) :
    (X.baseChangeAlong f).mapPoints φ (X.baseChangeAlongPointEquiv f A x) =
      X.baseChangeAlongPointEquiv f B (X.mapPoints (restrictCoefficientMap f φ) x) :=
  ((X.baseChange (coefficientTest f)).reAlgebraPointEquiv_natural _
    (coefficientAlgebraAlong_eq f) φ (X.toBaseChangePoints (coefficientTest f) A x)).trans
      (congrArg
        ((X.baseChange (coefficientTest f)).reAlgebraPointEquiv _
          (coefficientAlgebraAlong_eq f) B)
        (X.toBaseChangePoints_natural (coefficientTest f) φ x))

/-- A natural isomorphism on the entire compatible-family point functors. -/
def baseChangeAlongPointFunctorIso (X : BasicAtlas O R σ) (f : R →ₐ[O] S) :
    restrictCoefficientFunctor f ⋙ X.pointFunctor ≅ (X.baseChangeAlong f).pointFunctor :=
  NatIso.ofComponents
    (fun A => (X.baseChangeAlongPointEquiv f A).toModuleIso)
    (by
      intro A B φ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (X.baseChangeAlongPointEquiv_natural f φ x).symm)

namespace Hom

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Extend an actual formal atlas map to the supplied target scalar structure. -/
def baseChangeAlong (g : Hom X Y h) (f : R →ₐ[O] S) :
    Hom (X.baseChangeAlong f) (Y.baseChangeAlong f) (baseOpens_eq (coefficientTest f) h) :=
  (g.baseChange (coefficientTest f)).reAlgebra _ (coefficientAlgebraAlong_eq f)

/-- Supplied-target extension preserves identity formal maps. -/
@[simp]
theorem baseChangeAlong_id (X : BasicAtlas O R σ) (f : R →ₐ[O] S) :
    (Hom.id X).baseChangeAlong f = Hom.id (X.baseChangeAlong f) := by
  unfold Hom.baseChangeAlong
  rw [Hom.baseChange_id, Hom.reAlgebra_id]
  rfl

/-- Supplied-target extension preserves composition of formal maps. -/
@[simp]
theorem baseChangeAlong_comp (q : Hom Y Z k) (g : Hom X Y h) (f : R →ₐ[O] S) :
    (q.comp g).baseChangeAlong f = (q.baseChangeAlong f).comp (g.baseChangeAlong f) := by
  unfold Hom.baseChangeAlong
  rw [Hom.baseChange_comp, Hom.reAlgebra_comp]
  rfl

/-- Extended formal maps commute with the complete supplied-target family comparison. -/
theorem baseChangeAlong_onPoints (g : Hom X Y h) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (x : X.Point (restrictCoefficientAlgebra f A)) :
    (g.baseChangeAlong f).onPoints A (X.baseChangeAlongPointEquiv f A x) =
      Y.baseChangeAlongPointEquiv f A (g.onPoints (restrictCoefficientAlgebra f A) x) :=
  ((g.baseChange (coefficientTest f)).reAlgebra_onPoints _
    (coefficientAlgebraAlong_eq f) A (X.toBaseChangePoints (coefficientTest f) A x)).trans
      (congrArg
        ((Y.baseChange (coefficientTest f)).reAlgebraPointEquiv _
          (coefficientAlgebraAlong_eq f) A)
        (g.baseChange_onPoints (coefficientTest f) A x))

/-- The inverse complete-family comparison commutes with the same formal map. -/
theorem baseChangeAlong_fromPoints (g : Hom X Y h) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (y : (X.baseChangeAlong f).Point A) :
    g.onPoints (restrictCoefficientAlgebra f A) ((X.baseChangeAlongPointEquiv f A).symm y) =
      (Y.baseChangeAlongPointEquiv f A).symm ((g.baseChangeAlong f).onPoints A y) := by
  apply (Y.baseChangeAlongPointEquiv f A).injective
  rw [← g.baseChangeAlong_onPoints, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end Hom

namespace Iso

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {h : X.opens = Y.opens}

/-- Extend both maps of a formal isomorphism to the supplied scalar structure. -/
def baseChangeAlong (g : Iso X Y h) (f : R →ₐ[O] S) :
    Iso (X.baseChangeAlong f) (Y.baseChangeAlong f) (baseOpens_eq (coefficientTest f) h) :=
  (g.baseChange (coefficientTest f)).reAlgebra _ (coefficientAlgebraAlong_eq f)

end Iso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
