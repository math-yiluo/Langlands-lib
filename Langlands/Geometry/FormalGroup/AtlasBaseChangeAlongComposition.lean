import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasBaseChangeComposition

/-! # Successive supplied coefficient maps of actual formal atlases -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Changing the intermediate scalar structure changes the composite in the same way. -/
theorem coefficientAlgebra_comp_transport (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) (β : Algebra O S)
    (e : coefficientAlgebra (O := O) S = β) :
    coefficientAlgebra (O := O) (restrictTest S T) =
      (letI := β; coefficientAlgebra (O := O) T) := by
  cases e
  rfl

/-- Retype the actual raw composition isomorphism at both intermediate and final bases. -/
def baseCompReAlgebraIso (X : BasicAtlas O R σ)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ) :
    (letI := γ;
      Iso
        ((letI := β; ((X.baseChange S).reAlgebra β e).baseChange T).reAlgebra γ d)
        ((X.baseChange (restrictTest S T)).reAlgebra γ
          ((coefficientAlgebra_comp_transport S T β e).trans d))
        (X.baseCompOpens_eq S T)) := by
  cases e
  cases d
  exact X.baseCompIso S T

/-- The transported actual isomorphism retains the raw complete-family composition square. -/
theorem baseCompReAlgebra_onPoints (X : BasicAtlas O R σ)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ)
    (A : CommAlgCat.{v} T) (x : X.Point (restrictTest (restrictTest S T) A)) :
    (letI := γ;
      (X.baseCompReAlgebraIso S T β e γ d).onPoints A
        ((letI := β; ((X.baseChange S).reAlgebra β e).baseChange T).reAlgebraPointEquiv
          γ d A
          (letI := β; ((X.baseChange S).reAlgebra β e).toBaseChangePoints T A
            ((X.baseChange S).reAlgebraPointEquiv β e (restrictTest T A)
              (X.toBaseChangePoints S (restrictTest T A) x))))) =
      (X.baseChange (restrictTest S T)).reAlgebraPointEquiv γ
        ((coefficientAlgebra_comp_transport S T β e).trans d) A
        (X.toBaseChangePoints (restrictTest S T) A x) := by
  cases e
  cases d
  exact X.baseComp_onPoints S T A x

variable {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]

/-- Successive supplied-map image covers equal the image under the actual composite. -/
theorem baseAlongCompOpens_eq (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    ((X.baseChangeAlong f).baseChangeAlong g).opens =
      (X.baseChangeAlong (g.comp f)).opens := by
  change g '' (f '' X.opens) = (g.comp f) '' X.opens
  rw [Set.image_image]
  rfl

/-- Successive supplied coefficient extensions compare by actual inverse formal maps. -/
def baseAlongCompIso (X : BasicAtlas O R σ) (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    Iso ((X.baseChangeAlong f).baseChangeAlong g)
      (X.baseChangeAlong (g.comp f)) (X.baseAlongCompOpens_eq f g) :=
  X.baseCompReAlgebraIso (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g)

/-- The actual formal comparison realizes successive extension of every complete family. -/
theorem baseAlongComp_onPoints (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (A : CommAlgCat.{v} T)
    (x : X.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    (X.baseAlongCompIso f g).onPoints A
      ((X.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (X.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x)) =
      X.baseChangeAlongPointEquiv (g.comp f) A x :=
  X.baseCompReAlgebra_onPoints (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g) A x

/-- The same formal inverse realizes the reverse complete-family composition square. -/
theorem baseAlongComp_inv_onPoints (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (A : CommAlgCat.{v} T)
    (x : X.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    ((X.baseAlongCompIso f g).onPoints A).symm
      (X.baseChangeAlongPointEquiv (g.comp f) A x) =
      (X.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (X.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x) :=
  (LinearEquiv.symm_apply_eq ((X.baseAlongCompIso f g).onPoints A)).mpr
    (X.baseAlongComp_onPoints f g A x).symm

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
