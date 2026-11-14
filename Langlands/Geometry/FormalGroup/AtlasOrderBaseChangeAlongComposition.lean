import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlongComposition
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeComposition

/-! # Successive supplied coefficient maps with the full acting order -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Retype the actual full-order composition isomorphism at intermediate and final bases. -/
def baseCompReAlgebraIso (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ) :
    (letI := γ;
      Iso
        ((letI := β; ((E.baseChange S).reAlgebra β e).baseChange T).reAlgebra γ d)
        ((E.baseChange (restrictTest S T)).reAlgebra γ
          ((coefficientAlgebra_comp_transport S T β e).trans d))
        (X.baseCompOpens_eq S T)) := by
  cases e
  cases d
  exact E.baseCompIso S T

/-- Forgetting the order retains the exact transported forward formal map. -/
@[simp]
theorem baseCompReAlgebraIso_hom_val (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ) :
    (letI := γ; (E.baseCompReAlgebraIso S T β e γ d).hom.val) =
      (letI := γ; (X.baseCompReAlgebraIso S T β e γ d).hom) := by
  cases e
  cases d
  rfl

/-- Forgetting the order also retains the exact transported reverse formal map. -/
@[simp]
theorem baseCompReAlgebraIso_inv_val (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ) :
    (letI := γ; (E.baseCompReAlgebraIso S T β e γ d).inv.val) =
      (letI := γ; (X.baseCompReAlgebraIso S T β e γ d).inv) := by
  cases e
  cases d
  rfl

/-- Transport preserves the complete-family square with its entire order-module structure. -/
theorem baseCompReAlgebra_onPoints (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ)
    (A : CommAlgCat.{v} T) (x : E.Point (restrictTest (restrictTest S T) A)) :
    (letI := γ;
      (E.baseCompReAlgebraIso S T β e γ d).onPoints A
        ((letI := β; ((E.baseChange S).reAlgebra β e).baseChange T).reAlgebraPointEquiv
          γ d A
          (letI := β; ((E.baseChange S).reAlgebra β e).toBaseChangePoints T A
            ((E.baseChange S).reAlgebraPointEquiv β e (restrictTest T A)
              (E.toBaseChangePoints S (restrictTest T A) x))))) =
      (E.baseChange (restrictTest S T)).reAlgebraPointEquiv γ
        ((coefficientAlgebra_comp_transport S T β e).trans d) A
        (E.toBaseChangePoints (restrictTest S T) A x) := by
  cases e
  cases d
  exact E.baseComp_onPoints S T A x

variable {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]

/-- Successive supplied extensions compare by actual inverse full-order formal maps. -/
def baseAlongCompIso (E : OrderAction D X) (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    Iso ((E.baseChangeAlong f).baseChangeAlong g)
      (E.baseChangeAlong (g.comp f)) (X.baseAlongCompOpens_eq f g) :=
  E.baseCompReAlgebraIso (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g)

/-- The forward full-order map has exactly the existing basic formal series. -/
@[simp]
theorem baseAlongCompIso_hom_val (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E.baseAlongCompIso f g).hom.val = (X.baseAlongCompIso f g).hom :=
  E.baseCompReAlgebraIso_hom_val (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g)

/-- The reverse full-order map has exactly the existing reverse basic formal series. -/
@[simp]
theorem baseAlongCompIso_inv_val (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E.baseAlongCompIso f g).inv.val = (X.baseAlongCompIso f g).inv :=
  E.baseCompReAlgebraIso_inv_val (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g)

/-- The formal comparison realizes successive extension of every full order-module family. -/
theorem baseAlongComp_onPoints (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (A : CommAlgCat.{v} T)
    (x : E.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    (E.baseAlongCompIso f g).onPoints A
      ((E.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (E.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x)) =
      E.baseChangeAlongPointEquiv (g.comp f) A x :=
  E.baseCompReAlgebra_onPoints (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g) A x

/-- The actual formal inverse realizes the reverse full-family composition square. -/
theorem baseAlongComp_inv_onPoints (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (A : CommAlgCat.{v} T)
    (x : E.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    ((E.baseAlongCompIso f g).onPoints A).symm
      (E.baseChangeAlongPointEquiv (g.comp f) A x) =
      (E.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (E.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x) :=
  (LinearEquiv.symm_apply_eq ((E.baseAlongCompIso f g).onPoints A)).mpr
    (E.baseAlongComp_onPoints f g A x).symm

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
