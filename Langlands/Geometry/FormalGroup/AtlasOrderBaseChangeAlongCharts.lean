import Langlands.Geometry.FormalGroup.OrderScalarTransport
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlongComposition

/-! # Actual rational chart maps through supplied-target coefficient extension -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]

section AlgebraTransport

variable {α : Algebra O R}
variable {X : @BasicAtlas O _ R _ α σ _} {Y : @BasicAtlas O _ R _ α τ _}
variable {E : (letI := α; OrderAction D X)}
variable {E' : (letI := α; OrderAction D Y)}
variable {h : X.opens = Y.opens}

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Equal scalar structures retain both actual rational atlas maps and their inverse equations. -/
def reAlgebra (f : (letI := α; QuasiIsogeny F E E' h))
    (β : Algebra O R) (e : α = β) :
    (letI := β; QuasiIsogeny F (E.reAlgebra β e) (E'.reAlgebra β e)
      (reAlgebraOpens_eq X Y β e h)) := by
  cases e
  exact f

@[simp]
theorem reAlgebra_hom (f : (letI := α; QuasiIsogeny F E E' h))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (f.reAlgebra β e).hom) =
      (letI := α; RationalHom.reAlgebra β e f.hom) := by
  cases e
  rfl

end QuasiIsogeny

end AlgebraTransport

variable [Algebra O R]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {h : X.opens = Y.opens}

set_option backward.isDefEq.respectTransparency false in
/-- Compare the supplied scalar-retyped chart with the actual original chart
transported to the same scalar structure on the test ring. -/
def baseChangeReAlgebraOrderChartIso (E : OrderAction D X) (S : CommAlgCat.{v} R)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (A : CommAlgCat.{v} S) (b : X.baseOpens S) (hb : IsUnit (algebraMap S A b.val)) :
    (letI := β;
      ModuleLaw.OrderAction.Iso
        ((((E.baseChange S).reAlgebra β e).chart b).map
          (coefficientLift (O := O) b.val A hb))
        ((letI := coefficientAlgebra (O := O) (restrictTest S A)
          (E.chart (X.baseSource S b)).map
            (coefficientLift (O := O) (X.baseSource S b).val (restrictTest S A)
              (X.baseSource_unit S A b hb))).reAlgebra
          (coefficientAlgebra (O := O) A) (coefficientAlgebra_comp_transport S A β e))) := by
  cases e
  exact E.baseOrderChartIso S A b hb

set_option backward.isDefEq.respectTransparency false in
/-- Retain the actual source chart selected through the target's image generator. -/
def baseChangeReAlgebraSourceOrderChartIso (E : OrderAction D X) (S : CommAlgCat.{v} R)
    (h : X.opens = Y.opens) (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S) (hb : IsUnit (algebraMap S A b.val)) :
    (letI := β;
      ModuleLaw.OrderAction.Iso
        ((((E.baseChange S).reAlgebra β e).chart
          (sourceChart (X := (X.baseChange S).reAlgebra β e)
            (Y := (Y.baseChange S).reAlgebra β e) (baseOpens_eq S h) b)).map (coefficientLift (O := O) b.val A hb))
        ((letI := coefficientAlgebra (O := O) (restrictTest S A)
          (E.chart (sourceChart h (Y.baseSource S b))).map
            (coefficientLift (O := O) (Y.baseSource S b).val (restrictTest S A)
              (Y.baseSource_unit S A b hb))).reAlgebra
          (coefficientAlgebra (O := O) A) (coefficientAlgebra_comp_transport S A β e))) := by
  cases e
  exact E.baseSourceOrderChartIso S h A b hb

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

set_option backward.isDefEq.respectTransparency false in
/-- Retain the specified original chart quasi-isogeny at the induced new test scalar structure. -/
def originalChartReAlgebra (f : QuasiIsogeny F E E' h)
    (S : CommAlgCat.{v} R) (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S) (hb : IsUnit (algebraMap S A b.val)) :
    (letI := β;
      letI := coefficientAlgebra (O := O) A
      ModuleLaw.OrderAction.QuasiIsogeny F
        ((letI := coefficientAlgebra (O := O) (restrictTest S A)
          (E.chart (sourceChart h (Y.baseSource S b))).map
            (coefficientLift (O := O) (Y.baseSource S b).val (restrictTest S A)
              (Y.baseSource_unit S A b hb))).reAlgebra
          (coefficientAlgebra (O := O) A) (coefficientAlgebra_comp_transport S A β e))
        ((letI := coefficientAlgebra (O := O) (restrictTest S A)
          (E'.chart (Y.baseSource S b)).map
            (coefficientLift (O := O) (Y.baseSource S b).val (restrictTest S A)
              (Y.baseSource_unit S A b hb))).reAlgebra
          (coefficientAlgebra (O := O) A) (coefficientAlgebra_comp_transport S A β e))) := by
  cases e
  exact f.onChart (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb)

set_option backward.isDefEq.respectTransparency false in
/-- Actual chart evaluation of scalar-retyped coefficient extension is conjugation
of the same original chart quasi-isogeny, with all scalar structures retained. -/
theorem onChart_baseChangeReAlgebra (f : QuasiIsogeny F E E' h)
    (S : CommAlgCat.{v} R) (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S) (hb : IsUnit (algebraMap S A b.val)) :
    (letI := β; ((f.baseChange S).reAlgebra β e).onChart A b hb) =
      (letI := β;
        letI := coefficientAlgebra (O := O) A
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F)
          (baseChangeReAlgebraSourceOrderChartIso E S h β e A b hb)).trans
          ((originalChartReAlgebra f S β e A b hb).trans
            (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
              (baseChangeReAlgebraOrderChartIso E' S β e A b hb)).symm)) := by
  cases e
  exact f.onChart_baseChange S A b hb

end QuasiIsogeny

variable {S : Type v} [CommRing S] [Algebra O S]

/-- The actual coefficient chart comparison over independently supplied target scalars. -/
def baseChangeAlongOrderChartIso (E : OrderAction D X) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : (X.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) :=
  baseChangeReAlgebraOrderChartIso E (coefficientTest f) _
    (coefficientAlgebraAlong_eq f) A b hb

/-- The actual supplied-target source comparison retains the target-selected original chart. -/
def baseChangeAlongSourceOrderChartIso (E : OrderAction D X) (f : R →ₐ[O] S)
    (h : X.opens = Y.opens) (A : CommAlgCat.{v} S) (b : (Y.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) :=
  baseChangeReAlgebraSourceOrderChartIso E (coefficientTest f) h _
    (coefficientAlgebraAlong_eq f) A b hb

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

set_option backward.isDefEq.respectTransparency false in
/-- The specified supplied-target quasi-isogeny has exactly the original chart map
through the actual source, scalar and target comparisons. -/
theorem onChart_baseChangeAlong (g : QuasiIsogeny F E E' h) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : (Y.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) :
    (g.baseChangeAlong f).onChart A b hb =
      (letI := coefficientAlgebra (O := O) A
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F)
        (baseChangeAlongSourceOrderChartIso E f h A b hb)).trans
        ((originalChartReAlgebra g (coefficientTest f) _ (coefficientAlgebraAlong_eq f) A b hb).trans
          (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
            (baseChangeAlongOrderChartIso E' f A b hb)).symm)) := by
  have he : g.baseChangeAlong f =
      (g.baseChange (coefficientTest f)).reAlgebra _ (coefficientAlgebraAlong_eq f) := by
    apply ext_hom
    rw [reAlgebra_hom]
    rfl
  rw [he]
  exact onChart_baseChangeReAlgebra g (coefficientTest f) _
    (coefficientAlgebraAlong_eq f) A b hb

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
