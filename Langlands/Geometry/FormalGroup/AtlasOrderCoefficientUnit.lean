import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonTestComposition
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeSelf

/-! # Actual formal unit coherence for coefficient extension -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Iterated and direct source selections agree when the first coefficient map is the identity. -/
theorem baseComp_left_unit_source (X : BasicAtlas O R σ) (f : R →ₐ[O] S)
    (b : X.baseOpens (restrictTest (coefficientTest (AlgHom.id O R)) (coefficientTest f))) :
    X.baseCompIterSource (coefficientTest (AlgHom.id O R)) (coefficientTest f) b =
      X.baseSource (restrictTest (coefficientTest (AlgHom.id O R)) (coefficientTest f)) b := by
  have h := baseSource_sourceChart (X := X.baseChangeAlong (AlgHom.id O R)) (Y := X)
    (coefficientTest f) X.baseIdOpens_eq b
  have hh := congrArg (fun q => X.baseSource (coefficientTest (AlgHom.id O R)) q) h
  exact hh.trans (X.baseIdSource_eq (X.baseSource (coefficientTest f) b))

/-- Iterated and direct source selections agree when the second coefficient map is the identity. -/
theorem baseComp_right_unit_source (X : BasicAtlas O R σ) (f : R →ₐ[O] S)
    (b : X.baseOpens (restrictTest (coefficientTest f) (coefficientTest (AlgHom.id O S)))) :
    X.baseCompIterSource (coefficientTest f) (coefficientTest (AlgHom.id O S)) b =
      X.baseSource (restrictTest (coefficientTest f) (coefficientTest (AlgHom.id O S))) b := by
  exact congrArg (fun q => X.baseSource (coefficientTest f) q)
    ((X.baseChangeAlong f).baseIdSource_eq b)

/-- Scalar transport retains the complete coordinate formula of the actual coefficient-composition map. -/
theorem baseCompReAlgebraIso_hom_coordinates (X : BasicAtlas O R σ)
    (B : CommAlgCat.{v} R) (C : CommAlgCat.{v} B)
    (β : Algebra O B) (e : coefficientAlgebra (O := O) B = β)
    (γ : Algebra O C) (d : (letI := β; coefficientAlgebra (O := O) C) = γ)
    (A : CommAlgCat.{v} C) (b : X.baseOpens (restrictTest B C))
    (hb : IsUnit (algebraMap C A b.val)) :
    (letI := γ; ((X.baseCompReAlgebraIso B C β e γ d).hom.hom A b hb).toHom.toCoordinateMap) =
      (X.transition (restrictTest (restrictTest B C) A)
        (X.baseCompIterSource B C b) (X.baseSource (restrictTest B C) b)
        (X.baseCompIter_unit B C A b hb) (X.baseSource_unit (restrictTest B C) A b hb)).hom.toHom.toCoordinateMap := by
  cases e
  cases d
  exact X.baseCompChartIso_coordinates B C A b hb

/-- The actual left coefficient-composition unit has complete identity chart series. -/
theorem baseAlongCompIso_left_unit_hom_coordinates (X : BasicAtlas O R σ) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : (X.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) :
    ((X.baseAlongCompIso (AlgHom.id O R) f).hom.hom A b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  let B := coefficientTest (AlgHom.id O R)
  let C := coefficientTest f
  have h := X.baseCompReAlgebraIso_hom_coordinates B C _
    (coefficientAlgebraAlong_eq (AlgHom.id O R)) _ (coefficientAlgebraAlong_eq f) A b hb
  let T := restrictTest (restrictTest B C) A
  let x := X.baseCompIterSource B C b
  let y := X.baseSource (restrictTest B C) b
  have hx : IsUnit (algebraMap R T x.val) := X.baseCompIter_unit B C A b hb
  have hy : IsUnit (algebraMap R T y.val) := X.baseSource_unit (restrictTest B C) A b hb
  have ht := X.testTransition_coordinates_eq T x y y y hx hy hy hy
    (X.baseComp_left_unit_source f b) rfl
  exact h.trans (ht.trans (congrArg (fun q => q.hom.toHom.toCoordinateMap)
    (X.transition_self T y hy)))

/-- The actual right coefficient-composition unit has complete identity chart series. -/
theorem baseAlongCompIso_right_unit_hom_coordinates (X : BasicAtlas O R σ) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : (X.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) :
    ((X.baseAlongCompIso f (AlgHom.id O S)).hom.hom A b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  let B := coefficientTest f
  let C := coefficientTest (AlgHom.id O S)
  have h := X.baseCompReAlgebraIso_hom_coordinates B C _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq (AlgHom.id O S)) A b hb
  let T := restrictTest (restrictTest B C) A
  let x := X.baseCompIterSource B C b
  let y := X.baseSource (restrictTest B C) b
  have hx : IsUnit (algebraMap R T x.val) := X.baseCompIter_unit B C A b hb
  have hy : IsUnit (algebraMap R T y.val) := X.baseSource_unit (restrictTest B C) A b hb
  have ht := X.testTransition_coordinates_eq T x y y y hx hy hy hy
    (X.baseComp_right_unit_source f b) rfl
  exact h.trans (ht.trans (congrArg (fun q => q.hom.toHom.toCoordinateMap)
    (X.transition_self T y hy)))

namespace Hom

variable {τ : Type} [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {h : X.opens = Y.opens}

set_option backward.isDefEq.respectTransparency false in
/-- Supplied-target extension retains the complete original chart-map series on the restricted test. -/
theorem baseChangeAlong_coordinates (a : Hom X Y h) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : (Y.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) :
    ((a.baseChangeAlong f).hom A b hb).toHom.toCoordinateMap =
      (a.hom (restrictCoefficientAlgebra f A) (Y.baseSource (coefficientTest f) b)
        (Y.baseSource_unit (coefficientTest f) A b hb)).toHom.toCoordinateMap := by
  exact (Hom.reAlgebra_coordinates (a.baseChange (coefficientTest f)) _
    (coefficientAlgebraAlong_eq f) A b hb).trans (a.baseChange_coordinates (coefficientTest f) A b hb)

end Hom

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual left unit is extension of the identity-base comparison. -/
theorem baseAlongCompIso_left_unit (E : OrderAction D X) (f : R →ₐ[O] S) :
    E.baseAlongCompIso (AlgHom.id O R) f = E.baseIdIso.baseChangeAlong f := by
  apply Iso.ext_hom
  rw [Iso.baseChangeAlong_hom]
  apply Subtype.ext
  rw [baseAlongCompIso_hom_val, Hom.baseChangeAlong_val]
  apply BasicAtlas.Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  have h := X.baseIdHom.baseChangeAlong_coordinates f A b hb
  exact (X.baseAlongCompIso_left_unit_hom_coordinates f A b hb).trans h.symm

/-- The actual right unit is the identity-base comparison of the extended action. -/
theorem baseAlongCompIso_right_unit (E : OrderAction D X) (f : R →ₐ[O] S) :
    E.baseAlongCompIso f (AlgHom.id O S) = (E.baseChangeAlong f).baseIdIso := by
  apply Iso.ext_hom
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change ((E.baseAlongCompIso f (AlgHom.id O S)).hom.val.hom A b hb).toHom.toCoordinateMap =
    CoordinateMap.id
  rw [baseAlongCompIso_hom_val]
  exact X.baseAlongCompIso_right_unit_hom_coordinates f A b hb

variable [IsDomain O] {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]

/-- The actual rational test square identifying the two left-unit formal routes. -/
def baseAlongLeftUnitTestSquare (E : OrderAction D X) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : (X.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) :=
  let a := (E.baseIdIso.baseChangeAlong f).onChart A b hb
  let c := (E.baseAlongCompIso (AlgHom.id O R) f).onChart A b hb
  ModuleLaw.OrderAction.Iso.rationalSquare (F := F) a (ModuleLaw.OrderAction.Iso.refl _)
    c (ModuleLaw.OrderAction.Iso.refl _) (by
      have h := congrArg (fun z => z.onChart A b hb) (E.baseAlongCompIso_left_unit f)
      apply ModuleLaw.OrderAction.Iso.ext_hom
      change (ModuleLaw.OrderAction.Hom.id _).comp a.hom = (ModuleLaw.OrderAction.Hom.id _).comp c.hom
      simp only [ModuleLaw.OrderAction.Hom.id_comp]
      exact congrArg ModuleLaw.OrderAction.Iso.hom h.symm)

/-- The actual rational test square identifying the two right-unit formal routes. -/
def baseAlongRightUnitTestSquare (E : OrderAction D X) (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : (X.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val)) :=
  let a := (E.baseAlongCompIso f (AlgHom.id O S)).onChart A b hb
  let c := (E.baseChangeAlong f).baseIdIso.onChart A b hb
  ModuleLaw.OrderAction.Iso.rationalSquare (F := F) a (ModuleLaw.OrderAction.Iso.refl _)
    c (ModuleLaw.OrderAction.Iso.refl _) (by
      have h := congrArg (fun z => z.onChart A b hb) (E.baseAlongCompIso_right_unit f)
      apply ModuleLaw.OrderAction.Iso.ext_hom
      change (ModuleLaw.OrderAction.Hom.id _).comp a.hom = (ModuleLaw.OrderAction.Hom.id _).comp c.hom
      simp only [ModuleLaw.OrderAction.Hom.id_comp]
      exact congrArg ModuleLaw.OrderAction.Iso.hom h)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
