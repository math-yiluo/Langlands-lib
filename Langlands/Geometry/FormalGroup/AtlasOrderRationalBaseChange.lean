import Langlands.Geometry.FormalGroup.AtlasRationalBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeMorphism
import Langlands.Geometry.FormalGroup.AtlasOrderRationalMorphism

/-! # Coefficient extension of full-order rational formal atlas maps -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual source coefficient comparison retains the entire order action. -/
def baseSourceOrderChartIso (E : OrderAction D X) (S : CommAlgCat.{v} R)
    (h : X.opens = Y.opens) (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.OrderAction.Iso
      (((E.baseChange S).chart (sourceChart (baseOpens_eq S h) b)).map
        (coefficientLift (O := O) b.val A hb))
      ((E.chart (sourceChart h (Y.baseSource S b))).map
        (coefficientLift (O := O) (Y.baseSource S b).val (restrictTest S A)
          (Y.baseSource_unit S A b hb))) where
  hom := ⟨(baseSourceChartIso S h A b hb).hom, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((((E.baseOrderChart S (sourceChart (baseOpens_eq S h) b)).map _).action d).toHom.toCoordinateMap) =
      ((((E.chart (sourceChart h (Y.baseSource S b))).map _).action d).toHom.toCoordinateMap).comp
        CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, E.baseSourceOrderChart_coordinates]⟩
  inv := ⟨(baseSourceChartIso S h A b hb).inv, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((((E.chart (sourceChart h (Y.baseSource S b))).map _).action d).toHom.toCoordinateMap) =
      ((((E.baseOrderChart S (sourceChart (baseOpens_eq S h) b)).map _).action d).toHom.toCoordinateMap).comp
        CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, E.baseSourceOrderChart_coordinates]⟩
  inv_hom := by
    apply Subtype.ext
    exact (baseSourceChartIso S h A b hb).inv_hom
  hom_inv := by
    apply Subtype.ext
    exact (baseSourceChartIso S h A b hb).hom_inv

namespace RationalHom

/-- Actual coefficient-chart conjugation preserves full-order rational commutation. -/
theorem baseChange_mem (f : RationalHom F E E' h) (S : CommAlgCat.{v} R) :
    BasicAtlas.RationalHom.baseChange (X := X) (Y := Y) (h := h) S f.val ∈
      rationalHomSubmodule F (E.baseChange S) (E'.baseChange S) (baseOpens_eq S h) := by
  intro A b hb a
  have hc := ((ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
    (E'.baseOrderChartIso S A b hb).inv).comp
      ((f.onChart (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb)).comp
        (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
          (E.baseSourceOrderChartIso S h A b hb).hom))).commutes a
  have he := BasicAtlas.RationalHom.onChart_baseChange (X := X) (Y := Y) (h := h) f.val S A b hb
  exact (congrArg (fun t => ModuleLaw.RationalHom.comp t
    (ModuleLaw.RationalHom.ofHom
      ((((E.baseChange S).chart (sourceChart (baseOpens_eq S h) b)).map
        (coefficientLift (O := O) b.val A hb)).action a))) he).trans
    (hc.trans (congrArg (fun t => ModuleLaw.RationalHom.comp
      (ModuleLaw.RationalHom.ofHom
        ((((E'.baseChange S).chart b).map
          (coefficientLift (O := O) b.val A hb)).action a)) t) he.symm))

/-- Extend the ambient global tensor map, retaining every order commutation equation. -/
def baseChange (S : CommAlgCat.{v} R) :
    RationalHom F E E' h →ₗ[F]
      RationalHom F (E.baseChange S) (E'.baseChange S) (baseOpens_eq S h) where
  toFun f := ⟨BasicAtlas.RationalHom.baseChange (X := X) (Y := Y) (h := h) S f.val,
    baseChange_mem f S⟩
  map_add' f g := by
    apply ext
    exact (BasicAtlas.RationalHom.baseChange (F := F) (X := X) (Y := Y) (h := h) S).map_add f.val g.val
  map_smul' c f := by
    apply ext
    exact (BasicAtlas.RationalHom.baseChange (F := F) (X := X) (Y := Y) (h := h) S).map_smul c f.val

@[simp]
theorem baseChange_val (S : CommAlgCat.{v} R) (f : RationalHom F E E' h) :
    (baseChange (E := E) (E' := E') (h := h) S f).val =
      BasicAtlas.RationalHom.baseChange (X := X) (Y := Y) (h := h) S f.val := rfl

/-- Extension agrees with rationalization of integral full-order coefficient extension. -/
@[simp]
theorem baseChange_ofHom (S : CommAlgCat.{v} R) (f : Hom E E' h) :
    baseChange (E := E) (E' := E') (h := h) S (ofHom (F := F) f) =
      ofHom (F := F) (f.baseChange S) := by
  apply ext
  exact BasicAtlas.RationalHom.baseChange_ofHom S f.val

/-- Full-order coefficient extension preserves the rational formal identity. -/
@[simp]
theorem baseChange_id (E : OrderAction D X) (S : CommAlgCat.{v} R) :
    baseChange (E := E) (E' := E) (h := rfl) S (id (F := F) E) =
      id (E.baseChange S) := by
  apply ext
  exact BasicAtlas.RationalHom.baseChange_id X S

/-- Full-order coefficient extension preserves actual rational formal composition. -/
@[simp]
theorem baseChange_comp (g : RationalHom F E' E'' k) (f : RationalHom F E E' h)
    (S : CommAlgCat.{v} R) :
    baseChange (E := E) (E' := E'') (h := h.trans k) S (g.comp f) =
      (baseChange (E := E') (E' := E'') (h := k) S g).comp
        (baseChange (E := E) (E' := E') (h := h) S f) := by
  apply ext
  exact BasicAtlas.RationalHom.baseChange_comp g.val f.val S

/-- Extension is a ring map for full-order rational endomorphism composition. -/
def baseChangeRingHom (E : OrderAction D X) (S : CommAlgCat.{v} R) :
    RationalHom F E E rfl →+* RationalHom F (E.baseChange S) (E.baseChange S) rfl where
  toFun := baseChange (E := E) (E' := E) (h := rfl) S
  map_zero' := (baseChange (E := E) (E' := E) (h := rfl) S).map_zero
  map_add' := (baseChange (E := E) (E' := E) (h := rfl) S).map_add
  map_one' := baseChange_id E S
  map_mul' := fun g f => baseChange_comp g f S

/-- The chart formula holds in the full-order rational coordinate centralizer. -/
theorem onChart_baseChange (f : RationalHom F E E' h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (baseChange (E := E) (E' := E') (h := h) S f).onChart A b hb =
      (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
        (E'.baseOrderChartIso S A b hb).inv).comp
          ((f.onChart (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb)).comp
            (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
              (E.baseSourceOrderChartIso S h A b hb).hom)) := by
  apply ModuleLaw.OrderAction.RationalHom.ext
  exact BasicAtlas.RationalHom.onChart_baseChange (X := X) (Y := Y) (h := h) f.val S A b hb

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Extend both full-order rational maps and retain the two actual inverse equations. -/
def baseChange (f : QuasiIsogeny F E E' h) (S : CommAlgCat.{v} R) :
    QuasiIsogeny F (E.baseChange S) (E'.baseChange S) (baseOpens_eq S h) where
  hom := RationalHom.baseChange (E := E) (E' := E') (h := h) S f.hom
  inv := RationalHom.baseChange (E := E') (E' := E) (h := h.symm) S f.inv
  inv_hom := by
    apply RationalHom.ext
    exact (f.toAtlasQuasiIsogeny.baseChange S).inv_hom
  hom_inv := by
    apply RationalHom.ext
    exact (f.toAtlasQuasiIsogeny.baseChange S).hom_inv

@[simp]
theorem baseChange_hom (f : QuasiIsogeny F E E' h) (S : CommAlgCat.{v} R) :
    (f.baseChange S).hom = RationalHom.baseChange (E := E) (E' := E') (h := h) S f.hom := rfl

@[simp]
theorem baseChange_inv (f : QuasiIsogeny F E E' h) (S : CommAlgCat.{v} R) :
    (f.baseChange S).inv =
      RationalHom.baseChange (E := E') (E' := E) (h := h.symm) S f.inv := rfl

/-- Forgetting the order recovers exactly the existing ambient coefficient extension. -/
@[simp]
theorem toAtlas_baseChange (f : QuasiIsogeny F E E' h) (S : CommAlgCat.{v} R) :
    (f.baseChange S).toAtlasQuasiIsogeny = f.toAtlasQuasiIsogeny.baseChange S := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  rfl

@[simp]
theorem baseChange_refl (E : OrderAction D X) (S : CommAlgCat.{v} R) :
    (refl (F := F) E).baseChange S = refl (E.baseChange S) := by
  apply ext_hom
  exact RationalHom.baseChange_id E S

@[simp]
theorem baseChange_symm (f : QuasiIsogeny F E E' h) (S : CommAlgCat.{v} R) :
    f.symm.baseChange S = (f.baseChange S).symm := by
  apply ext_hom
  rfl

@[simp]
theorem baseChange_trans (f : QuasiIsogeny F E E' h) (g : QuasiIsogeny F E' E'' k)
    (S : CommAlgCat.{v} R) :
    (f.trans g).baseChange S = (f.baseChange S).trans (g.baseChange S) := by
  apply ext_hom
  exact RationalHom.baseChange_comp g.hom f.hom S

@[simp]
theorem baseChange_ofIso (f : Iso E E' h) (S : CommAlgCat.{v} R) :
    (ofIso (F := F) f).baseChange S = ofIso (f.baseChange S) := by
  apply ext_hom
  exact RationalHom.baseChange_ofHom S f.hom

/-- Evaluation is conjugation by the actual full-order coefficient comparisons. -/
theorem onChart_baseChange (f : QuasiIsogeny F E E' h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (f.baseChange S).onChart A b hb =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (E.baseSourceOrderChartIso S h A b hb)).trans
        ((f.onChart (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb)).trans
          (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (E'.baseOrderChartIso S A b hb)).symm) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  exact (RationalHom.onChart_baseChange f.hom S A b hb).trans
    (ModuleLaw.OrderAction.RationalHom.comp_assoc _ _ _).symm

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
