import Langlands.Geometry.FormalGroup.AtlasRationalMorphism
import Langlands.Geometry.FormalGroup.AtlasBaseChangeMorphism

/-! # Coefficient extension of actual rational formal atlas maps -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory TensorProduct

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type w} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom

/-- Coefficient extension of actual integral atlas maps is O-linear. -/
def baseChangeLinear (S : CommAlgCat.{v} R) :
    Hom X Y h →ₗ[O] Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h) where
  toFun f := f.baseChange S
  map_add' f g := by
    apply Hom.ext (X := X.baseChange S) (Y := Y.baseChange S) (h := baseOpens_eq S h)
    intro A b hb
    change (Y.baseChartIso S A b hb).inv.comp
      ((f.hom (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb) +
        g.hom (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb)).comp
        (baseSourceChartIso S h A b hb).hom) = _
    exact (congrArg (fun z => (Y.baseChartIso S A b hb).inv.comp z)
      (ModuleLaw.Hom.add_comp _ _ _)).trans (ModuleLaw.Hom.comp_add _ _ _)
  map_smul' a f := by
    apply Hom.ext (X := X.baseChange S) (Y := Y.baseChange S) (h := baseOpens_eq S h)
    intro A b hb
    change (Y.baseChartIso S A b hb).inv.comp
      ((a • f.hom (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb)).comp
        (baseSourceChartIso S h A b hb).hom) = _
    exact (congrArg (fun z => (Y.baseChartIso S A b hb).inv.comp z)
      (ModuleLaw.Hom.smul_comp _ _ _)).trans (ModuleLaw.Hom.comp_smul _ _ _)

@[simp]
theorem baseChangeLinear_apply (S : CommAlgCat.{v} R) (f : Hom X Y h) :
    baseChangeLinear (X := X) (Y := Y) (h := h) S f = f.baseChange S := rfl

end Hom

namespace RationalHom

/-- Extend the actual integral coefficient-extension map by rational scalars. -/
def baseChange (S : CommAlgCat.{v} R) :
    RationalHom F X Y h →ₗ[F]
      RationalHom F (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h) :=
  (Hom.baseChangeLinear (X := X) (Y := Y) (h := h) S).baseChange F

@[simp]
theorem baseChange_tmul (S : CommAlgCat.{v} R) (a : F) (f : Hom X Y h) :
    baseChange (X := X) (Y := Y) (h := h) S (a ⊗ₜ[O] f) =
      (a ⊗ₜ[O] f.baseChange S :
        RationalHom F (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h)) :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
theorem baseChange_ofHom (S : CommAlgCat.{v} R) (f : Hom X Y h) :
    baseChange (X := X) (Y := Y) (h := h) S (ofHom (F := F) f) =
      ofHom (F := F) (f.baseChange S) :=
  baseChange_tmul S (1 : F) f

/-- Coefficient extension preserves the actual rational formal identity. -/
@[simp]
theorem baseChange_id (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R) :
    baseChange (X := X) (Y := X) (h := rfl) S (id (F := F) X) =
      id (X.baseChange S) := by
  rw [id, baseChange_ofHom, Hom.baseChange_id]
  rfl

/-- Coefficient extension preserves composition of actual rational formal maps. -/
@[simp]
theorem baseChange_comp (g : RationalHom F Y Z k) (f : RationalHom F X Y h)
    (S : CommAlgCat.{v} R) :
    baseChange (X := X) (Y := Z) (h := h.trans k) S (comp g f) =
      comp (baseChange (X := Y) (Y := Z) (h := k) S g)
        (baseChange (X := X) (Y := Y) (h := h) S f) := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ =>
    simp only [add_comp, _root_.map_add, hg₁, hg₂]
  | tmul a g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ =>
      simp only [comp_add, _root_.map_add, hf₁, hf₂]
    | tmul b f =>
      simp only [comp_tmul, baseChange_tmul, Hom.baseChange_comp]

/-- Coefficient extension respects the rational endomorphism composition ring. -/
def baseChangeRingHom (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R) :
    RationalHom F X X rfl →+* RationalHom F (X.baseChange S) (X.baseChange S) rfl where
  toFun := baseChange (X := X) (Y := X) (h := rfl) S
  map_zero' := (baseChange (X := X) (Y := X) (h := rfl) S).map_zero
  map_add' := (baseChange (X := X) (Y := X) (h := rfl) S).map_add
  map_one' := baseChange_id X S
  map_mul' := fun g f => baseChange_comp g f S

/-- The extended chart map is the original test-chart map through actual comparisons. -/
theorem onChart_baseChange (f : RationalHom F X Y h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    onChart (X := X.baseChange S) (Y := Y.baseChange S) (h := baseOpens_eq S h) A b hb
      (baseChange (X := X) (Y := Y) (h := h) S f) =
      ModuleLaw.RationalHom.comp
        (ModuleLaw.RationalHom.ofHom (Y.baseChartIso S A b hb).inv)
        (ModuleLaw.RationalHom.comp
          (onChart (X := X) (Y := Y) (h := h) (restrictTest S A)
            (Y.baseSource S b) (Y.baseSource_unit S A b hb) f)
          (ModuleLaw.RationalHom.ofHom (baseSourceChartIso S h A b hb).hom)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add]
    exact (congrArg₂ (fun x y => x + y) hf hg).trans
      ((congrArg
        (fun z => ModuleLaw.RationalHom.comp
          (ModuleLaw.RationalHom.ofHom (Y.baseChartIso S A b hb).inv) z)
        (ModuleLaw.RationalHom.add_comp _ _ _)).trans
          (ModuleLaw.RationalHom.comp_add _ _ _)).symm
  | tmul a f =>
    change a ⊗ₜ[O] (f.baseChange S).hom A b hb =
      ModuleLaw.RationalHom.comp
        (1 ⊗ₜ[O] (Y.baseChartIso S A b hb).inv)
        (ModuleLaw.RationalHom.comp
          (a ⊗ₜ[O] f.hom (restrictTest S A) (Y.baseSource S b)
            (Y.baseSource_unit S A b hb))
          (1 ⊗ₜ[O] (baseSourceChartIso S h A b hb).hom))
    change a ⊗ₜ[O] (f.baseChange S).hom A b hb =
      (1 * (a * 1)) ⊗ₜ[O] _
    exact congrArg (fun z : F => z ⊗ₜ[O] (f.baseChange S).hom A b hb)
      (by rw [mul_one, one_mul])

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Extend both rational maps and transport their actual formal inverse equations. -/
def baseChange (f : QuasiIsogeny F X Y h) (S : CommAlgCat.{v} R) :
    QuasiIsogeny F (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h) where
  hom := RationalHom.baseChange (X := X) (Y := Y) (h := h) S f.hom
  inv := RationalHom.baseChange (X := Y) (Y := X) (h := h.symm) S f.inv
  inv_hom := by
    rw [← RationalHom.baseChange_comp, f.inv_hom, RationalHom.baseChange_id]
  hom_inv := by
    rw [← RationalHom.baseChange_comp, f.hom_inv, RationalHom.baseChange_id]

@[simp]
theorem baseChange_hom (f : QuasiIsogeny F X Y h) (S : CommAlgCat.{v} R) :
    (f.baseChange S).hom = RationalHom.baseChange (X := X) (Y := Y) (h := h) S f.hom := rfl

@[simp]
theorem baseChange_inv (f : QuasiIsogeny F X Y h) (S : CommAlgCat.{v} R) :
    (f.baseChange S).inv =
      RationalHom.baseChange (X := Y) (Y := X) (h := h.symm) S f.inv := rfl

@[simp]
theorem baseChange_refl (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R) :
    (refl (F := F) X).baseChange S = refl (X.baseChange S) := by
  apply ext_hom
  exact RationalHom.baseChange_id X S

@[simp]
theorem baseChange_symm (f : QuasiIsogeny F X Y h) (S : CommAlgCat.{v} R) :
    f.symm.baseChange S = (f.baseChange S).symm := by
  apply ext_hom
  rfl

@[simp]
theorem baseChange_trans (f : QuasiIsogeny F X Y h) (g : QuasiIsogeny F Y Z k)
    (S : CommAlgCat.{v} R) :
    (f.trans g).baseChange S = (f.baseChange S).trans (g.baseChange S) := by
  apply ext_hom
  exact RationalHom.baseChange_comp g.hom f.hom S

@[simp]
theorem baseChange_ofIso (f : Iso X Y h) (S : CommAlgCat.{v} R) :
    (ofIso (F := F) f).baseChange S = ofIso (f.baseChange S) := by
  apply ext_hom
  exact RationalHom.baseChange_ofHom S f.hom

/-- Evaluation is coefficient extension through the actual source and target comparisons. -/
theorem onChart_baseChange (f : QuasiIsogeny F X Y h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (f.baseChange S).onChart A b hb =
      (ModuleLaw.QuasiIsogeny.ofIso (baseSourceChartIso S h A b hb)).trans
        ((f.onChart (restrictTest S A) (Y.baseSource S b) (Y.baseSource_unit S A b hb)).trans
          (ModuleLaw.QuasiIsogeny.ofIso (Y.baseChartIso S A b hb).symm)) := by
  apply ModuleLaw.QuasiIsogeny.ext_hom
  exact (RationalHom.onChart_baseChange f.hom S A b hb).trans
    (ModuleLaw.RationalHom.comp_assoc _ _ _).symm

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
