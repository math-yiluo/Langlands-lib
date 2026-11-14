import Langlands.Geometry.FormalGroup.AtlasRationalMorphism
import Langlands.Geometry.FormalGroup.AtlasRefinementMorphism

/-! # Restriction of rational formal atlas maps to finer covers -/

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

/-- The two restricted atlases use the same finer cover. -/
theorem CoverRefinement.opens_eq_retarget (q : CoverRefinement X) :
    q.atlas.opens = (q.retarget Y h).atlas.opens := rfl

namespace Hom

/-- Restriction of actual formal atlas maps is linear over O. -/
def restrictLinear (q : CoverRefinement X) :
    Hom X Y h →ₗ[O] Hom q.atlas (q.retarget Y h).atlas
      (q.opens_eq_retarget (Y := Y) (h := h)) where
  toFun f := f.restrict q
  map_add' f g := by
    apply Hom.ext (X := q.atlas) (Y := (q.retarget Y h).atlas)
      (h := q.opens_eq_retarget (Y := Y) (h := h))
    intro A b hb
    change q.opens at b
    change ((q.retarget Y h).chartIso A b hb).inv.comp
      ((f.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb) +
        g.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).comp
        (q.chartIso A b hb).hom) = _
    exact (congrArg (fun z => ((q.retarget Y h).chartIso A b hb).inv.comp z)
      (ModuleLaw.Hom.add_comp _ _ _)).trans (ModuleLaw.Hom.comp_add _ _ _)
  map_smul' a f := by
    apply Hom.ext (X := q.atlas) (Y := (q.retarget Y h).atlas)
      (h := q.opens_eq_retarget (Y := Y) (h := h))
    intro A b hb
    change q.opens at b
    change ((q.retarget Y h).chartIso A b hb).inv.comp
      ((a • f.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).comp
        (q.chartIso A b hb).hom) = _
    exact (congrArg (fun z => ((q.retarget Y h).chartIso A b hb).inv.comp z)
      (ModuleLaw.Hom.smul_comp _ _ _)).trans (ModuleLaw.Hom.comp_smul _ _ _)

@[simp]
theorem restrictLinear_apply (q : CoverRefinement X) (f : Hom X Y h) :
    restrictLinear (Y := Y) (h := h) q f = f.restrict q := rfl

end Hom

namespace RationalHom

/-- Extend the actual integral restriction map by F-scalars. -/
def restrict (q : CoverRefinement X) :
    RationalHom F X Y h →ₗ[F] RationalHom F q.atlas (q.retarget Y h).atlas
      (q.opens_eq_retarget (Y := Y) (h := h)) :=
  (Hom.restrictLinear (Y := Y) (h := h) q).baseChange F

@[simp]
theorem restrict_tmul (q : CoverRefinement X) (a : F) (f : Hom X Y h) :
    restrict (Y := Y) (h := h) q (a ⊗ₜ[O] f) =
      (a ⊗ₜ[O] f.restrict q :
        RationalHom F q.atlas (q.retarget Y h).atlas
          (q.opens_eq_retarget (Y := Y) (h := h))) :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
theorem restrict_ofHom (q : CoverRefinement X) (f : Hom X Y h) :
    restrict (Y := Y) (h := h) q (ofHom (F := F) f) =
      ofHom (F := F) (X := q.atlas) (Y := (q.retarget Y h).atlas)
        (h := q.opens_eq_retarget (Y := Y) (h := h))
        (f.restrict q) :=
  restrict_tmul q (1 : F) f

/-- Restriction preserves the actual rational identity. -/
@[simp]
theorem restrict_id (q : CoverRefinement X) :
    restrict (Y := X) (h := rfl) q (id (F := F) X) = id q.atlas := by
  rw [id, restrict_ofHom, Hom.restrict_id]
  rfl

/-- Restriction preserves composition, with the same target refinement as integrally. -/
@[simp]
theorem restrict_comp (g : RationalHom F Y Z k) (f : RationalHom F X Y h)
    (q : CoverRefinement X) :
    restrict (Y := Z) (h := h.trans k) q (comp g f) =
      comp (restrict (Y := Z) (h := k) (q.retarget Y h) g)
        (restrict (Y := Y) (h := h) q f) := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ =>
    simp only [add_comp, _root_.map_add, hg₁, hg₂]
    rfl
  | tmul a g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ =>
      simp only [comp_add, _root_.map_add, hf₁, hf₂]
      rfl
    | tmul b f =>
      simp only [comp_tmul, restrict_tmul, Hom.restrict_comp]
      rfl

/-- Refinement of endomorphisms respects the composition ring. -/
def restrictRingHom (q : CoverRefinement X) :
    RationalHom F X X rfl →+* RationalHom F q.atlas q.atlas rfl where
  toFun := restrict (Y := X) (h := rfl) q
  map_zero' := (restrict (Y := X) (h := rfl) q).map_zero
  map_add' := (restrict (Y := X) (h := rfl) q).map_add
  map_one' := restrict_id q
  map_mul' := fun g f => restrict_comp g f q

/-- On charts, restriction is conjugation by the actual coefficient comparisons. -/
theorem onChart_restrict (f : RationalHom F X Y h) (q : CoverRefinement X)
    (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    onChart (X := q.atlas) (Y := (q.retarget Y h).atlas)
      (h := q.opens_eq_retarget (Y := Y) (h := h)) A b hb
        (restrict (Y := Y) (h := h) q f) =
      ModuleLaw.RationalHom.comp
        (ModuleLaw.RationalHom.ofHom ((q.retarget Y h).chartIso A b hb).inv)
        (ModuleLaw.RationalHom.comp
          (onChart (X := X) (h := h) A
            (sourceChart h.symm (q.source b)) (q.source_unit A b hb) f)
          (ModuleLaw.RationalHom.ofHom (q.chartIso A b hb).hom)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add]
    exact (congrArg₂ (fun x y => x + y) hf hg).trans
      ((congrArg
        (fun z => ModuleLaw.RationalHom.comp
          (ModuleLaw.RationalHom.ofHom ((q.retarget Y h).chartIso A b hb).inv) z)
        (ModuleLaw.RationalHom.add_comp _ _ _)).trans
          (ModuleLaw.RationalHom.comp_add _ _ _)).symm
  | tmul a f =>
    change a ⊗ₜ[O] ((f.restrict q).hom A b hb) =
      ModuleLaw.RationalHom.comp
        (1 ⊗ₜ[O] ((q.retarget Y h).chartIso A b hb).inv)
        (ModuleLaw.RationalHom.comp
          (a ⊗ₜ[O] f.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb))
          (1 ⊗ₜ[O] (q.chartIso A b hb).hom))
    change a ⊗ₜ[O] ((f.restrict q).hom A b hb) =
      (1 * (a * 1)) ⊗ₜ[O] _
    exact congrArg (fun z : F => z ⊗ₜ[O] (f.restrict q).hom A b hb)
      (by rw [mul_one, one_mul])

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Restrict both actual rational maps and transport their formal inverse equations. -/
def restrict (f : QuasiIsogeny F X Y h) (q : CoverRefinement X) :
    QuasiIsogeny F q.atlas (q.retarget Y h).atlas
      (q.opens_eq_retarget (Y := Y) (h := h)) where
  hom := RationalHom.restrict (Y := Y) (h := h) q f.hom
  inv := RationalHom.restrict (Y := X) (h := h.symm) (q.retarget Y h) f.inv
  inv_hom := by
    exact (RationalHom.restrict_comp f.inv f.hom q).symm.trans
      ((congrArg (RationalHom.restrict (F := F) (Y := X) (h := h.trans h.symm) q)
        f.inv_hom).trans (RationalHom.restrict_id q))
  hom_inv := by
    exact (RationalHom.restrict_comp f.hom f.inv (q.retarget Y h)).symm.trans
      ((congrArg (RationalHom.restrict (F := F) (Y := Y) (h := h.symm.trans h)
        (q.retarget Y h)) f.hom_inv).trans
          (RationalHom.restrict_id (q.retarget Y h)))

@[simp]
theorem restrict_hom (f : QuasiIsogeny F X Y h) (q : CoverRefinement X) :
    (f.restrict q).hom = RationalHom.restrict (Y := Y) (h := h) q f.hom := rfl

@[simp]
theorem restrict_inv (f : QuasiIsogeny F X Y h) (q : CoverRefinement X) :
    (f.restrict q).inv =
      RationalHom.restrict (Y := X) (h := h.symm) (q.retarget Y h) f.inv := rfl

@[simp]
theorem restrict_refl (q : CoverRefinement X) :
    (refl (F := F) X).restrict q = refl q.atlas := by
  apply ext_hom (F := F)
  exact RationalHom.restrict_id q

@[simp]
theorem restrict_symm (f : QuasiIsogeny F X Y h) (q : CoverRefinement X) :
    f.symm.restrict (q.retarget Y h) = (f.restrict q).symm := by
  apply ext_hom (F := F)
  rfl

@[simp]
theorem restrict_trans (f : QuasiIsogeny F X Y h) (g : QuasiIsogeny F Y Z k)
    (q : CoverRefinement X) :
    (f.trans g).restrict q =
      (f.restrict q).trans (g.restrict (q.retarget Y h)) := by
  apply ext_hom (F := F)
  exact RationalHom.restrict_comp g.hom f.hom q

@[simp]
theorem restrict_ofIso (f : Iso X Y h) (q : CoverRefinement X) :
    (ofIso (F := F) f).restrict q = ofIso (f.restrict q) := by
  apply ext_hom (F := F)
  exact RationalHom.restrict_ofHom q f.hom

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
