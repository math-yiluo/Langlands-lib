import Langlands.Geometry.FormalGroup.OrderActionCentralAtlas
import Langlands.Geometry.FormalGroup.AtlasOrderMorphism
import Langlands.Geometry.FormalGroup.AtlasHomModule
import Langlands.Geometry.FormalGroup.CentralScalarKernel

/-! # Integral order-linear atlas maps over changed central scalars -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Hom

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {G : OrderAction D Y} {H : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}
variable (hs : ∀ (b : X.opens) (a : C) (x : σ → Localization.Away b.val),
  (E.chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
    algebraMap C (Localization.Away b.val) a • x)
variable (ht : ∀ (b : Y.opens) (a : C) (x : τ → Localization.Away b.val),
  (G.chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
    algebraMap C (Localization.Away b.val) a • x)
variable (hu : ∀ (b : Z.opens) (a : C) (x : υ → Localization.Away b.val),
  (H.chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
    algebraMap C (Localization.Away b.val) a • x)

/-- The formal scalar endomorphism of an order atlas. -/
def scalarHom (E : OrderAction D X) (a : O) : Hom E E rfl :=
  ⟨a • BasicAtlas.Hom.id X, by
    intro A b hb x
    simp only [BasicAtlas.Hom.smul_hom, BasicAtlas.Hom.id, ModuleLaw.Hom.smul_comp,
      ModuleLaw.Hom.comp_smul, ModuleLaw.Hom.id_comp, ModuleLaw.Hom.comp_id]⟩

@[simp]
theorem scalarHom_onChart (E : OrderAction D X) (a : O) (B : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    (scalarHom E a).val.hom B b hb = ((X.chart b).map (coefficientLift (O := O) b.val B hb)).scalarHom a := rfl

/-- Keep the actual coordinates of each atlas map and use its order commutation for the new
central scalar law. -/
def centralScalars (f : Hom E G h) : Hom (E.centralAtlasOrder hs) (G.centralAtlasOrder ht) h :=
  ⟨{
    hom := fun B b hb => ⟨(f.val.hom B b hb).toHom, fun a =>
      congrArg ModuleLaw.Hom.toHom (f.commutes B b hb (algebraMap C D a))⟩
    natural := fun φ b ha hb => f.val.natural φ b ha hb
    transition := fun B b d hb hd => by
      have he := congrArg ModuleLaw.Hom.toHom (f.val.transition B b d hb hd)
      exact ModuleLaw.Hom.ext he },
    fun B b hb a => by
      have he := congrArg ModuleLaw.Hom.toHom (f.commutes B b hb a)
      exact ModuleLaw.Hom.ext he⟩

@[simp]
theorem centralScalars_coordinates (f : Hom E G h) (B : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    ((f.centralScalars hs ht).val.hom B b hb).toHom = (f.val.hom B b hb).toHom := rfl

@[simp]
theorem centralScalars_id : (id E).centralScalars hs hs = id (E.centralAtlasOrder hs) := by
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro B b hb
  apply ModuleLaw.Hom.ext
  rfl

/-- Changing central scalars respects composition of actual order atlas maps. -/
theorem centralScalars_comp (g : Hom G H k) (f : Hom E G h) :
    (g.comp f).centralScalars hs hu = (g.centralScalars ht hu).comp (f.centralScalars hs ht) := by
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro B b hb
  apply ModuleLaw.Hom.ext
  rfl

/-- The same natural number acts by the same formal scalar endomorphism. -/
theorem centralScalars_scalarNatCast (n : ℕ) :
    (scalarHom E (n : O)).centralScalars hs hs = scalarHom (E.centralAtlasOrder hs) (n : C) := by
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro B b hb
  apply ModuleLaw.Hom.ext
  let A₁ := (E.chart b).map (coefficientLift (O := O) b.val B hb)
  let A₂ := ((E.centralAtlasOrder hs).chart b).map (coefficientLift (O := C) b.val B hb)
  have hn₁ := A₁.action_algebraMap_eq_scalarHom (n : O)
  have hn₂ := A₂.action_algebraMap_eq_scalarHom (n : C)
  rw [map_natCast] at hn₁ hn₂
  have hn : (A₁.action (n : D)).toHom = (A₂.action (n : D)).toHom := rfl
  exact (congrArg ModuleLaw.Hom.toHom hn₁).symm.trans
    (hn.trans (congrArg ModuleLaw.Hom.toHom hn₂))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Hom
