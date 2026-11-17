import Langlands.Geometry.FormalGroup.AtlasRationalHeight
import Langlands.Geometry.FormalGroup.RationalHeightIso
import Langlands.Geometry.FormalGroup.AtlasOrderQuasiIsogenyCalculus

/-! # Full-order atlas isomorphism transport of actual local rational heights -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {X' : BasicAtlas O R υ} {Y' : BasicAtlas O R ω}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {G : OrderAction D X'} {G' : OrderAction D Y'}
variable {h : X.opens = Y.opens} {aCover : X.opens = X'.opens}
variable {bCover : Y.opens = Y'.opens}

namespace RationalHom

/-- Change both actual atlas coordinates, retaining every acting order element. -/
def isoTransport (a : Iso E G aCover) (b : Iso E' G' bCover) :
    RationalHom F E E' h →ₗ[F]
      RationalHom F G G' ((aCover.symm.trans h).trans bCover) where
  toFun f := (ofHom b.hom).comp (f.comp (ofHom a.inv))
  map_add' f g := by rw [add_comp, comp_add]
  map_smul' c f := by rw [smul_comp, comp_smul]; rfl

/-- The coordinate change is composition with the specified rationalized formal maps. -/
@[simp]
theorem isoTransport_apply (a : Iso E G aCover) (b : Iso E' G' bCover)
    (f : RationalHom F E E' h) :
    isoTransport a b f = (ofHom b.hom).comp (f.comp (ofHom a.inv)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The same actual local kernel-rank height is retained on every transported test chart. -/
theorem isoTransport_height (a : Iso E G aCover) (b : Iso E' G' bCover)
    (f : RationalHom F E E' h) {π : O} {q : ℕ} {n : ℤ}
    (hf : f.val.HasConstantChartHeight π q n) :
    (isoTransport a b f).val.HasConstantChartHeight π q n := by
  intro A c hc
  let d := sourceChart bCover c
  let x := sourceChart aCover.symm (sourceChart h d)
  let a' := (a.onChart A x hc).toModuleIso
  let b' := (b.onChart A c hc).toModuleIso
  have hz := (hf A d hc).ofGlobal_isoTransport a' b'
  have he := ModuleLaw.RationalHom.isoTransport_eq_comp a' b'
    (BasicAtlas.RationalHom.onChart (X := X) (Y := Y) (h := h) A d hc f.val)
  have ht := (congrArg
    (fun z => RationalSection.HasHeightFunction π q (RationalSection.ofGlobal z) (fun _ => n))
    he).mp hz
  let a0 : BasicAtlas.RationalHom F X' X aCover.symm :=
    BasicAtlas.RationalHom.ofHom a.inv.val
  let b0 : BasicAtlas.RationalHom F Y Y' bCover :=
    BasicAtlas.RationalHom.ofHom b.hom.val
  change RationalSection.HasHeightFunction π q
    (RationalSection.ofGlobal
      (BasicAtlas.RationalHom.onChart (X := X') (Y := Y')
        (h := (aCover.symm.trans h).trans bCover) A c hc
        (BasicAtlas.RationalHom.comp b0 (BasicAtlas.RationalHom.comp f.val a0))))
    (fun _ => n)
  rw [BasicAtlas.RationalHom.onChart_comp b0 (BasicAtlas.RationalHom.comp f.val a0) A c hc,
    BasicAtlas.RationalHom.onChart_comp f.val a0 A (sourceChart bCover c) hc]
  simp only [a0, b0]
  exact ht

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Transport both actual rational maps and their inverse equations. -/
def isoTransport (f : QuasiIsogeny F E E' h)
    (a : Iso E G aCover) (b : Iso E' G' bCover) :
    QuasiIsogeny F G G' ((aCover.symm.trans h).trans bCover) :=
  ((ofIso a).symm.trans f).trans (ofIso b)

@[simp]
theorem isoTransport_hom (f : QuasiIsogeny F E E' h)
    (a : Iso E G aCover) (b : Iso E' G' bCover) :
    (f.isoTransport a b).hom = RationalHom.isoTransport a b f.hom := rfl

/-- Both transported rational maps still give the original signed local height for the forward map. -/
theorem isoTransport_height (f : QuasiIsogeny F E E' h)
    (a : Iso E G aCover) (b : Iso E' G' bCover)
    {π : O} {q : ℕ} {n : ℤ} (hf : f.hom.val.HasConstantChartHeight π q n) :
    (f.isoTransport a b).hom.val.HasConstantChartHeight π q n :=
  RationalHom.isoTransport_height a b f.hom hf

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
