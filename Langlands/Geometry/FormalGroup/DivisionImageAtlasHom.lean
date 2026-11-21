import Langlands.Geometry.FormalGroup.DivisionImageOrderAtlas
import Langlands.Geometry.FormalGroup.IdempotentImageAtlasMap
import Langlands.Geometry.FormalGroup.AtlasOrderMorphism
import Langlands.Geometry.FormalGroup.AtlasHomModule

/-! # Order-linear maps of the actual division-image atlases -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ σ' τ' υ' : Type}
variable [Finite σ] [Finite τ] [Finite υ] [Finite σ'] [Finite τ'] [Finite υ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {E : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) M} {G : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) N}
variable {H : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) P}
variable (I : IdempotentImageCover E.divisionProjector σ')
variable (J : IdempotentImageCover G.divisionProjector τ')
variable {h : I.atlas.opens = J.atlas.opens}

/-- An integral map commuting with the split order restricts to a division-order map
of the actual image atlases. -/
def restrictDivisionHom (f : ModuleLaw.OrderAction.Hom E G) :
    BasicAtlas.OrderAction.Hom (I.divisionOrder E) (J.divisionOrder G) h :=
  ⟨I.restrictHom J f.val (f.commutes (0, 1)), by
    intro A b hb x
    let a := sourceChart (X := I.atlas) (Y := J.atlas) h b
    let φ := IsScalarTower.toAlgHom O R A
    let I₀ : (E.map (IsScalarTower.toAlgHom O R (Localization.Away a.val))).DivisionImage _ := (I.image a).2
    let J₀ : (G.map (IsScalarTower.toAlgHom O R (Localization.Away b.val))).DivisionImage _ := (J.image b).2
    let IA : (E.map φ).DivisionImage _ := I₀.overChartTest A hb
    let JA : (G.map φ).DivisionImage _ := J₀.overChartTest A hb
    let fA := f.map φ
    change (IA.restrictHom JA fA.val).comp ((I₀.order.map (coefficientLift (O := O) b.val A hb)).action x) =
      ((J₀.order.map (coefficientLift (O := O) b.val A hb)).action x).comp (IA.restrictHom JA fA.val)
    have hs := I₀.overChartTest_order_action A hb x
    have ht := J₀.overChartTest_order_action A hb x
    rw [hs, ht]
    change (IA.restrictHom JA fA.val).comp (IA.restrictHom IA ((E.map φ).action (0, x))) =
      (JA.restrictHom JA ((G.map φ).action (0, x))).comp (IA.restrictHom JA fA.val)
    have hx := ((E.map φ).action_comp_divisionProjector x).trans
      ((E.map φ).divisionProjector_comp_action x).symm
    rw [← IA.restrictHom_comp IA JA _ _ hx,
      ← IA.restrictHom_comp JA JA _ _ (fA.commutes (0, 1)), fA.commutes]⟩

@[simp]
theorem restrictDivisionHom_id : I.restrictDivisionHom I (h := rfl) (ModuleLaw.OrderAction.Hom.id E) =
    BasicAtlas.OrderAction.Hom.id (I.divisionOrder E) := by
  apply Subtype.ext
  exact I.restrictHom_id

/-- Order-linear restriction preserves composition on the actual atlases. -/
theorem restrictDivisionHom_comp (K : IdempotentImageCover H.divisionProjector υ')
    {k : J.atlas.opens = K.atlas.opens} (g : ModuleLaw.OrderAction.Hom G H)
    (f : ModuleLaw.OrderAction.Hom E G) :
    I.restrictDivisionHom K (h := h.trans k) (g.comp f) =
      (J.restrictDivisionHom K (h := k) g).comp (I.restrictDivisionHom J (h := h) f) := by
  apply Subtype.ext
  exact I.restrictHom_comp J f.val (f.commutes (0, 1)) K g.val (g.commutes (0, 1))

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover
