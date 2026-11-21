import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Simultaneous equality as a closed subscheme -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} {X Y : Over S} [IsSeparated Y.hom]
  {J : Type v} (f g : J → (X ⟶ Y))

/-- The sum of the defining ideal sheaves of a family of closed equalizers. -/
def simultaneousEqualizerIdeal : X.left.IdealSheafData :=
  ⨆ j, (equalizer.ι (f j) (g j)).left.ker

/-- The closed subscheme on which every pair of maps in the family agrees. -/
def simultaneousEqualizer : Over S :=
  Over.mk ((simultaneousEqualizerIdeal f g).subschemeι ≫ X.hom)

/-- The simultaneous equalizer's inclusion in the original scheme. -/
def simultaneousEqualizerι : simultaneousEqualizer f g ⟶ X :=
  Over.homMk (simultaneousEqualizerIdeal f g).subschemeι rfl

instance : IsClosedImmersion (simultaneousEqualizerι f g).left :=
  inferInstanceAs (IsClosedImmersion (simultaneousEqualizerIdeal f g).subschemeι)

/-- Factorization through the closed simultaneous equalizer from equality of all composites. -/
def simultaneousEqualizerLift {T : Over S} (a : T ⟶ X)
    (h : ∀ j, a ≫ f j = a ≫ g j) : T ⟶ simultaneousEqualizer f g := by
  let i := simultaneousEqualizerι f g
  have hker : i.left.ker ≤ a.left.ker := by
    change (simultaneousEqualizerIdeal f g).subschemeι.ker ≤ a.left.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, simultaneousEqualizerIdeal]
    apply iSup_le
    intro j
    have hc : (equalizer.lift a (h j)).left ≫ (equalizer.ι (f j) (g j)).left = a.left := by
      rw [← Over.comp_left, equalizer.lift_ι]
    rw [← hc]
    exact Scheme.Hom.le_ker_comp _ _
  let q := IsClosedImmersion.lift i.left a.left hker
  have hq : q ≫ i.left = a.left := IsClosedImmersion.lift_fac _ _ _
  exact Over.homMk q (by change q ≫ i.left ≫ X.hom = _; rw [← Category.assoc, hq, Over.w a])

omit [IsSeparated Y.hom] in
@[reassoc (attr := simp)]
lemma simultaneousEqualizerLift_ι {T : Over S} (a : T ⟶ X)
    (h : ∀ j, a ≫ f j = a ≫ g j) :
    simultaneousEqualizerLift f g a h ≫ simultaneousEqualizerι f g = a := by
  ext1
  exact IsClosedImmersion.lift_fac _ _ _

@[reassoc]
lemma simultaneousEqualizer_condition (j : J) :
    simultaneousEqualizerι f g ≫ f j = simultaneousEqualizerι f g ≫ g j := by
  let e := equalizer.ι (f j) (g j)
  let i := simultaneousEqualizerι f g
  have hi : e.left.ker ≤ i.left.ker := by
    change _ ≤ (simultaneousEqualizerIdeal f g).subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact le_iSup (fun k ↦ (equalizer.ι (f k) (g k)).left.ker) j
  let q := IsClosedImmersion.lift e.left i.left hi
  have hq : q ≫ e.left = i.left := IsClosedImmersion.lift_fac _ _ _
  ext1
  have he : e.left ≫ (f j).left = e.left ≫ (g j).left :=
    congrArg (fun k : equalizer (f j) (g j) ⟶ Y ↦ k.left) (equalizer.condition (f j) (g j))
  change i.left ≫ (f j).left = i.left ≫ (g j).left
  rw [← hq, Category.assoc, he, ← Category.assoc]

/-- Testing equality of two maps to a separated target after a schematically dominant
map is sufficient; the source of the maps need not be reduced. -/
lemma overHom_ext_of_schematicallyDominant {W : Over S} {a b : X ⟶ Y} (j : W ⟶ X)
    [IsSchemeTheoreticallyDominant j.left] (h : j ≫ a = j ≫ b) : a = b := by
  let i := equalizer.ι a b
  have hfac : (equalizer.lift j h).left ≫ i.left = j.left := by
    rw [← Over.comp_left, equalizer.lift_ι]
  have hle := Scheme.Hom.le_ker_comp (equalizer.lift j h).left i.left
  rw [hfac, j.left.ker_eq_bot, le_bot_iff] at hle
  have : IsIso i.left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hle
  apply (Over.forget S).map_injective
  change a.left = b.left
  rw [← cancel_epi i.left]
  exact congrArg (fun k : equalizer a b ⟶ Y ↦ k.left) (equalizer.condition a b)

end Langlands.AlgebraicGeometry
