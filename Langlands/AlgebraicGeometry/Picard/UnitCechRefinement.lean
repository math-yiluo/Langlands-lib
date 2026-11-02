import Langlands.AlgebraicGeometry.Picard.UnitCechLineBundle
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleRefinement

/-! # Refinement of ordered actual-unit cocycles and their glued sheaves -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.UnitCechRefinement

open Langlands.Cohomology Cech UnitCechLineBundle

variable {X : Scheme.{u}} {ι κ : Type u} (U : ι → X.Opens) (V : κ → X.Opens)
  (β : κ → ι) (hβ : ∀ j, V j ≤ U (β j))

/-- Restricting ordered cochains restricts the corresponding actual transition units. -/
lemma pairUnits_refine (z : C (unitP (X := X)) U 1) :
    pairUnits V (refine (unitP (X := X)) U V β hβ 1 z) =
      CocycleGluing.refineCocycle (pairUnits U z) β hβ := by
  funext i j
  apply Units.ext
  rw [CocycleGluing.refineCocycle_val, res_pairUnits_val]
  change unitVal (res (Cech.inter_two (U := V) i j).ge
    (refine (unitP (X := X)) U V β hβ 1 z ![i, j])) = _
  rw [refine_apply, res_res]
  apply congrArg (unitVal (X := X))
  exact Cech.res_congr (unitP (X := X)) U
    (by funext k; fin_cases k <;> rfl) z _ _

/-- A full refinement preserves the actual sheaf glued from an ordered unit cocycle. -/
def refinementIso (hV : (⨆ j, V j) = ⊤) (z : C (unitP (X := X)) U 1)
    (hz : d (unitP (X := X)) U 1 z = 0) :
    CocycleGluing.glued (pairUnits U z) ≅
      CocycleGluing.glued (pairUnits V (refine (unitP (X := X)) U V β hβ 1 z)) := by
  rw [pairUnits_refine]
  exact CocycleGluing.refinementIso _ (isCocycle_pairUnits U hz) β hβ hV

/-- The product family of pairwise intersections is a common refinement. -/
def commonCover : ι × κ → X.Opens := fun p => U p.1 ⊓ V p.2

lemma commonCover_eq_top (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤) :
    (⨆ p, commonCover U V p) = ⊤ := by
  apply top_unique
  intro x _
  have hxU : x ∈ iSup U := by rw [hU]; trivial
  have hxV : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hxU
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hxV
  exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩

/-- Restriction from the first family to the product intersection cover. -/
def commonRefineLeft (p : ℕ) :
    C (unitP (X := X)) U p →+ C (unitP (X := X)) (commonCover U V) p :=
  refine (unitP (X := X)) U (commonCover U V) Prod.fst (fun _ => inf_le_left) p

/-- Restriction from the second family to the product intersection cover. -/
def commonRefineRight (p : ℕ) :
    C (unitP (X := X)) V p →+ C (unitP (X := X)) (commonCover U V) p :=
  refine (unitP (X := X)) V (commonCover U V) Prod.snd (fun _ => inf_le_right) p

/-- Glued sheaves from two full covers are isomorphic exactly when their cocycles
have a coboundary difference on their common product cover. -/
theorem nonempty_iso_glued_iff_commonCover
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤)
    {z : C (unitP (X := X)) U 1} {w : C (unitP (X := X)) V 1}
    (hz : d (unitP (X := X)) U 1 z = 0) (hw : d (unitP (X := X)) V 1 w = 0) :
    Nonempty (CocycleGluing.glued (pairUnits U z) ≅
      CocycleGluing.glued (pairUnits V w)) ↔
    ∃ a : C (unitP (X := X)) (commonCover U V) 0,
      d (unitP (X := X)) (commonCover U V) 0 a =
        commonRefineRight U V 1 w - commonRefineLeft U V 1 z := by
  have hW := commonCover_eq_top U V hU hV
  have hz' : d (unitP (X := X)) (commonCover U V) 1
      (commonRefineLeft U V 1 z) = 0 := by
    dsimp only [commonRefineLeft]
    rw [d_refine, hz, map_zero]
  have hw' : d (unitP (X := X)) (commonCover U V) 1
      (commonRefineRight U V 1 w) = 0 := by
    dsimp only [commonRefineRight]
    rw [d_refine, hw, map_zero]
  let eU := refinementIso U (commonCover U V) Prod.fst (fun _ => inf_le_left) hW z hz
  let eV := refinementIso V (commonCover U V) Prod.snd (fun _ => inf_le_right) hW w hw
  have h := nonempty_iso_glued_iff (commonCover U V) hz' hw'
  constructor
  · rintro ⟨e⟩
    exact h.1 ⟨eU.symm ≪≫ e ≪≫ eV⟩
  · intro ha
    obtain ⟨e⟩ := h.2 ha
    exact ⟨eU ≪≫ e ≪≫ eV.symm⟩

end Langlands.AlgebraicGeometry.Picard.UnitCechRefinement
