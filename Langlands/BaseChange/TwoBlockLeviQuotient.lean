import Langlands.Analysis.Local.LeftQuotientProduct
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.Analysis.Local.QuotientTopology
import Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar

/-! Quotient coordinates for a subgroup of the two-block Levi. -/

noncomputable section

namespace Langlands.BaseChange

open Topology Langlands.GeneralLinear Langlands.QuotientIntegration
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg

universe u

variable {R : Type u} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "M" => BlockShape.Levi B R
local notation "G" => GeneralLinear (t + 1) R
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem parabolicPoint_left_levi (a L : M) (x : Rect) :
    parabolicPoint h (a * L, x) = (B).leviEmbedding R a * parabolicPoint h (L, x) := by
  simp only [parabolicPoint, map_mul, mul_assoc]

variable (A : Subgroup ((succBlockShape m h).Levi R))
variable (H : Subgroup (GeneralLinear (t + 1) R))
variable (e : A ≃ₜ* H)

variable (he : ∀ a : A, (e a).val = (succBlockShape m h).leviEmbedding R a.val)

/-- Map the Levi quotient and radical coordinates into the actual ambient left quotient. -/
def leviRadicalQuotientPoint (z : LeftQuotient A × Rect) : LeftQuotient H :=
  Quotient.lift (fun L : M => fun x : Rect => leftQuotientMap H (parabolicPoint h (L, x)))
    (by
      intro L L' hh
      have ha : L' * L⁻¹ ∈ A := QuotientGroup.rightRel_apply.mp hh
      let a : A := ⟨L' * L⁻¹, ha⟩
      have hL : L' = a.val * L := by
        change L' = L' * L⁻¹ * L
        simp
      funext x
      rw [hL, parabolicPoint_left_levi, ← he a, leftQuotientMap_subgroup_mul]) z.1 z.2

omit [IsTopologicalRing R] in
@[simp] theorem leviRadicalQuotientPoint_mk (L : M) (x : Rect) :
    leviRadicalQuotientPoint h A H e he (leftQuotientMap A L, x) =
      leftQuotientMap H (parabolicPoint h (L, x)) := rfl

theorem continuous_leviRadicalQuotientPoint :
    Continuous (leviRadicalQuotientPoint h A H e he) := by
  have hq := (leftQuotient_isOpenQuotientMap A).prodMap
    (IsOpenQuotientMap.id (X := Rect))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (leftQuotientMap H ∘ parabolicPoint h)
  exact continuous_quotient_mk'.comp (continuous_parabolicPoint h R)

variable [T2Space R] [LocallyCompactSpace (GeneralLinear (t + 1) R)]

/-- Restriction of a compact test function on the ambient left quotient to the
Levi quotient and radical coordinates still has compact support. -/
theorem hasCompactSupport_comp_leviRadicalQuotientPoint {V : Type*} [Zero V]
    (hH : IsClosed (H : Set G)) (hA : IsClosed (A : Set M))
    {f : LeftQuotient H → V} (hf : HasCompactSupport f) :
    HasCompactSupport (f ∘ leviRadicalQuotientPoint h A H e he) := by
  let : T2Space (LeftQuotient A) := leftQuotient_t2Space A hA
  obtain ⟨C, hC, hLift⟩ := leftQuotient_exists_isCompact_image H hH hf
  let Cₚ : Set ((B).parabolic R) := Subtype.val ⁻¹' C
  have hCₚ : IsCompact Cₚ := ((B).isClosed_parabolic R).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  let coords (g : (B).parabolic R) : LeftQuotient A × Rect :=
    (leftQuotientMap A (parabolicCoord h g).1, (parabolicCoord h g).2)
  have hCoords : Continuous coords :=
    ((leftQuotient_isOpenQuotientMap A).continuous.comp
      (continuous_fst.comp (continuous_parabolicCoord h R))).prodMk
      (continuous_snd.comp (continuous_parabolicCoord h R))
  have hK := hCₚ.image hCoords
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  rintro ⟨q, x⟩ hSupport
  induction q using Quotient.inductionOn with
  | h L =>
    let g := parabolicPoint h (L, x)
    have hq : leftQuotientMap H g ∈ tsupport f := subset_tsupport _ hSupport
    rw [← hLift] at hq
    obtain ⟨w, hw, hwq⟩ := hq
    have hCentral : w * g⁻¹ ∈ H := (leftQuotient_mk_eq_mk_iff H g w).mp hwq.symm
    let a := e.symm ⟨w * g⁻¹, hCentral⟩
    have hemb : (B).leviEmbedding R a.val = w * g⁻¹ := by
      rw [← he a, e.apply_symm_apply]
    have hp : parabolicPoint h (a.val * L, x) = w := by
      rw [parabolicPoint_left_levi, hemb]
      exact inv_mul_cancel_right w g
    have hwP : w ∈ (B).parabolic R := hp ▸ parabolicPoint_mem h (a.val * L, x)
    refine ⟨⟨w, hwP⟩, hw, ?_⟩
    have hSub : (⟨parabolicPoint h (a.val * L, x), parabolicPoint_mem h _⟩ :
        (B).parabolic R) = ⟨w, hwP⟩ := Subtype.ext hp
    have hCoord : parabolicCoord h (⟨w, hwP⟩ : (B).parabolic R) = (a.val * L, x) :=
      hSub ▸ parabolicCoord_parabolicPoint h (a.val * L, x)
    dsimp only [coords]
    simp only [hCoord, leftQuotientMap_subgroup_mul]
    rfl

end Langlands.BaseChange
