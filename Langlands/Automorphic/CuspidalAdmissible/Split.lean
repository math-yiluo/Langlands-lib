import Langlands.Automorphic.CuspidalAdmissible.CuspRealization

/-!
# Splitting the Siegel set over the band into a compact part and cusp regions

A point of a Siegel set over the determinant band, written `torInf x · q` with `q` in the fixed
compact frame `Q₁` and `x` in the chamber, either has all drops of `x` at most `T` — then `x` is
bounded and the point lies in a compact region — or has a drop larger than `T` at some block
position, i.e. lies in a cusp region.
-/

noncomputable section

universe uF

open MeasureTheory NumberField
open scoped Classical Topology ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.CuspidalL2
  Langlands.Automorphic.OperatorDeterminantSlice

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

/-- The compact region `{torInf x · q : |x_i| ≤ B, q ∈ Q₁}`. -/
def compactRegion (Q₁ : Set (AdelicGL F n)) (B : ℝ) : Set (AdelicGL F n) :=
  (fun p : (Fin n → ℝ) × AdelicGL F n => AdelicGL.ofInfinite F n (torInf F n p.1) * p.2) ''
    ((Set.univ.pi fun _ => Set.Icc (-B) B) ×ˢ Q₁)

theorem isCompact_compactRegion {Q₁ : Set (AdelicGL F n)} (hQ₁ : IsCompact Q₁) (B : ℝ) :
    IsCompact (compactRegion Q₁ B) :=
  ((isCompact_univ_pi fun _ => isCompact_Icc).prod hQ₁).image
    (((map_continuous (AdelicGL.ofInfinite F n)).comp
      ((continuous_torInf F n).comp continuous_fst)).mul continuous_snd)

theorem absDet_eq_determinantNorm (g : AdelicGL F n) :
    absDet F n g = ((AdelicBlockDeterminantCharacter.determinantNorm F n g : ℝ≥0ˣ) : ℝ≥0) :=
  rfl

/-- **The split.** -/
theorem exists_siegel_band_split {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))}
    {C : Set (Ideles F)} {c : ℝ} {Q₁ : Set (AdelicGL F n)} (hQ₁ : IsCompact Q₁) {K : ℝ}
    (hK : 0 ≤ K)
    (hform : ∀ h ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c,
      ∃ (x : Fin n → ℝ) (q : AdelicGL F n), q ∈ Q₁ ∧
        h = AdelicGL.ofInfinite F n (torInf F n x) * q ∧ Chamber K x) :
    ∃ R : ℝ, ∀ T : ℝ, 0 ≤ T → ∀ g : AdelicGL F n,
      g ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c → point F n g ∈ band F n →
        g ∈ compactRegion Q₁ (R + n * (n * (K + T))) ∨
          ∃ a : Fin n, 0 < a.val ∧ g ∈ cuspRegion ΩN C c Q₁ K a T := by
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ, ∀ q ∈ Q₁, |Real.log (absDet F n q)| ≤ L₁ :=
    (hQ₁.image (continuous_abs.comp ((continuous_absDet F n).log
      fun g => (absDet_pos F n g).ne'))).bddAbove.elim
      fun L hL => ⟨L, fun q hq => hL ⟨q, hq, rfl⟩⟩
  refine ⟨Real.log 2 + L₁, fun T hT g hg hband => ?_⟩
  obtain ⟨x, q, hq, rfl, hch⟩ := hform _ hg
  have hdet : 1 < absDet F n (AdelicGL.ofInfinite F n (torInf F n x) * q) ∧
      absDet F n (AdelicGL.ofInfinite F n (torInf F n x) * q) < 2 := by
    have := hband
    simp only [band, Set.mem_ofPred_eq, quotientDeterminantNorm_point] at this
    rw [absDet_eq_determinantNorm]
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have hR : |∑ i, x i| ≤ Real.log 2 + L₁ := by
    have h1 := abs_sum_le_of_absDet F n x q
    have hlog : |Real.log (absDet F n (AdelicGL.ofInfinite F n (torInf F n x) * q))| ≤
        Real.log 2 := by
      rw [abs_of_pos (Real.log_pos hdet.1)]
      exact Real.log_le_log (by linarith [hdet.1]) hdet.2.le
    linarith [hL₁ q hq]
  by_cases hall : ∀ a : Fin n, 0 < a.val → chamberDrop x a ≤ T
  · left
    have hdrop : ∀ i j : Fin n, i.val + 1 = j.val → x i - x j ≤ T := by
      intro i j hij
      rw [← chamberDrop_of_succ x i j hij]
      exact hall j (by omega)
    have hsub := sub_le_of_chamber hK hT x hch hdrop
    refine ⟨(x, q), ⟨fun i _ => ?_, hq⟩, rfl⟩
    exact abs_le.mp (abs_le_of_sub_le x hsub hR i)
  · right
    push Not at hall
    obtain ⟨a, ha, hTa⟩ := hall
    exact ⟨a, ha, hg, hband, x, q, hq, rfl, hch, hTa⟩

end Langlands.Automorphic.CuspidalAdmissible
