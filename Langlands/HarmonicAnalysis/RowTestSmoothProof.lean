import Langlands.HarmonicAnalysis.RowTestSmoothStatement

/-! Open stabilizers of Schwartz–Bruhat row functions via compact support. -/

namespace Langlands.HarmonicAnalysis

universe uF

open Set
open scoped Topology

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ}

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem row_mul_inv (x : Fin n → F) (g : Langlands.GeneralLinear n F) :
    Matrix.vecMul (Matrix.vecMul x g.val) (g⁻¹).val = x := by
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one]

private def rowStabilizer (Φ : SchwartzBruhat (Fin n → F)) :
    Subgroup (Langlands.GeneralLinear n F) where
  carrier := {g | ∀ x, Φ (Matrix.vecMul x g.val) = Φ x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, hh, hg]
  inv_mem' := by
    intro g hg x
    have hx := hg (Matrix.vecMul x (g⁻¹).val)
    have hcancel := row_mul_inv x (g⁻¹)
    simp only [inv_inv] at hcancel
    rw [hcancel] at hx
    exact hx.symm

private theorem rowStabilizer_isOpen (Φ : SchwartzBruhat (Fin n → F)) :
    IsOpen (rowStabilizer Φ : Set (Langlands.GeneralLinear n F)) := by
  let O : Set (Langlands.GeneralLinear n F × (Fin n → F)) :=
    {p | Φ (Matrix.vecMul p.2 p.1.val) = Φ p.2}
  have hrow : Continuous (fun p : Langlands.GeneralLinear n F × (Fin n → F) =>
      Matrix.vecMul p.2 p.1.val) :=
    continuous_snd.matrix_vecMul (Units.continuous_val.comp continuous_fst)
  have hO : IsOpen O :=
    ((Φ.locallyConstant.comp_continuous hrow).prodMk
      (Φ.locallyConstant.comp_continuous continuous_snd)) {p : ℂ × ℂ | p.1 = p.2}
  have hsubset :
      ({1} : Set (Langlands.GeneralLinear n F)) ×ˢ tsupport (Φ : (Fin n → F) → ℂ) ⊆ O := by
    rintro ⟨g, x⟩ ⟨hg, _⟩
    rcases Set.mem_singleton_iff.mp hg with rfl
    simp [O]
  obtain ⟨U, V, hU, _, h1U, hsV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton Φ.hasCompactSupport hO hsubset
  have h1 : (1 : Langlands.GeneralLinear n F) ∈ U := h1U (by simp)
  have hinvU : IsOpen ((fun g : Langlands.GeneralLinear n F => g⁻¹) ⁻¹' U) :=
    hU.preimage continuous_inv
  apply (rowStabilizer Φ).isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset ((hU.inter hinvU).mem_nhds ⟨h1, by simpa using h1⟩)
  intro g hg
  change ∀ x, Φ (Matrix.vecMul x g.val) = Φ x
  intro x
  by_cases hx : x ∈ tsupport (Φ : (Fin n → F) → ℂ)
  · exact hUV (show (g, x) ∈ U ×ˢ V from ⟨hg.1, hsV hx⟩)
  · have hx0 : Φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    by_cases hy : Matrix.vecMul x g.val ∈ tsupport (Φ : (Fin n → F) → ℂ)
    · have hi := hUV (show (g⁻¹, Matrix.vecMul x g.val) ∈ U ×ˢ V from
        ⟨hg.2, hsV hy⟩)
      change Φ (Matrix.vecMul (Matrix.vecMul x g.val) (g⁻¹).val) =
        Φ (Matrix.vecMul x g.val) at hi
      rw [row_mul_inv] at hi
      exact hi.symm
    · exact (image_eq_zero_of_notMem_tsupport hy).trans hx0.symm

/-- Schwartz–Bruhat row functions have open stabilizers under right multiplication. -/
theorem rowTestSmooth (F : Type uF) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] (n : ℕ) : RowTestSmoothStatement F n := by
  intro Φ
  exact ⟨⟨rowStabilizer Φ, rowStabilizer_isOpen Φ⟩, fun _ hg => hg⟩

/-- The orbit map takes values in the set of row functions and is locally
constant, without any topology on that function space. -/
theorem rowTranslate_locallyConstant (Φ : SchwartzBruhat (Fin n → F)) :
    IsLocallyConstant (fun g : Langlands.GeneralLinear n F =>
      fun x : Fin n → F => Φ (Matrix.vecMul x g.val)) := by
  obtain ⟨U, hU⟩ := rowTestSmooth F n Φ
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (U : Set (Langlands.GeneralLinear n F)),
    U.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro h hh
    funext x
    have hx := hU (g⁻¹ * h) hh (Matrix.vecMul x g.val)
    simpa only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel_left] using hx

/-- Restriction of the row-translate orbit map to any compact set has finite
range. In particular, this applies to a compact open subgroup. -/
theorem finite_rowTranslate_range (Φ : SchwartzBruhat (Fin n → F))
    (K : Set (Langlands.GeneralLinear n F)) (hK : IsCompact K) :
    (Set.range (fun g : K => fun x : Fin n → F => Φ (Matrix.vecMul x g.val.val))).Finite := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact ((rowTranslate_locallyConstant Φ).comp_continuous continuous_subtype_val).range_finite

end Langlands.HarmonicAnalysis
