import Langlands.Representation.Archimedean.RealLeviBorel

/-!
# The Haar measure of a block orthogonal subgroup of `O(N)`

Tools for the proof of `RealLeviParabolicIntegrationStatement`.

For a block function `cl : Fin N → ι` (positions `p, q` lie in the same block iff
`cl p = cl q`), `Kc cl` is the closed subgroup of `O(N)` of orthogonal matrices without entries
between different blocks, and `μc cl` is its normalized Haar measure. If the first `a` positions
form a block (`cl` is constant `c₀` on them and `> c₀` on the remaining `M` positions), then
`(k₁, k₂) ↦ diag(k₁, k₂)` is a continuous surjective homomorphism `O(a) × Kc (clR cl) → Kc cl`,
so that `μc cl` is the image of `haarK a ⊗ μc (clR cl)` (uniqueness of Haar probability
measures) and `∫_{Kc cl} f = ∫_{O(a)} ∫_{Kc (clR cl)} f(diag(k₁, k₂)) dk₂ dk₁`
(`integral_Kc_eq`).
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviBlockHaar

open GramFormula MaximalParabolicIntegration RealLeviChartGram RealLeviChartIntegrable
  RealLeviTwoBlock RealPrincipalSeriesDuality Langlands.GeneralLinear

attribute [local instance] measurableSpaceK

local instance borelSpaceK_bh (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-- `GL_n(ℝ)` is second countable (it carries the topology induced from `M_n(ℝ) × M_n(ℝ)ᵐᵒᵖ`). -/
theorem secondCountableTopology_GL (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℝ) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ :=
    TopologicalSpace.secondCountableTopology_induced _ (Matrix (Fin n) (Fin n) ℝ) MulOpposite.unop
  exact TopologicalSpace.secondCountableTopology_induced _ _
    (Units.embedProduct (Matrix (Fin n) (Fin n) ℝ))

attribute [local instance] secondCountableTopology_GL

/-- `O(n)` is second countable. -/
theorem secondCountableTopology_O (n : ℕ) : SecondCountableTopology (unitaryCompact ℝ n) :=
  TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

attribute [local instance] secondCountableTopology_O

variable {ι : Type*} [LinearOrder ι]

/-! ## The block orthogonal subgroup -/

section Group

variable {N : ℕ} (cl : Fin N → ι)

/-- The orthogonal matrices without entries between different blocks of `cl`. -/
def Kc : Subgroup (Langlands.GeneralLinear N ℝ) where
  carrier := {g | g ∈ unitaryCompact ℝ N ∧
    ∀ p q, cl p ≠ cl q → (g : Matrix (Fin N) (Fin N) ℝ) p q = 0}
  mul_mem' {g h} hg hh := by
    refine ⟨mul_mem hg.1 hh.1, fun p q hpq => ?_⟩
    simp only [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : cl p = cl r
    · rw [hh.2 r q (fun h' => hpq (hr.trans h')), mul_zero]
    · rw [hg.2 p r hr, zero_mul]
  one_mem' := ⟨one_mem _, fun p q hpq => by
    simp only [Units.val_one]
    exact Matrix.one_apply_ne fun h => hpq (h ▸ rfl)⟩
  inv_mem' {g} hg := by
    refine ⟨inv_mem hg.1, fun p q hpq => ?_⟩
    have hinv : ((g⁻¹ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) =
        (g : Matrix (Fin N) (Fin N) ℝ)ᵀ :=
      Units.inv_eq_of_mul_eq_one_right (mul_transpose_eq_one_of_mem hg.1)
    change ((g⁻¹ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) p q = 0
    rw [hinv, Matrix.transpose_apply]
    exact hg.2 q p (Ne.symm hpq)

theorem mem_unitaryCompact_of_mem_Kc {g : Langlands.GeneralLinear N ℝ} (hg : g ∈ Kc cl) :
    g ∈ unitaryCompact ℝ N := hg.1

theorem isClosed_Kc : IsClosed (Kc cl : Set (Langlands.GeneralLinear N ℝ)) := by
  have h1 : IsClosed (unitaryCompact ℝ N : Set (Langlands.GeneralLinear N ℝ)) :=
    (isCompact_iff_compactSpace.mpr
      (inferInstanceAs (CompactSpace (unitaryCompact ℝ N)))).isClosed
  have h2 : IsClosed {g : Langlands.GeneralLinear N ℝ |
      ∀ p q, cl p ≠ cl q → (g : Matrix (Fin N) (Fin N) ℝ) p q = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ =>
      isClosed_eq (Units.continuous_val.matrix_elem p q) continuous_const
  exact h1.inter h2

theorem isCompact_Kc : IsCompact (Kc cl : Set (Langlands.GeneralLinear N ℝ)) :=
  (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (unitaryCompact ℝ N))) :
    IsCompact (unitaryCompact ℝ N : Set (Langlands.GeneralLinear N ℝ))).of_isClosed_subset
    (isClosed_Kc cl) fun _ hg => hg.1

instance compactSpace_Kc : CompactSpace (Kc cl) :=
  isCompact_iff_compactSpace.mp (isCompact_Kc cl)

instance measurableSpace_Kc : MeasurableSpace (Kc cl) := borel _

instance borelSpace_Kc : BorelSpace (Kc cl) := ⟨rfl⟩

instance secondCountableTopology_Kc : SecondCountableTopology (Kc cl) :=
  TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

/-- The normalized Haar measure on `Kc cl`. -/
def μc : Measure (Kc cl) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance isHaarMeasure_μc : (μc cl).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance isProbabilityMeasure_μc : IsProbabilityMeasure (μc cl) :=
  ⟨Measure.haarMeasure_self⟩

/-- **Uniqueness.** A Haar probability measure on `Kc cl` is `μc cl`. -/
theorem eq_μc (ν : Measure (Kc cl)) [ν.IsHaarMeasure] [IsProbabilityMeasure ν] :
    ν = μc cl :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν (μc cl)

end Group

/-! ## Continuity of the block embedding -/

section Continuity

variable {a M : ℕ}

theorem continuous_dg :
    Continuous fun p : Matrix (Fin a) (Fin a) ℝ × Matrix (Fin M) (Fin M) ℝ => dg p.1 p.2 := by
  have h : (fun p : Matrix (Fin a) (Fin a) ℝ × Matrix (Fin M) (Fin M) ℝ => dg p.1 p.2) =
      fun p => dgLinL (M := M) p.1 + dgLinR (a := a) p.2 := by
    funext p
    change dg p.1 p.2 = dg p.1 0 + dg 0 p.2
    rw [← dg_add, add_zero, zero_add]
  rw [h]
  exact ((LinearMap.continuous_of_finiteDimensional _).comp continuous_fst).add
    ((LinearMap.continuous_of_finiteDimensional _).comp continuous_snd)

theorem continuous_dgGL :
    Continuous (dgGL : Langlands.GeneralLinear a ℝ × Langlands.GeneralLinear M ℝ → _) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_dg.comp ((Units.continuous_val.comp continuous_fst).prodMk
      (Units.continuous_val.comp continuous_snd))
  · have h : (fun p : Langlands.GeneralLinear a ℝ × Langlands.GeneralLinear M ℝ =>
        (((dgGL p)⁻¹ : Langlands.GeneralLinear (a + M) ℝ) : Matrix (Fin (a + M)) (Fin (a + M)) ℝ)) =
        fun p => dg ((p.1⁻¹ : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ)
          ((p.2⁻¹ : Langlands.GeneralLinear M ℝ) : Matrix (Fin M) (Fin M) ℝ) := by
      funext p
      rw [← map_inv, dgGL_val, Prod.fst_inv, Prod.snd_inv]
    rw [h]
    exact continuous_dg.comp ((Units.continuous_coe_inv.comp continuous_fst).prodMk
      (Units.continuous_coe_inv.comp continuous_snd))

end Continuity

/-! ## The first-block decomposition -/

section Peel

variable {a M : ℕ} {cl : Fin (a + M) → ι} {c0 : ι}
  (h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = c0)

include h1 in
theorem dgGL_mem_Kc {k₁ : Langlands.GeneralLinear a ℝ} (hk₁ : k₁ ∈ unitaryCompact ℝ a)
    {k₂ : Langlands.GeneralLinear M ℝ} (hk₂ : k₂ ∈ Kc (clR cl)) : dgGL (k₁, k₂) ∈ Kc cl := by
  refine ⟨dgGL_mem_unitaryCompact hk₁ hk₂.1, fun p q hpq => ?_⟩
  rw [dgGL_val]
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j => exact absurd ((h1 i).trans (h1 j).symm) hpq
    | right s => simp
  | right r =>
    induction q using Fin.addCases with
    | left j => simp
    | right s =>
      rw [dg_natAdd_natAdd]
      exact hk₂.2 r s hpq

/-- `(k₁, k₂) ↦ diag(k₁, k₂)` from `O(a) × Kc (clR cl)` to `Kc cl`. -/
def dgK : unitaryCompact ℝ a × Kc (clR cl) →* Kc cl :=
  (dgGL.comp ((unitaryCompact ℝ a).subtype.prodMap (Kc (clR cl)).subtype)).codRestrict (Kc cl)
    fun p => dgGL_mem_Kc h1 p.1.2 p.2.2

theorem dgK_val (p : unitaryCompact ℝ a × Kc (clR cl)) :
    ((dgK h1 p : Kc cl) : Langlands.GeneralLinear (a + M) ℝ) =
      dgGL ((p.1 : Langlands.GeneralLinear a ℝ), (p.2 : Langlands.GeneralLinear M ℝ)) :=
  rfl

theorem continuous_dgK : Continuous (dgK h1) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_dgGL.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

variable (h2 : ∀ r : Fin M, c0 < cl (Fin.natAdd a r))

include h2 in
theorem surjective_dgK : Function.Surjective (dgK h1) := by
  rintro ⟨k, hk⟩
  set K := (k : Matrix (Fin (a + M)) (Fin (a + M)) ℝ) with hKdef
  let A : Matrix (Fin a) (Fin a) ℝ := Matrix.of fun i j => K (Fin.castAdd M i) (Fin.castAdd M j)
  let B : Matrix (Fin M) (Fin M) ℝ := Matrix.of fun r s => K (Fin.natAdd a r) (Fin.natAdd a s)
  have hne : ∀ (i : Fin a) (r : Fin M), cl (Fin.castAdd M i) ≠ cl (Fin.natAdd a r) :=
    fun i r => by rw [h1]; exact (h2 r).ne
  have hK : dg A B = K := by
    ext p q
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left j => simp [A]
      | right s => rw [dg_castAdd_natAdd]; exact (hk.2 _ _ (hne i s)).symm
    | right r =>
      induction q using Fin.addCases with
      | left j => rw [dg_natAdd_castAdd]; exact (hk.2 _ _ (hne j r).symm).symm
      | right s => simp [B]
  have hKK : K * Kᵀ = 1 := mul_transpose_eq_one_of_mem hk.1
  have hAB : dg (A * Aᵀ) (B * Bᵀ) = dg 1 1 := by
    rw [← dg_mul_transpose, hK, hKK, dg_one]
  have hA : A * Aᵀ = 1 := by
    ext i j
    have := congrFun (congrFun hAB (Fin.castAdd M i)) (Fin.castAdd M j)
    simpa only [dg_castAdd_castAdd] using this
  have hB : B * Bᵀ = 1 := by
    ext r s
    have := congrFun (congrFun hAB (Fin.natAdd a r)) (Fin.natAdd a s)
    simpa only [dg_natAdd_natAdd] using this
  let kA : Langlands.GeneralLinear a ℝ := ⟨A, Aᵀ, hA, mul_eq_one_comm.mp hA⟩
  let kB : Langlands.GeneralLinear M ℝ := ⟨B, Bᵀ, hB, mul_eq_one_comm.mp hB⟩
  have hkA : kA ∈ unitaryCompact ℝ a := by
    change A ∈ Matrix.unitaryGroup (Fin a) ℝ
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    exact hA
  have hkB : kB ∈ Kc (clR cl) := by
    refine ⟨?_, fun r s hrs => hk.2 _ _ hrs⟩
    change B ∈ Matrix.unitaryGroup (Fin M) ℝ
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    exact hB
  refine ⟨(⟨kA, hkA⟩, ⟨kB, hkB⟩), ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hK

include h2 in
/-- `μc cl` is the image of `haarK a ⊗ μc (clR cl)` under `(k₁, k₂) ↦ diag(k₁, k₂)`. -/
theorem map_dgK : Measure.map (dgK h1) ((haarK a).prod (μc (clR cl))) = μc cl := by
  have hc := continuous_dgK h1
  have : (Measure.map (dgK h1) ((haarK a).prod (μc (clR cl)))).IsHaarMeasure :=
    Measure.isHaarMeasure_map_of_isFiniteMeasure _ (dgK h1) hc (surjective_dgK h1 h2)
  exact eq_μc cl _

include h2 in
/-- **The first-block decomposition of the integral over `Kc cl`.** -/
theorem integral_Kc_eq {f : Kc cl → ℂ} (hf : Continuous f) :
    ∫ k, f k ∂μc cl =
      ∫ k₁, ∫ k₂, f (dgK h1 (k₁, k₂)) ∂μc (clR cl) ∂haarK a := by
  have hc := continuous_dgK h1
  rw [← map_dgK h1 h2, integral_map hc.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ ((hf.comp hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

end Peel

end RealLeviBlockHaar

end Langlands.Archimedean
