import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.UnipotentSandwich
import Langlands.Representation.Hecke.ActionProjection

/-!
# Growth of a unipotent-invariant functional on the dominant cone

Let `ρ` be a smooth representation of `GL_(n+1)(k)`, `P = K(a)` a positive principal level
with finite-dimensional fixed space `E`, and `ℓ` a linear functional invariant under the upper
unipotent elements of `P`. For antitone `μ` the value `ℓ(ρ(ϖ^μ) w)`, `w ∈ E`, grows at most
geometrically in the length of `μ` along the generators of the antitone cone.

The proof averages over `P`: by the unipotent sandwich, `ℓ(ρ(ϖ^μ) ρ(g) ρ(ϖ^ν) w)` is
independent of `g ∈ P` for antitone `μ, ν`, so `ℓ(ρ(ϖ^(μ+ν)) w) = ℓ(ρ(ϖ^μ) T_ν w)` with
`T_ν` the averaged translation, an endomorphism of the finite-dimensional space `E`.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockConvergence

open MeasureTheory Langlands.Conductor Langlands.GeneralLinear

universe u uG uV

section Average

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- If a linear functional is constant on the `K`-orbit of `v`, then it takes that constant
value at the normalized `K`-average of `v`. -/
theorem fixedProjection_dual_eq_of_const (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (L : V →ₗ[ℂ] ℂ) (v : V) (c : ℂ)
    (hc : ∀ g ∈ K, L (ρ g v) = c) :
    L (Hecke.fixedProjection μ ρ hρ K hK v : V) = c := by
  rw [Hecke.fixedProjection_apply]
  change L (Hecke.integratedAction μ ρ hρ _ v) = c
  rw [Hecke.integratedAction_dual]
  have h : ∀ g, (Hecke.HeckeAlgebra.toTestFunction μ
      (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) : HarmonicAnalysis.SchwartzBruhat G) g *
        L (ρ g v) =
      (K : Set G).indicator (fun _ => (μ.real (K : Set G) : ℂ)⁻¹ * c) g := by
    intro g
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem (show g ∈ (K : Set G) from hg), hc g hg]
      change Hecke.HeckeAlgebra.normalizedIndicator μ K hK g * c = _
      rw [Hecke.HeckeAlgebra.normalizedIndicator_apply,
        Set.indicator_of_mem (show g ∈ (K : Set G) from hg), mul_one]
    · rw [Set.indicator_of_notMem (show g ∉ (K : Set G) from hg)]
      change Hecke.HeckeAlgebra.normalizedIndicator μ K hK g * _ = 0
      rw [Hecke.HeckeAlgebra.normalizedIndicator_apply,
        Set.indicator_of_notMem (show g ∉ (K : Set G) from hg), mul_zero, zero_mul]
  simp_rw [h]
  rw [integral_indicator_const _ K.isOpen.measurableSet, Complex.real_smul, ← mul_assoc,
    mul_inv_cancel₀ (Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK), one_mul]

end Average

section Cone

/-- The length of an antitone exponent along the generators of the antitone cone:
`(lam_0 - lam_n) + |lam_n|`. -/
def coneWeight {n : ℕ} (lam : Fin (n + 1) → ℤ) : ℕ :=
  (lam 0 - lam (Fin.last n)).toNat + (lam (Fin.last n)).natAbs

/-- The generators of the antitone cone: the step exponents `(1, …, 1, 0, …, 0)` with the
last `1` at position `k`, and the constant exponents `1` and `-1`. -/
def coneGenerator {n : ℕ} : Fin n ⊕ Bool → Fin (n + 1) → ℤ
  | Sum.inl k => fun i => if i ≤ k.castSucc then 1 else 0
  | Sum.inr true => fun _ => 1
  | Sum.inr false => fun _ => -1

theorem antitone_coneGenerator {n : ℕ} (s : Fin n ⊕ Bool) : Antitone (coneGenerator s) := by
  rcases s with k | b
  · intro i j hij
    simp only [coneGenerator]
    split_ifs with hj hi hi
    · exact le_rfl
    · exact absurd (hij.trans hj) hi
    · exact zero_le_one
    · exact le_rfl
  · cases b <;> intro i j _ <;> exact le_rfl

theorem eq_zero_of_coneWeight_eq_zero {n : ℕ} {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam)
    (h : coneWeight lam = 0) (i : Fin (n + 1)) : lam i = 0 := by
  have h₀ := hlam (Fin.zero_le i)
  have h₁ := hlam (Fin.le_last i)
  unfold coneWeight at h
  omega

/-- A nonzero antitone exponent is an antitone exponent of smaller weight plus a cone
generator. -/
theorem exists_coneGenerator_step {n : ℕ} {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam)
    (h : coneWeight lam ≠ 0) :
    ∃ s, Antitone (lam - coneGenerator s) ∧ coneWeight (lam - coneGenerator s) + 1 =
      coneWeight lam := by
  have hlast := hlam (Fin.zero_le (Fin.last n))
  by_cases hc : lam 0 = lam (Fin.last n)
  · have hconst : ∀ i, lam i = lam (Fin.last n) := fun i => by
      have := hlam (Fin.zero_le i)
      have := hlam (Fin.le_last i)
      omega
    have hsub : ∀ c : ℤ, Antitone (lam - fun _ => c) := fun c i j _ => by
      simp only [Pi.sub_apply, hconst i, hconst j, le_rfl]
    rcases lt_or_ge 0 (lam (Fin.last n)) with hpos | hneg
    · refine ⟨Sum.inr true, hsub 1, ?_⟩
      unfold coneWeight at h ⊢
      simp only [coneGenerator, Pi.sub_apply]
      omega
    · refine ⟨Sum.inr false, hsub (-1), ?_⟩
      unfold coneWeight at h ⊢
      simp only [coneGenerator, Pi.sub_apply]
      omega
  · obtain ⟨k, hk⟩ : ∃ k : Fin n, lam k.castSucc ≠ lam k.succ := by
      by_contra hall
      push Not at hall
      have hall' : ∀ i : Fin (n + 1), lam i = lam 0 := fun i => by
        induction i using Fin.induction with
        | zero => rfl
        | succ i ih => rw [← hall i, ih]
      exact hc (hall' _).symm
    have hk' : lam k.succ < lam k.castSucc :=
      lt_of_le_of_ne (hlam (Fin.castSucc_le_succ k)) (Ne.symm hk)
    refine ⟨Sum.inl k, ?_, ?_⟩
    · intro i j hij
      simp only [Pi.sub_apply, coneGenerator]
      split_ifs with hj hi hi
      · linarith [hlam hij]
      · exact absurd (hij.trans hj) hi
      · have hkj : k.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hj)
        linarith [hlam hkj, hlam hi]
      · linarith [hlam hij]
    · have h0 : (0 : Fin (n + 1)) ≤ k.castSucc := Fin.zero_le _
      have hl : ¬ Fin.last n ≤ k.castSucc := not_le.mpr (Fin.castSucc_lt_last k)
      unfold coneWeight
      simp only [Pi.sub_apply, coneGenerator, h0, hl, ↓reduceIte]
      omega

end Cone

section Torus

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- **Projector identity.** For `w` fixed by the positive principal level `P = K(a)`, a
functional `ℓ` invariant under `P ∩ N`, and antitone exponents `lam₁, lam₂`,
`ℓ(ρ(ϖ^lam₁) Π_P(ρ(ϖ^lam₂) w)) = ℓ(ρ(ϖ^(lam₁+lam₂)) w)`. -/
theorem dual_torus_fixedProjection_torus
    [MeasurableSpace (GeneralLinear (n + 1) k)] [BorelSpace (GeneralLinear (n + 1) k)]
    (μ : Measure (GeneralLinear (n + 1) k)) [μ.IsHaarMeasure]
    (ρ : Representation ℂ (GeneralLinear (n + 1) k) V) (hρ : IsSmooth ρ)
    {a : ℕ} (ha : 0 < a) {ϖ : kˣ} (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1)
    (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ x ∈ principalLevelSubgroup k n a, x ∈ upperUnipotent (n + 1) k →
      ∀ v, ℓ (ρ x v) = ℓ v)
    {lam₁ lam₂ : Fin (n + 1) → ℤ} (h₁ : Antitone lam₁) (h₂ : Antitone lam₂)
    {w : V} (hw : w ∈ fixedVectors ρ (principalLevelOpenSubgroup k n a).toSubgroup) :
    ℓ (ρ (Iwasawa.torus ϖ lam₁)
        (Hecke.fixedProjection μ ρ hρ (principalLevelOpenSubgroup k n a)
          (isCompact_principalLevelOpenSubgroup k n a) (ρ (Iwasawa.torus ϖ lam₂) w) : V)) =
      ℓ (ρ (Iwasawa.torus ϖ (lam₁ + lam₂)) w) := by
  apply fixedProjection_dual_eq_of_const μ ρ hρ _ _ (ℓ ∘ₗ ρ (Iwasawa.torus ϖ lam₁))
  intro g hg
  obtain ⟨x, hxP, hxN, y, hyP, hxy⟩ := exists_unipotent_sandwich ha hϖ h₁ h₂ hg
  have hyw : ρ y w = w := (Representation.mem_invariants _ w).1 hw ⟨y, hyP⟩
  change ℓ (ρ (Iwasawa.torus ϖ lam₁) (ρ g (ρ (Iwasawa.torus ϖ lam₂) w))) = _
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    hxy, torus_add, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hyw,
    hℓ x hxP hxN]

/-- **Growth on the dominant cone.** For a positive principal level `P = K(a)` with
finite-dimensional fixed space and a functional `ℓ` invariant under `P ∩ N`, there is one
base `B ≥ 1` such that every `P`-fixed `w` satisfies `|ℓ(ρ(ϖ^lam) w)| ≤ C_w B^(weight lam)`
for all antitone `lam`. -/
theorem exists_dominant_bound (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (hρ : IsSmooth ρ) {a : ℕ} (ha : 0 < a)
    (hfin : Module.Finite ℂ (fixedVectors ρ (principalLevelOpenSubgroup k n a).toSubgroup))
    {ϖ : kˣ} (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ x ∈ principalLevelSubgroup k n a, x ∈ upperUnipotent (n + 1) k →
      ∀ v, ℓ (ρ x v) = ℓ v) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ w ∈ fixedVectors ρ (principalLevelOpenSubgroup k n a).toSubgroup,
      ∃ C : ℝ, ∀ lam : Fin (n + 1) → ℤ, Antitone lam →
        ‖ℓ (ρ (Iwasawa.torus ϖ lam) w)‖ ≤ C * B ^ coneWeight lam := by
  let G := GeneralLinear (n + 1) k
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  set K := principalLevelOpenSubgroup k n a
  have hK : IsCompact (K : Set G) := isCompact_principalLevelOpenSubgroup k n a
  let K₀ : TopologicalSpace.PositiveCompacts G :=
    ⟨⟨(K : Set G), hK⟩, by
      simpa only [K.isOpen.interior_eq] using
        (show (K : Set G).Nonempty from ⟨1, K.one_mem⟩)⟩
  let μ : Measure G := Measure.haarMeasure K₀
  have : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  set E := fixedVectors ρ K.toSubgroup
  let T : Fin n ⊕ Bool → E →ₗ[ℂ] E := fun s =>
    Hecke.fixedProjection μ ρ hρ K hK ∘ₗ ρ (Iwasawa.torus ϖ (coneGenerator s)) ∘ₗ E.subtype
  let e := (Module.finBasis ℂ E).equivFun
  let A : Fin n ⊕ Bool → _ := fun s =>
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ T s ∘ₗ e.symm.toLinearMap)
  let L := LinearMap.toContinuousLinearMap (ℓ ∘ₗ E.subtype ∘ₗ e.symm.toLinearMap)
  have hA : ∀ s (w : E), ‖e (T s w)‖ ≤ ‖A s‖ * ‖e w‖ := by
    intro s w
    have := (A s).le_opNorm (e w)
    simpa only [A, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply] using this
  have hL : ∀ w : E, ‖ℓ w‖ ≤ ‖L‖ * ‖e w‖ := by
    intro w
    have := L.le_opNorm (e w)
    simpa only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
      Submodule.coe_subtype] using this
  set B : ℝ := 1 + ∑ s, ‖A s‖
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun s _ => norm_nonneg _)
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hAB : ∀ s, ‖A s‖ ≤ B := fun s =>
    (Finset.single_le_sum (fun s _ => norm_nonneg (A s)) (Finset.mem_univ s)).trans
      (le_add_of_nonneg_left zero_le_one)
  have key : ∀ N : ℕ, ∀ lam : Fin (n + 1) → ℤ, Antitone lam → coneWeight lam = N →
      ∀ w : E, ‖ℓ (ρ (Iwasawa.torus ϖ lam) w)‖ ≤ ‖L‖ * B ^ N * ‖e w‖ := by
    intro N
    induction N with
    | zero =>
      intro lam hlam h0 w
      have hlam0 : lam = 0 := funext (eq_zero_of_coneWeight_eq_zero hlam h0)
      have ht : Iwasawa.torus ϖ lam = 1 := by
        rw [hlam0, Iwasawa.torus]
        simp only [Pi.zero_apply, zpow_zero]
        exact map_one _
      rw [ht, map_one, Module.End.one_apply, pow_zero, mul_one]
      exact hL w
    | succ N ih =>
      intro lam hlam hN w
      obtain ⟨s, hs, hws⟩ := exists_coneGenerator_step hlam (by omega)
      have hid := dual_torus_fixedProjection_torus μ ρ hρ ha hϖ ℓ hℓ hs
        (antitone_coneGenerator s) w.property
      rw [sub_add_cancel] at hid
      rw [← hid]
      have h1 := ih (lam - coneGenerator s) hs (by omega) (T s w)
      have h2 : ‖e (T s w)‖ ≤ B * ‖e w‖ :=
        (hA s w).trans (mul_le_mul_of_nonneg_right (hAB s) (norm_nonneg _))
      calc
        _ ≤ ‖L‖ * B ^ N * ‖e (T s w)‖ := h1
        _ ≤ ‖L‖ * B ^ N * (B * ‖e w‖) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (norm_nonneg _) (pow_nonneg hB0 _))
        _ = ‖L‖ * B ^ (N + 1) * ‖e w‖ := by ring
  refine ⟨B, hB1, fun w hw => ⟨‖L‖ * ‖e ⟨w, hw⟩‖, fun lam hlam => ?_⟩⟩
  have := key _ lam hlam rfl ⟨w, hw⟩
  calc
    _ ≤ ‖L‖ * B ^ coneWeight lam * ‖e ⟨w, hw⟩‖ := this
    _ = _ := by ring

end Torus

end Langlands.RankinSelberg.TwoBlockConvergence
