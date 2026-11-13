import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Langlands.GroupScheme.Quaternionic.KneserThreeUnits
import Langlands.GroupScheme.Examples.HermitianRootReflectionAction

/-!
# Quaternion data from an orthogonal involution and a symmetric element

Let `D` be a quaternion division algebra over `K` with an orthogonal involution `σ`, let
`ℓ = σ.quaternionAlternatingUnit` and let `bar = σ.quaternionConjugation` (so
`bar a = ℓ σ(a) ℓ⁻¹` and `a · bar a = Nrd a`). For a nonzero `σ`-symmetric `μ` and `2 ≠ 0`, the
element `x = -μ ℓ⁻¹` is pure and not a scalar, and a commutator `j = x y - y x` anticommutes with
`x`. `Quaternion.quatData` packages `x, j` and the basis `1, x, j, j x` as `QuatData K D`, whose
conjugation is `bar` and for which `σ d = ℓ · bar d · ℓ⁻¹` with `ℓ = ι l₁ + j ι l₂`. The section
`QuatData` (generic part) defines the Hermitian form with weights `(-1, δ)` and proves it is
anisotropic when `D` is a division ring.
-/

noncomputable section

universe u

open scoped TensorProduct


namespace Langlands.GroupScheme.KneserThree.QuatData

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.HermitianRoot QuadField

section Generic

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] (Q : QuatData K D)

local notation "conjL" => SU3Root.conjugation K (field Q.c)

/-- `(ι a + j ι a') · bar (ι a + j ι a') = ι (a ā - δ a' ā')`. -/
theorem elem_mul_bar (a a' : field Q.c) :
    Q.elem a a' * Q.bar (Q.elem a a') =
      Q.ι (a * conjL a - algebraMap K (field Q.c) Q.δ * a' * conjL a') := by
  have hb : Q.bar (Q.elem a a') = Q.ι (conjL a) - Q.j * Q.ι a' := by
    rw [QuatData.bar, QuatData.elem, Q.fst_mk, Q.snd_mk]
  have hι : ∀ b : field Q.c, Q.ι b * Q.j = Q.j * Q.ι (conjL b) := fun b => by
    rw [Q.j_mul_ι, SU3Root.conjugation_involutive K (field Q.c) b]
  have hjj : Q.j * Q.j = Q.ι (algebraMap K (field Q.c) Q.δ) := by
    rw [Q.j_mul_j, AlgHom.commutes]
  rw [hb, QuatData.elem]
  calc (Q.ι a + Q.j * Q.ι a') * (Q.ι (conjL a) - Q.j * Q.ι a') =
      Q.ι a * Q.ι (conjL a) - (Q.ι a * Q.j) * Q.ι a' + Q.j * (Q.ι a' * Q.ι (conjL a)) -
        Q.j * (Q.ι a' * Q.j) * Q.ι a' := by noncomm_ring
    _ = Q.ι a * Q.ι (conjL a) - Q.j * (Q.ι (conjL a) * Q.ι a') +
        Q.j * (Q.ι a' * Q.ι (conjL a)) - (Q.j * Q.j) * (Q.ι (conjL a') * Q.ι a') := by
        rw [hι, hι]; noncomm_ring
    _ = _ := by
        rw [hjj, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
          mul_comm (conjL a) a', sub_add_cancel, ← map_sub]
        congr 1
        ring

variable (hδ : Q.δ ≠ 0)

/-- The diagonal Hermitian form with weights `(-1, δ)`. -/
def diagForm : DiagonalForm (SU3Root.fieldInvolution K (field Q.c)) (Fin 2) where
  weight := ![-1, algebraMap K (field Q.c) Q.δ]
  bar_weight i := by
    fin_cases i
    · simp
    · exact (SU3Root.conjugation K (field Q.c)).commutes Q.δ

@[simp] theorem diagForm_weight : (Q.diagForm).weight = ![-1, algebraMap K (field Q.c) Q.δ] :=
  rfl

include hδ in
theorem algebraMap_δ_ne_zero : algebraMap K (field Q.c) Q.δ ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K (field Q.c))).mpr hδ

include hδ in
/-- Unit witnesses for the weights. -/
def diagUnits : Fin 2 → (field Q.c)ˣ :=
  ![-1, Units.mk0 (algebraMap K (field Q.c) Q.δ) (Q.algebraMap_δ_ne_zero hδ)]

theorem diagUnits_val : ∀ i, (Q.diagUnits hδ i : field Q.c) = (Q.diagForm).weight i := by
  intro i
  fin_cases i <;> simp [diagUnits]

include hδ in
/-- The weights `(-1, δ)` give an anisotropic form, because `δ` is not a norm from `L` in the
division algebra `D`. -/
theorem diagForm_isAnisotropic : (Q.diagForm).IsAnisotropic := by
  intro x hx
  have hx' : -(x 0 * conjL (x 0)) + algebraMap K (field Q.c) Q.δ * (x 1 * conjL (x 1)) = 0 := by
    simpa [DiagonalForm.pairing, Fin.sum_univ_two, mul_assoc] using hx
  by_cases h1 : x 1 = 0
  · have h0 : x 0 * conjL (x 0) = 0 := by simpa [h1] using hx'
    have : x 0 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · simpa using h
    funext i
    fin_cases i
    · exact this
    · exact h1
  · exfalso
    set a := x 0 * (x 1)⁻¹
    have hδa : algebraMap K (field Q.c) Q.δ = a * conjL a := by
      have hc1 : conjL (x 1) ≠ 0 := by simpa using h1
      simp only [a, map_mul, map_inv₀]
      field_simp
      linear_combination hx'
    have ha : a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hδa
      exact Q.algebraMap_δ_ne_zero hδ hδa
    set b := (conjL a)⁻¹
    have hb : b ≠ 0 := by simpa [b] using ha
    set u := Q.j * Q.ι b
    have hu : u * u = 1 := by
      have hι : Q.ι b * Q.j = Q.j * Q.ι (conjL b) := by
        rw [Q.j_mul_ι, SU3Root.conjugation_involutive K (field Q.c) b]
      calc u * u = Q.j * (Q.ι b * Q.j) * Q.ι b := by simp only [u, mul_assoc]
        _ = (Q.j * Q.j) * Q.ι (conjL b * b) := by rw [hι, map_mul]; noncomm_ring
        _ = Q.ι (algebraMap K (field Q.c) Q.δ * (conjL b * b)) := by
            rw [Q.j_mul_j, ← AlgHom.commutes Q.ι, ← map_mul]
        _ = 1 := by
            have hca : conjL a ≠ 0 := fun h => ha ((map_eq_zero_iff (SU3Root.conjugation K
              (field Q.c)) (SU3Root.conjugation K (field Q.c)).injective).mp h)
            have hcb : conjL b = a⁻¹ := by
              simp only [b]
              rw [map_inv₀, SU3Root.conjugation_involutive K (field Q.c) a]
            rw [hδa, hcb, ← map_one Q.ι]
            congr 1
            simp only [b]
            calc a * conjL a * (a⁻¹ * (conjL a)⁻¹) = (a * a⁻¹) * (conjL a * (conjL a)⁻¹) := by
                  ring
              _ = 1 := by rw [mul_inv_cancel₀ ha, mul_inv_cancel₀ hca, one_mul]
    have hu' : (u - 1) * (u + 1) = 0 := by
      calc (u - 1) * (u + 1) = u * u - 1 := by noncomm_ring
        _ = 0 := by rw [hu, sub_self]
    have hsnd : Q.snd u = b := Q.snd_j_mul b
    rcases mul_eq_zero.mp hu' with h | h
    · rw [sub_eq_zero.mp h, ← map_one Q.ι, Q.snd_ι] at hsnd
      exact hb hsnd.symm
    · rw [eq_neg_of_add_eq_zero_left h, ← map_one Q.ι, ← map_neg, Q.snd_ι] at hsnd
      exact hb hsnd.symm

end Generic

end Langlands.GroupScheme.KneserThree.QuatData

namespace Langlands.GroupScheme.KneserThree.Quaternion

open Langlands.GroupScheme.Quaternionic QuadField

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D) (hdim : Module.finrank K D = 4)
  (hsym : Module.finrank K σ.symmetricSubspace = 3)

/-- The quaternion conjugation. -/
abbrev conj : FirstKindInvolution K D := σ.quaternionConjugation hdim hsym

/-- The alternating unit `ℓ`. -/
abbrev ell : Dˣ := σ.quaternionAlternatingUnit hdim hsym

/-- The reduced norm as an element of `K`. -/
def nrd (a : D) : K := Langlands.CentralSimple.reducedNorm K D K (1 ⊗ₜ[K] a)

theorem mul_conj (a : D) : a * conj σ hdim hsym a = algebraMap K D (nrd a) :=
  σ.quaternionConjugation_norm hdim hsym a

omit [Algebra.IsCentral K D] in
theorem conj_apply (a : D) :
    conj σ hdim hsym a = (ell σ hdim hsym : D) * σ a * (ell σ hdim hsym : D)⁻¹ := rfl

omit [Algebra.IsCentral K D] in
theorem sigma_ell : σ (ell σ hdim hsym : D) = -(ell σ hdim hsym : D) :=
  σ.map_eq_neg_of_mem_alternating (σ.quaternionAlternatingUnit_mem hdim hsym)

omit [Algebra.IsCentral K D] in
theorem conj_ell : conj σ hdim hsym (ell σ hdim hsym : D) = -(ell σ hdim hsym : D) := by
  rw [conj_apply, sigma_ell]
  simp

omit [Algebra.IsCentral K D] in
theorem conj_algebraMap (k : K) : conj σ hdim hsym (algebraMap K D k) = algebraMap K D k :=
  FirstKindInvolution.map_algebraMap _ k

theorem add_conj_mem (a : D) : ∃ t : K, a + conj σ hdim hsym a = algebraMap K D t := by
  refine ⟨nrd (1 + a) - 1 - nrd a, ?_⟩
  have h1 := mul_conj σ hdim hsym (1 + a)
  have h2 := mul_conj σ hdim hsym a
  rw [FirstKindInvolution.map_add, FirstKindInvolution.map_one] at h1
  rw [map_sub, map_sub, ← h1, ← h2, map_one]
  noncomm_ring

omit [Algebra.IsCentral K D] in
theorem sigma_ell_inv : σ ((ell σ hdim hsym : D)⁻¹) = -((ell σ hdim hsym : D)⁻¹) := by
  have hl : (ell σ hdim hsym : D) ≠ 0 := (ell σ hdim hsym).ne_zero
  have h : σ ((ell σ hdim hsym : D)⁻¹) * σ (ell σ hdim hsym : D) = 1 := by
    rw [← FirstKindInvolution.map_mul, mul_inv_cancel₀ hl, FirstKindInvolution.map_one]
  rw [sigma_ell] at h
  have h' : σ ((ell σ hdim hsym : D)⁻¹) = ((-(ell σ hdim hsym : D)))⁻¹ :=
    eq_inv_of_mul_eq_one_left h
  rw [h', inv_neg]

variable {σ hdim hsym}

variable (σ hdim hsym) in
/-- The pure quaternion `x = -μ ℓ⁻¹`. -/
def pure (μ : D) : D := -(μ * (ell σ hdim hsym : D)⁻¹)

omit [Algebra.IsCentral K D] in
theorem conj_pure {μ : D} (hμ : σ μ = μ) :
    conj σ hdim hsym (pure σ hdim hsym μ) = -pure σ hdim hsym μ := by
  have hl : (ell σ hdim hsym : D) ≠ 0 := (ell σ hdim hsym).ne_zero
  rw [conj_apply, pure, FirstKindInvolution.map_neg, FirstKindInvolution.map_mul, hμ,
    sigma_ell_inv]
  simp only [neg_mul, neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hl, one_mul]

theorem pure_mul_self {μ : D} (hμ : σ μ = μ) :
    pure σ hdim hsym μ * pure σ hdim hsym μ =
      algebraMap K D (-nrd (pure σ hdim hsym μ)) := by
  have h := mul_conj σ hdim hsym (pure σ hdim hsym μ)
  rw [conj_pure hμ, mul_neg] at h
  rw [map_neg, ← h, neg_neg]

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
theorem two_ne_zero_D (h2 : (2 : K) ≠ 0) : (2 : D) ≠ 0 := by
  have := (map_ne_zero_iff (algebraMap K D) (FaithfulSMul.algebraMap_injective K D)).mpr h2
  rwa [map_ofNat] at this

omit [Algebra.IsCentral K D] in
theorem pure_ne_zero {μ : D} (hμ0 : μ ≠ 0) : pure σ hdim hsym μ ≠ 0 := by
  simp [pure, hμ0, (ell σ hdim hsym).ne_zero]

omit [Algebra.IsCentral K D] in
theorem pure_ne_algebraMap (h2 : (2 : K) ≠ 0) {μ : D} (hμ : σ μ = μ) (hμ0 : μ ≠ 0) (k : K) :
    pure σ hdim hsym μ ≠ algebraMap K D k := by
  intro h
  have hc := conj_pure (hdim := hdim) (hsym := hsym) hμ
  rw [h, conj_algebraMap, ← h] at hc
  have : (2 : D) * pure σ hdim hsym μ = 0 := by
    rw [two_mul]; nth_rewrite 1 [hc]; simp
  rcases mul_eq_zero.mp this with h' | h'
  · exact two_ne_zero_D h2 h'
  · exact pure_ne_zero hμ0 h'

theorem exists_not_commute (h2 : (2 : K) ≠ 0) {μ : D} (hμ : σ μ = μ) (hμ0 : μ ≠ 0) :
    ∃ y : D, pure σ hdim hsym μ * y ≠ y * pure σ hdim hsym μ := by
  by_contra hc
  push Not at hc
  have hmem : pure σ hdim hsym μ ∈ Subalgebra.center K D := by
    rw [Subalgebra.mem_center_iff]
    intro y
    exact (hc y).symm
  have hbot := Algebra.IsCentral.out hmem
  obtain ⟨k, hk⟩ := Algebra.mem_bot.mp hbot
  exact pure_ne_algebraMap h2 hμ hμ0 k hk.symm

section Partner

variable (σ hdim hsym) (h2 : (2 : K) ≠ 0) {μ : D} (hμ : σ μ = μ) (hμ0 : μ ≠ 0)
include h2 hμ hμ0

/-- An element not commuting with `x`. -/
def partner : D := (exists_not_commute (hdim := hdim) (hsym := hsym) h2 hμ hμ0).choose

/-- The commutator `j = x y - y x`. -/
def jay : D :=
  pure σ hdim hsym μ * partner σ hdim hsym h2 hμ hμ0 - partner σ hdim hsym h2 hμ hμ0 * pure σ hdim hsym μ

theorem jay_ne_zero : jay σ hdim hsym h2 hμ hμ0 ≠ 0 := by
  rw [jay, sub_ne_zero]
  exact (exists_not_commute (hdim := hdim) (hsym := hsym) h2 hμ hμ0).choose_spec

theorem jay_mul_pure :
    jay σ hdim hsym h2 hμ hμ0 * pure σ hdim hsym μ = -(pure σ hdim hsym μ * jay σ hdim hsym h2 hμ hμ0) := by
  have hc : pure σ hdim hsym μ * pure σ hdim hsym μ * partner σ hdim hsym h2 hμ hμ0 =
      partner σ hdim hsym h2 hμ hμ0 * (pure σ hdim hsym μ * pure σ hdim hsym μ) := by
    rw [pure_mul_self hμ]
    exact (Algebra.commutes _ _)
  simp only [jay, sub_mul, mul_sub, neg_sub]
  have e1 : pure σ hdim hsym μ * partner σ hdim hsym h2 hμ hμ0 * pure σ hdim hsym μ =
      pure σ hdim hsym μ * (partner σ hdim hsym h2 hμ hμ0 * pure σ hdim hsym μ) := mul_assoc _ _ _
  rw [mul_assoc (partner σ hdim hsym h2 hμ hμ0), ← mul_assoc (pure σ hdim hsym μ) (pure σ hdim hsym μ), hc,
    ← mul_assoc, e1]

theorem conj_jay : conj σ hdim hsym (jay σ hdim hsym h2 hμ hμ0) = -jay σ hdim hsym h2 hμ hμ0 := by
  obtain ⟨t, ht⟩ := add_conj_mem σ hdim hsym (partner σ hdim hsym h2 hμ hμ0)
  have hy : conj σ hdim hsym (partner σ hdim hsym h2 hμ hμ0) = algebraMap K D t - partner σ hdim hsym h2 hμ hμ0 := by
    rw [← ht]; abel
  rw [jay, FirstKindInvolution.map_sub, FirstKindInvolution.map_mul,
    FirstKindInvolution.map_mul, hy, conj_pure hμ]
  have hcomm : algebraMap K D t * pure σ hdim hsym μ = pure σ hdim hsym μ * algebraMap K D t :=
    Algebra.commutes _ _
  noncomm_ring
  rw [hcomm]
  abel

theorem jay_mul_self :
    jay σ hdim hsym h2 hμ hμ0 * jay σ hdim hsym h2 hμ hμ0 = algebraMap K D (-nrd (jay σ hdim hsym h2 hμ hμ0)) := by
  have h := mul_conj σ hdim hsym (jay σ hdim hsym h2 hμ hμ0)
  rw [conj_jay, mul_neg] at h
  rw [map_neg, ← h, neg_neg]

end Partner

section Basis

variable (σ hdim hsym) (h2 : (2 : K) ≠ 0) {μ : D} (hμ : σ μ = μ) (hμ0 : μ ≠ 0)
include h2 hμ hμ0

/-- The four vectors `1, x, j, j x`. -/
def quadVectors : Fin 4 → D :=
  ![1, pure σ hdim hsym μ, jay σ hdim hsym h2 hμ hμ0,
    jay σ hdim hsym h2 hμ hμ0 * pure σ hdim hsym μ]

private theorem eq_zero_of_linear {a b : K}
    (h : a • (1 : D) + b • pure σ hdim hsym μ = 0) : a = 0 ∧ b = 0 := by
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
  by_cases hb : b = 0
  · subst hb
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨(map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K D)).mp h, rfl⟩
  · exfalso
    apply pure_ne_algebraMap (hdim := hdim) (hsym := hsym) h2 hμ hμ0 (-(a / b))
    have hb' : algebraMap K D b ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K D)).mpr hb
    have : algebraMap K D b * pure σ hdim hsym μ =
        algebraMap K D b * algebraMap K D (-(a / b)) := by
      rw [← map_mul, mul_neg, mul_div_cancel₀ _ hb, map_neg]
      exact eq_neg_of_add_eq_zero_right h
    exact mul_left_cancel₀ hb' this

theorem linearIndependent_quadVectors :
    LinearIndependent K (quadVectors σ hdim hsym h2 hμ hμ0) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set x := pure σ hdim hsym μ
  set j := jay σ hdim hsym h2 hμ hμ0
  set u := g 0 • (1 : D) + g 1 • x
  set w := g 2 • (1 : D) + g 3 • x
  have hsum : u + j * w = 0 := by
    rw [← hg]
    simp [quadVectors, Fin.sum_univ_four, u, w, mul_add, x, j]
    abel
  have hxj : x * j = -(j * x) := by rw [jay_mul_pure, neg_neg]
  have hxu : x * u = u * x := by
    simp [u, mul_add, add_mul]
  have hxw : x * w = w * x := by
    simp [w, mul_add, add_mul]
  have hdiff : (u - j * w) * x = 0 := by
    have : x * (u + j * w) = (u - j * w) * x := by
      rw [mul_add, hxu, ← mul_assoc, hxj, neg_mul, mul_assoc, hxw, sub_mul, mul_assoc]
      abel
    rw [← this, hsum, mul_zero]
  have hdiff' : u - j * w = 0 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact h
    · exact absurd h (pure_ne_zero hμ0)
  have hu : u = 0 := by
    have h2u : (2 : D) * u = 0 := by
      rw [two_mul]
      calc u + u = (u + j * w) + (u - j * w) := by abel
        _ = 0 := by rw [hsum, hdiff', add_zero]
    rcases mul_eq_zero.mp h2u with h | h
    · exact absurd h (two_ne_zero_D h2)
    · exact h
  have hw : w = 0 := by
    have hjw : j * w = 0 := by rw [hu, zero_add] at hsum; exact hsum
    rcases mul_eq_zero.mp hjw with h | h
    · exact absurd h (jay_ne_zero σ hdim hsym h2 hμ hμ0)
    · exact h
  obtain ⟨h0, h1⟩ := eq_zero_of_linear σ hdim hsym h2 hμ hμ0 hu
  obtain ⟨h2', h3⟩ := eq_zero_of_linear σ hdim hsym h2 hμ hμ0 hw
  intro i
  fin_cases i <;> assumption

/-- The basis `1, x, j, j x` of `D`. -/
def quadBasis : Module.Basis (Fin 4) K D :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_quadVectors σ hdim hsym h2 hμ hμ0)
    (by rw [Fintype.card_fin, hdim])

theorem quadBasis_apply (i : Fin 4) :
    quadBasis σ hdim hsym h2 hμ hμ0 i = quadVectors σ hdim hsym h2 hμ hμ0 i := by
  simp [quadBasis]

end Basis


section Ell

/-- `ℓ² = -Nrd ℓ` is a scalar. -/
theorem ell_mul_self :
    (ell σ hdim hsym : D) * ell σ hdim hsym = algebraMap K D (-nrd (ell σ hdim hsym : D)) := by
  have h := mul_conj σ hdim hsym (ell σ hdim hsym : D)
  rw [conj_ell, mul_neg] at h
  rw [map_neg, ← h, neg_neg]

/-- `σ d = ℓ · conj d · ℓ⁻¹`, since `ℓ²` is central. -/
theorem sigma_eq_conj (d : D) :
    σ d = (ell σ hdim hsym : D) * conj σ hdim hsym d *
      (((ell σ hdim hsym)⁻¹ : Dˣ) : D) := by
  set l := ell σ hdim hsym
  have hl0 : (l : D) ≠ 0 := l.ne_zero
  have hc : (l : D) * l * σ d = σ d * (l * l) := by
    rw [ell_mul_self]; exact Algebra.commutes _ _
  rw [conj_apply, Units.val_inv_eq_inv_val]
  calc σ d = σ d * ((l : D) * l) * ((l : D)⁻¹ * (l : D)⁻¹) := by
        rw [mul_assoc, mul_assoc (l : D), mul_inv_cancel_left₀ hl0, mul_inv_cancel₀ hl0, mul_one]
    _ = (l : D) * l * σ d * ((l : D)⁻¹ * (l : D)⁻¹) := by rw [hc]
    _ = _ := by simp only [mul_assoc]; rfl

end Ell

section Data

variable (σ hdim hsym) (h2 : (2 : K) ≠ 0) {μ : D} (hμ : σ μ = μ) (hμ0 : μ ≠ 0)
include h2 hμ hμ0

theorem pure_sq_ne (r : K) : r * r ≠ -nrd (pure σ hdim hsym μ) := by
  intro hr
  set x := pure σ hdim hsym μ
  have hx : x * x = algebraMap K D (-nrd x) := pure_mul_self hμ
  have hc : x * algebraMap K D r = algebraMap K D r * x := (Algebra.commutes r x).symm
  have h0 : (x - algebraMap K D r) * (x + algebraMap K D r) = 0 := by
    calc (x - algebraMap K D r) * (x + algebraMap K D r) =
        x * x + x * algebraMap K D r - algebraMap K D r * x -
          algebraMap K D r * algebraMap K D r := by noncomm_ring
      _ = 0 := by rw [hx, hc, ← map_mul, hr]; abel
  rcases mul_eq_zero.mp h0 with h | h
  · exact pure_ne_algebraMap h2 hμ hμ0 r (sub_eq_zero.mp h)
  · exact pure_ne_algebraMap h2 hμ hμ0 (-r) (by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h)

/-- **The quaternion data** `x = -μ ℓ⁻¹`, `j = x y - y x`, `c = x²`, `δ = j²`, basis
`1, x, j, j x`. -/
def quatData : QuatData K D where
  c := -nrd (pure σ hdim hsym μ)
  δ := -nrd (jay σ hdim hsym h2 hμ hμ0)
  x := pure σ hdim hsym μ
  j := jay σ hdim hsym h2 hμ hμ0
  x_mul_x := pure_mul_self hμ
  j_mul_j := jay_mul_self σ hdim hsym h2 hμ hμ0
  j_mul_x := jay_mul_pure σ hdim hsym h2 hμ hμ0
  basis := quadBasis σ hdim hsym h2 hμ hμ0
  basis_eq := funext (quadBasis_apply σ hdim hsym h2 hμ hμ0)
  irreducible := QuadField.irreducible_poly (pure_sq_ne σ hdim hsym h2 hμ hμ0)
  separable := by
    have : Fact (Irreducible (QuadField.poly (-nrd (pure σ hdim hsym μ)))) :=
      ⟨QuadField.irreducible_poly (pure_sq_ne σ hdim hsym h2 hμ hμ0)⟩
    exact QuadField.isSeparable h2 (fun h =>
      pure_sq_ne σ hdim hsym h2 hμ hμ0 0 (by rw [mul_zero, h]))

theorem quatData_x : (quatData σ hdim hsym h2 hμ hμ0).x = pure σ hdim hsym μ := rfl

theorem quatData_j : (quatData σ hdim hsym h2 hμ hμ0).j = jay σ hdim hsym h2 hμ hμ0 := rfl

theorem quatData_δ_ne_zero : (quatData σ hdim hsym h2 hμ hμ0).δ ≠ 0 := by
  intro h
  have hj := (quatData σ hdim hsym h2 hμ hμ0).j_mul_j
  rw [h, map_zero, quatData_j] at hj
  rcases mul_eq_zero.mp hj with h' | h' <;> exact jay_ne_zero σ hdim hsym h2 hμ hμ0 h'

theorem conj_ι (a : field (quatData σ hdim hsym h2 hμ hμ0).c) :
    conj σ hdim hsym ((quatData σ hdim hsym h2 hμ hμ0).ι a) =
      (quatData σ hdim hsym h2 hμ hμ0).ι
        (SU3Root.conjugation K (field (quatData σ hdim hsym h2 hμ hμ0).c) a) := by
  obtain ⟨a₀, a₁, rfl⟩ := QuadField.exists_eq a
  have hcr : SU3Root.conjugation K (field (quatData σ hdim hsym h2 hμ hμ0).c)
      (a₀ • (1 : field (quatData σ hdim hsym h2 hμ hμ0).c) + a₁ • QuadField.root) =
      a₀ • (1 : field (quatData σ hdim hsym h2 hμ hμ0).c) + (-a₁) • QuadField.root := by
    rw [map_add, map_smul, map_smul, map_one, QuadField.conjugation_root, smul_neg, neg_smul]
  rw [hcr, QuatData.ι_linear, QuatData.ι_linear, FirstKindInvolution.map_add,
    FirstKindInvolution.map_smul, FirstKindInvolution.map_smul, FirstKindInvolution.map_one,
    quatData_x, conj_pure hμ, smul_neg, neg_smul]

/-- The Library's quaternion conjugation is the conjugation `bar` of the splitting. -/
theorem conj_eq_bar (d : D) :
    conj σ hdim hsym d = (quatData σ hdim hsym h2 hμ hμ0).bar d := by
  set Q := quatData σ hdim hsym h2 hμ hμ0
  have hj : conj σ hdim hsym Q.j = -Q.j := conj_jay σ hdim hsym h2 hμ hμ0
  conv_lhs => rw [← Q.decompose d]
  rw [FirstKindInvolution.map_add, FirstKindInvolution.map_mul, conj_ι, conj_ι, hj, mul_neg,
    ← Q.j_mul_ι, QuatData.bar, sub_eq_add_neg]

/-- The coordinates `ℓ = ι l₁ + j ι l₂` of the alternating unit. -/
abbrev lOne : field (quatData σ hdim hsym h2 hμ hμ0).c :=
  (quatData σ hdim hsym h2 hμ hμ0).fst (ell σ hdim hsym : D)

abbrev lTwo : field (quatData σ hdim hsym h2 hμ hμ0).c :=
  (quatData σ hdim hsym h2 hμ hμ0).snd (ell σ hdim hsym : D)

theorem elem_lOne_lTwo :
    (quatData σ hdim hsym h2 hμ hμ0).elem (lOne σ hdim hsym h2 hμ hμ0)
      (lTwo σ hdim hsym h2 hμ hμ0) = (ell σ hdim hsym : D) :=
  (quatData σ hdim hsym h2 hμ hμ0).decompose _

theorem conjugation_lOne :
    SU3Root.conjugation K (field (quatData σ hdim hsym h2 hμ hμ0).c)
      (lOne σ hdim hsym h2 hμ hμ0) = -lOne σ hdim hsym h2 hμ hμ0 := by
  set Q := quatData σ hdim hsym h2 hμ hμ0
  have h : Q.bar (ell σ hdim hsym : D) = -(ell σ hdim hsym : D) := by
    rw [← conj_eq_bar, conj_ell]
  have h' := congrArg Q.fst h
  rw [QuatData.bar, sub_eq_add_neg, ← mul_neg, ← map_neg, Q.fst_mk, map_neg] at h'
  exact h'

theorem sigma_eq_bar (d : D) :
    σ d = (quatData σ hdim hsym h2 hμ hμ0).elem (lOne σ hdim hsym h2 hμ hμ0)
      (lTwo σ hdim hsym h2 hμ hμ0) * (quatData σ hdim hsym h2 hμ hμ0).bar d *
        (((ell σ hdim hsym)⁻¹ : Dˣ) : D) := by
  rw [elem_lOne_lTwo, ← conj_eq_bar, ← sigma_eq_conj]

/-- With `θ = root`, `-(ι θ · ℓ) = μ`. -/
theorem neg_ι_root_mul_elem :
    -((quatData σ hdim hsym h2 hμ hμ0).ι QuadField.root *
      (quatData σ hdim hsym h2 hμ hμ0).elem (lOne σ hdim hsym h2 hμ hμ0)
        (lTwo σ hdim hsym h2 hμ hμ0)) = μ := by
  rw [(quatData σ hdim hsym h2 hμ hμ0).ι_root, elem_lOne_lTwo, quatData_x, pure, neg_mul,
    neg_neg, mul_assoc, inv_mul_cancel₀ (ell σ hdim hsym).ne_zero, mul_one]

theorem root_ne_zero : (QuadField.root : field (quatData σ hdim hsym h2 hμ hμ0).c) ≠ 0 := by
  intro h
  have hr := QuadField.root_mul_self (c := (quatData σ hdim hsym h2 hμ hμ0).c)
  rw [h, mul_zero] at hr
  have h0 : (quatData σ hdim hsym h2 hμ hμ0).c = 0 :=
    (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K _)).mp hr.symm
  exact pure_sq_ne σ hdim hsym h2 hμ hμ0 0 (by rw [mul_zero]; exact h0.symm)

theorem norm_lOne_lTwo_ne_zero :
    lOne σ hdim hsym h2 hμ hμ0 *
        SU3Root.conjugation K (field (quatData σ hdim hsym h2 hμ hμ0).c)
          (lOne σ hdim hsym h2 hμ hμ0) -
      algebraMap K (field (quatData σ hdim hsym h2 hμ hμ0).c)
          (quatData σ hdim hsym h2 hμ hμ0).δ * lTwo σ hdim hsym h2 hμ hμ0 *
        SU3Root.conjugation K (field (quatData σ hdim hsym h2 hμ hμ0).c)
          (lTwo σ hdim hsym h2 hμ hμ0) ≠ 0 := by
  set Q := quatData σ hdim hsym h2 hμ hμ0
  intro h
  have hm := Q.elem_mul_bar (lOne σ hdim hsym h2 hμ hμ0) (lTwo σ hdim hsym h2 hμ hμ0)
  rw [h, map_zero, elem_lOne_lTwo, ← conj_eq_bar, conj_ell, mul_neg, neg_eq_zero] at hm
  rcases mul_eq_zero.mp hm with h' | h' <;> exact (ell σ hdim hsym).ne_zero h'

end Data

end Langlands.GroupScheme.KneserThree.Quaternion
