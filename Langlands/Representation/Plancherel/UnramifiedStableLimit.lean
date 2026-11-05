import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! # Weak stable limits of polynomial endomorphism families

If iterates of an endomorphism applied to a vector converge weakly, the limit
is fixed, and every annihilating polynomial `(X - 1)^k r` gives
`r(1) • limit = r(Φ) start`. For a regular finite-dimensional family this
supplies one nonzero regular scalar before every starting vector.
-/

noncomputable section

open Filter Topology Polynomial
open scoped NNReal

namespace Langlands.Plancherel

universe uG uI uE uW uY

section StableLimit

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]
  (Φ : Module.End ℂ E) (D : Submodule ℂ (Module.Dual ℂ E))

/-- Precomposition with powers of `Φ` preserves a `Φ`-stable functional space. -/
theorem comp_pow_mem (hD : ∀ l ∈ D, l ∘ₗ Φ ∈ D) (n : ℕ) {l : Module.Dual ℂ E}
    (hl : l ∈ D) : l ∘ₗ (Φ ^ n) ∈ D := by
  induction n with
  | zero =>
    rw [pow_zero, Module.End.one_eq_id, LinearMap.comp_id]
    exact hl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    exact hD _ ih

/-- Precomposition with any polynomial in `Φ` preserves the functional space. -/
theorem comp_aeval_mem (hD : ∀ l ∈ D, l ∘ₗ Φ ∈ D) (p : ℂ[X]) {l : Module.Dual ℂ E}
    (hl : l ∈ D) : l ∘ₗ aeval Φ p ∈ D := by
  have heq : l ∘ₗ aeval Φ p =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (l ∘ₗ Φ ^ i) := by
    rw [aeval_eq_sum_range]
    ext x
    simp [LinearMap.sum_apply, map_sum]
  rw [heq]
  exact D.sum_mem fun i _ => D.smul_mem _ (comp_pow_mem Φ D hD i hl)

/-- A vector killed by a power of `Φ - 1`, whose iterates tend weakly to zero
along a separating `Φ`-stable functional space, is zero. -/
theorem eq_zero_of_unipotent_of_tendsto_zero (hD : ∀ l ∈ D, l ∘ₗ Φ ∈ D)
    (hsep : ∀ x : E, (∀ l ∈ D, l x = 0) → x = 0) :
    ∀ (k : ℕ) (y : E), ((Φ - 1) ^ k) y = 0 →
      (∀ l ∈ D, Tendsto (fun n => l ((Φ ^ n) y)) atTop (𝓝 0)) → y = 0 := by
  intro k
  induction k with
  | zero =>
    intro y hy _
    simpa using hy
  | succ k ih =>
    intro y hy hlim
    apply ih y _ hlim
    apply hsep
    intro l hl
    have hz : Φ (((Φ - 1) ^ k) y) = ((Φ - 1) ^ k) y := by
      have h1 : (Φ - 1) (((Φ - 1) ^ k) y) = 0 := by
        rw [pow_succ', Module.End.mul_apply] at hy
        exact hy
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
      exact h1
    have hpow : ∀ n : ℕ, (Φ ^ n) (((Φ - 1) ^ k) y) = ((Φ - 1) ^ k) y := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn => rw [pow_succ', Module.End.mul_apply, ihn, hz]
    have hcomm : Commute ((Φ - 1) ^ k) Φ :=
      ((Commute.refl Φ).sub_left (Commute.one_left Φ)).pow_left k
    have hl' : l ∘ₗ ((Φ - 1) ^ k) ∈ D := by
      have := comp_aeval_mem Φ D hD ((X - C 1) ^ k) hl
      simpa using this
    have ht := hlim _ hl'
    have hfun : (fun n : ℕ => (l ∘ₗ ((Φ - 1) ^ k)) ((Φ ^ n) y)) =
        fun _ => l (((Φ - 1) ^ k) y) := by
      funext n
      rw [LinearMap.comp_apply, ← Module.End.mul_apply, (hcomm.pow_right n).eq,
        Module.End.mul_apply, hpow]
    rw [hfun] at ht
    exact tendsto_nhds_unique tendsto_const_nhds ht

/-- A weak limit of iterates is fixed by `Φ`. -/
theorem stableLimit_fixed (hD : ∀ l ∈ D, l ∘ₗ Φ ∈ D)
    (hsep : ∀ x : E, (∀ l ∈ D, l x = 0) → x = 0) {β₀ β : E}
    (hlim : ∀ l ∈ D, Tendsto (fun n => l ((Φ ^ n) β₀)) atTop (𝓝 (l β))) :
    Φ β = β := by
  have h0 : Φ β - β = 0 := by
    apply hsep
    intro l hl
    have h1 := hlim _ (hD l hl)
    have h2 : Tendsto (fun n => l ((Φ ^ (n + 1)) β₀)) atTop (𝓝 (l β)) :=
      (hlim l hl).comp (tendsto_add_atTop_nat 1)
    have hfun : (fun n => (l ∘ₗ Φ) ((Φ ^ n) β₀)) = fun n => l ((Φ ^ (n + 1)) β₀) := by
      funext n
      rw [LinearMap.comp_apply, pow_succ', Module.End.mul_apply]
    rw [hfun] at h1
    rw [map_sub, sub_eq_zero]
    exact (tendsto_nhds_unique h2 h1).symm
  exact sub_eq_zero.mp h0

/-- A polynomial in `Φ` acts on a fixed vector by its value at one. -/
theorem aeval_apply_of_fixed {β : E} (hβ : Φ β = β) (p : ℂ[X]) :
    aeval Φ p β = p.eval 1 • β := by
  by_cases h0 : β = 0
  · simp [h0]
  · apply Module.End.aeval_apply_of_hasEigenvector
    refine ⟨?_, h0⟩
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact hβ

/-- The stable-limit identity `r(1) • β = r(Φ) β₀` for any annihilating
polynomial `(X - 1)^k r` of `Φ`. -/
theorem eval_one_smul_eq_aeval_of_stableLimit (hD : ∀ l ∈ D, l ∘ₗ Φ ∈ D)
    (hsep : ∀ x : E, (∀ l ∈ D, l x = 0) → x = 0) {β₀ β : E}
    (hlim : ∀ l ∈ D, Tendsto (fun n => l ((Φ ^ n) β₀)) atTop (𝓝 (l β)))
    {k : ℕ} {r : ℂ[X]} (hann : aeval Φ ((X - C 1) ^ k * r) = 0) :
    r.eval 1 • β = aeval Φ r β₀ := by
  have hfix := stableLimit_fixed Φ D hD hsep hlim
  have hβ := aeval_apply_of_fixed Φ hfix r
  have hpowfix : ∀ n : ℕ, (Φ ^ n) β = β := by
    intro n
    induction n with
    | zero => simp
    | succ n ihn => rw [pow_succ', Module.End.mul_apply, ihn, hfix]
  have hy : aeval Φ r (β₀ - β) = 0 := by
    apply eq_zero_of_unipotent_of_tendsto_zero Φ D hD hsep k
    · have h := LinearMap.congr_fun hann (β₀ - β)
      rw [map_mul, Module.End.mul_apply, map_pow, map_sub, aeval_X, aeval_C,
        Algebra.algebraMap_eq_smul_one, one_smul] at h
      simpa using h
    · intro l hl
      have hl' : l ∘ₗ aeval Φ r ∈ D := comp_aeval_mem Φ D hD r hl
      have ht := ((hlim _ hl').sub_const ((l ∘ₗ aeval Φ r) β))
      rw [sub_self] at ht
      have hcomm : ∀ n : ℕ, Φ ^ n * aeval Φ r = aeval Φ r * Φ ^ n := by
        intro n
        rw [← aeval_X_pow (R := ℂ), ← map_mul, ← map_mul, mul_comm]
      refine ht.congr fun n => ?_
      have h1 : (Φ ^ n) ((aeval Φ r) (β₀ - β)) =
          (aeval Φ r) ((Φ ^ n) β₀) - (aeval Φ r) β := by
        rw [← Module.End.mul_apply, hcomm n, Module.End.mul_apply, map_sub, hpowfix, map_sub]
      rw [h1, map_sub]
      rfl
  rw [map_sub, sub_eq_zero] at hy
  rw [← hβ, hy]

end StableLimit

section Bilinear

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]

/-- Simultaneous precomposition of a bilinear form in both arguments. -/
def bilinearPrecomp (T : Module.End ℂ W) (S : Module.End ℂ Y) :
    Module.End ℂ (W →ₗ[ℂ] Y →ₗ[ℂ] ℂ) where
  toFun β := β.compl₁₂ T S
  map_add' _ _ := by
    ext
    rfl
  map_smul' _ _ := by
    ext
    rfl

@[simp]
theorem bilinearPrecomp_apply (T : Module.End ℂ W) (S : Module.End ℂ Y)
    (β : W →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (w : W) (y : Y) :
    bilinearPrecomp T S β w y = β (T w) (S y) := rfl

theorem bilinearPrecomp_pow_apply (T : Module.End ℂ W) (S : Module.End ℂ Y)
    (β : W →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (n : ℕ) (w : W) (y : Y) :
    (bilinearPrecomp T S ^ n) β w y = β ((T ^ n) w) ((S ^ n) y) := by
  induction n generalizing w y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, bilinearPrecomp_apply, ih, pow_succ, pow_succ,
      Module.End.mul_apply, Module.End.mul_apply]

/-- Evaluation of bilinear forms at one pair of vectors. -/
def bilinearEval (w : W) (y : Y) : Module.Dual ℂ (W →ₗ[ℂ] Y →ₗ[ℂ] ℂ) where
  toFun β := β w y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The span of all pair evaluations. -/
def bilinearEvalSpan : Submodule ℂ (Module.Dual ℂ (W →ₗ[ℂ] Y →ₗ[ℂ] ℂ)) :=
  Submodule.span ℂ (Set.range fun p : W × Y => bilinearEval p.1 p.2)

theorem bilinearEvalSpan_comp_mem (T : Module.End ℂ W) (S : Module.End ℂ Y) :
    ∀ l ∈ (bilinearEvalSpan : Submodule ℂ (Module.Dual ℂ (W →ₗ[ℂ] Y →ₗ[ℂ] ℂ))),
      l ∘ₗ bilinearPrecomp T S ∈ (bilinearEvalSpan : Submodule ℂ _) := by
  intro l hl
  induction hl using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨w, y⟩, rfl⟩ := hx
    have : bilinearEval w y ∘ₗ bilinearPrecomp T S = bilinearEval (T w) (S y) := by
      ext β
      rfl
    rw [this]
    exact Submodule.subset_span ⟨(T w, S y), rfl⟩
  | zero => simp
  | add x z _ _ hx hz =>
    rw [LinearMap.add_comp]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    rw [LinearMap.smul_comp]
    exact Submodule.smul_mem _ c hx

theorem bilinearEvalSpan_separates (β : W →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (h : ∀ l ∈ (bilinearEvalSpan : Submodule ℂ (Module.Dual ℂ (W →ₗ[ℂ] Y →ₗ[ℂ] ℂ))),
      l β = 0) : β = 0 := by
  ext w y
  exact h _ (Submodule.subset_span ⟨(w, y), rfl⟩)

theorem bilinearEvalSpan_tendsto (T : Module.End ℂ W) (S : Module.End ℂ Y)
    {β₀ β : W →ₗ[ℂ] Y →ₗ[ℂ] ℂ}
    (hlim : ∀ w y, Tendsto (fun n => β₀ ((T ^ n) w) ((S ^ n) y)) atTop (𝓝 (β w y))) :
    ∀ l ∈ (bilinearEvalSpan : Submodule ℂ (Module.Dual ℂ (W →ₗ[ℂ] Y →ₗ[ℂ] ℂ))),
      Tendsto (fun n => l ((bilinearPrecomp T S ^ n) β₀)) atTop (𝓝 (l β)) := by
  intro l hl
  induction hl using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨w, y⟩, rfl⟩ := hx
    have hfun : (fun n => bilinearEval w y ((bilinearPrecomp T S ^ n) β₀)) =
        fun n => β₀ ((T ^ n) w) ((S ^ n) y) := by
      funext n
      exact bilinearPrecomp_pow_apply T S β₀ n w y
    rw [hfun]
    exact hlim w y
  | zero => simp
  | add x z _ _ hx hz => simpa using hx.add hz
  | smul c x _ hx => simpa using hx.const_mul c

end Bilinear

namespace UnramifiedOperatorFamily

section Families

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)} {Ω : Set (unramifiedCharacters ν)}
  {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- Evaluation of the concrete regular algebra at one actual character. -/
def regularEval (χ : unramifiedCharacters ν) : unramifiedRegularFunctions ν →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : unramifiedCharacters ν => ℂ) χ).comp
    (unramifiedRegularFunctions ν).val

@[simp]
theorem regularEval_apply (χ : unramifiedCharacters ν) (b : unramifiedRegularFunctions ν) :
    regularEval χ b = b.val χ := rfl

theorem isPolynomialOn_zero : IsPolynomialOn Ω (fun _ => (0 : E)) := by
  simpa using isPolynomialOn_const (U := Ω) (0 : E)

/-- Finite sums of polynomial families are polynomial. -/
theorem isPolynomialOn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → E)
    (hf : ∀ i ∈ s, IsPolynomialOn Ω (f i)) :
    IsPolynomialOn Ω (fun χ => ∑ i ∈ s, f i χ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isPolynomialOn_zero (Ω := Ω) (E := E))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Applying a polynomial endomorphism family to a polynomial vector family. -/
theorem IsPolynomialOn.endApply {Φ : Ω → Module.End ℂ E} {y : Ω → E}
    (hΦ : IsPolynomialOn Ω Φ) (hy : IsPolynomialOn Ω y) :
    IsPolynomialOn Ω (fun χ => Φ χ (y χ)) := by
  obtain ⟨n, c, T, hΦ⟩ := hΦ
  have heq : (fun χ => Φ χ (y χ)) = fun χ => ∑ i, (c i).val χ.val • T i (y χ) := by
    funext χ
    rw [hΦ χ, LinearMap.sum_apply]
    rfl
  rw [heq]
  exact isPolynomialOn_finset_sum _ _ fun i _ => (hy.linearMap (T i)).regular_smul (c i)

/-- Iterates of a polynomial endomorphism family on a fixed vector. -/
theorem IsPolynomialOn.pow_apply {Φ : Ω → Module.End ℂ E}
    (hΦ : IsPolynomialOn Ω Φ) (v : E) (n : ℕ) :
    IsPolynomialOn Ω (fun χ => (Φ χ ^ n) v) := by
  induction n with
  | zero => simpa using isPolynomialOn_const (U := Ω) v
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    exact hΦ.endApply ih

/-- Composition of two polynomial endomorphism families. -/
theorem IsPolynomialOn.mul {A B : Ω → Module.End ℂ E}
    (hA : IsPolynomialOn Ω A) (hB : IsPolynomialOn Ω B) :
    IsPolynomialOn Ω (fun χ => A χ * B χ) := by
  obtain ⟨n, c, T, hA⟩ := hA
  have heq : (fun χ => A χ * B χ) = fun χ => ∑ i, (c i).val χ.val • (T i * B χ) := by
    funext χ
    rw [hA χ, Finset.sum_mul]
    simp only [smul_mul_assoc]
  rw [heq]
  refine isPolynomialOn_finset_sum _ _ fun i _ => ?_
  exact (hB.linearMap (LinearMap.mulLeft ℂ (T i))).regular_smul (c i)

/-- Bilinear precomposition of two polynomial families is polynomial. -/
theorem IsPolynomialOn.bilinearPrecomp {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    {T : Ω → Module.End ℂ W} {S : Ω → Module.End ℂ Y}
    (hT : IsPolynomialOn Ω T) (hS : IsPolynomialOn Ω S) :
    IsPolynomialOn Ω (fun χ => Langlands.Plancherel.bilinearPrecomp (T χ) (S χ)) := by
  have hT' : IsPolynomialOn Ω
      (fun χ => Langlands.Plancherel.bilinearPrecomp (T χ) (1 : Module.End ℂ Y)) := by
    obtain ⟨n, c, A, hA⟩ := hT
    refine ⟨n, c, fun i => Langlands.Plancherel.bilinearPrecomp (A i) 1, fun χ => ?_⟩
    ext β w y
    simp [hA χ, LinearMap.sum_apply, map_sum, map_smul]
  have hS' : IsPolynomialOn Ω
      (fun χ => Langlands.Plancherel.bilinearPrecomp (1 : Module.End ℂ W) (S χ)) := by
    obtain ⟨n, c, A, hA⟩ := hS
    refine ⟨n, c, fun i => Langlands.Plancherel.bilinearPrecomp 1 (A i), fun χ => ?_⟩
    ext β w y
    simp [hA χ, LinearMap.sum_apply, map_sum, map_smul]
  have heq : (fun χ => Langlands.Plancherel.bilinearPrecomp (T χ) (S χ)) =
      fun χ => Langlands.Plancherel.bilinearPrecomp (T χ) (1 : Module.End ℂ Y) *
        Langlands.Plancherel.bilinearPrecomp (1 : Module.End ℂ W) (S χ) := by
    funext χ
    ext β w y
    rfl
  rw [heq]
  exact hT'.mul hS'

/-- A regular polynomial, specialized at each parameter and applied through a
polynomial endomorphism family to a fixed vector, is polynomial. -/
theorem IsPolynomialOn.aeval_map_apply {Φ : Ω → Module.End ℂ E}
    (hΦ : IsPolynomialOn Ω Φ) (q : (unramifiedRegularFunctions ν)[X]) (v : E) :
    IsPolynomialOn Ω (fun χ =>
      aeval (Φ χ) (q.map (regularEval χ.val).toRingHom) v) := by
  have hdeg : ∀ χ : Ω, (q.map (regularEval χ.val).toRingHom).natDegree < q.natDegree + 1 :=
    fun χ => Nat.lt_succ_of_le (natDegree_map_le)
  have heq : (fun χ : Ω => aeval (Φ χ) (q.map (regularEval χ.val).toRingHom) v) =
      fun χ => ∑ i ∈ Finset.range (q.natDegree + 1),
        (q.coeff i).val χ.val • (Φ χ ^ i) v := by
    funext χ
    rw [aeval_eq_sum_range' (hdeg χ), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, LinearMap.smul_apply]
    rfl
  rw [heq]
  exact isPolynomialOn_finset_sum _ _ fun i _ => (hΦ.pow_apply v i).regular_smul (q.coeff i)

/-- A polynomial endomorphism family on a finite-dimensional space has one monic
regular polynomial annihilating every specialization. -/
theorem IsPolynomialOn.exists_monic_annihilator [FiniteDimensional ℂ E]
    {Φ : Ω → Module.End ℂ E} (hΦ : IsPolynomialOn Ω Φ) :
    ∃ P : (unramifiedRegularFunctions ν)[X], P.Monic ∧
      ∀ χ : Ω, aeval (Φ χ) (P.map (regularEval χ.val).toRingHom) = 0 := by
  classical
  obtain ⟨n, c, T, hΦ⟩ := hΦ
  let bE := Module.finBasis ℂ E
  let MB : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E))
      (unramifiedRegularFunctions ν) :=
    ∑ i, c i • (LinearMap.toMatrix bE bE (T i)).map (algebraMap ℂ (unramifiedRegularFunctions ν))
  refine ⟨MB.charpoly, Matrix.charpoly_monic MB, fun χ => ?_⟩
  have hmat : MB.map (regularEval χ.val).toRingHom = LinearMap.toMatrix bE bE (Φ χ) := by
    ext a b
    rw [hΦ χ, map_sum]
    simp only [MB, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum,
      smul_eq_mul, map_mul, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change regularEval χ.val (c i) * regularEval χ.val (algebraMap ℂ _ _) = _
    rw [AlgHom.commutes]
    rfl
  rw [← Matrix.charpoly_map, hmat, LinearMap.charpoly_toMatrix]
  exact LinearMap.aeval_self_charpoly _

/-- One nonzero regular scalar precedes every starting vector: weak stable
limits of a regular finite-dimensional endomorphism family become polynomial
after multiplication by it. -/
theorem IsPolynomialOn.exists_regular_stableLimit_numerator [FiniteDimensional ℂ E]
    {Φ : Ω → Module.End ℂ E} (hΦ : IsPolynomialOn Ω Φ)
    (D : Submodule ℂ (Module.Dual ℂ E)) (hD : ∀ χ : Ω, ∀ l ∈ D, l ∘ₗ Φ χ ∈ D)
    (hsep : ∀ x : E, (∀ l ∈ D, l x = 0) → x = 0) :
    ∃ b : unramifiedRegularFunctions ν, b ≠ 0 ∧
      ∀ (β₀ : E) (β : Ω → E),
        (∀ χ : Ω, ∀ l ∈ D, Tendsto (fun n => l ((Φ χ ^ n) β₀)) atTop (𝓝 (l (β χ)))) →
        IsPolynomialOn Ω (fun χ => b.val χ.val • β χ) := by
  have : Nonempty (unramifiedCharacters ν) := ⟨1⟩
  obtain ⟨P, hPm, hP⟩ := hΦ.exists_monic_annihilator
  obtain ⟨q, hq, hndvd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hPm.ne_zero 1
  refine ⟨q.eval 1, fun h0 => hndvd (dvd_iff_isRoot.mpr h0), ?_⟩
  intro β₀ β hlim
  have hpt : ∀ χ : Ω, (q.eval 1).val χ.val • β χ =
      aeval (Φ χ) (q.map (regularEval χ.val).toRingHom) β₀ := by
    intro χ
    have hann : aeval (Φ χ) ((X - C 1) ^ P.rootMultiplicity 1 *
        q.map (regularEval χ.val).toRingHom) = 0 := by
      have h := hP χ
      rw [hq, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
        map_one] at h
      exact h
    have h := eval_one_smul_eq_aeval_of_stableLimit (Φ χ) D (hD χ) hsep (hlim χ) hann
    rw [eval_one_map] at h
    exact h
  have heq : (fun χ : Ω => (q.eval 1).val χ.val • β χ) =
      fun χ => aeval (Φ χ) (q.map (regularEval χ.val).toRingHom) β₀ := funext hpt
  rw [heq]
  exact hΦ.aeval_map_apply q β₀

/-- Bilinear version: one nonzero regular scalar precedes every starting form.
If iterated simultaneous precompositions converge pointwise, the limiting
forms become polynomial after multiplication by that scalar. -/
theorem exists_regular_bilinear_stableLimit_numerator
    {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {Y : Type uY} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    {T : Ω → Module.End ℂ W} {S : Ω → Module.End ℂ Y}
    (hT : IsPolynomialOn Ω T) (hS : IsPolynomialOn Ω S) :
    ∃ b : unramifiedRegularFunctions ν, b ≠ 0 ∧
      ∀ (β₀ : W →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (β : Ω → W →ₗ[ℂ] Y →ₗ[ℂ] ℂ),
        (∀ χ w y, Tendsto (fun n => β₀ ((T χ ^ n) w) ((S χ ^ n) y)) atTop
          (𝓝 (β χ w y))) →
        IsPolynomialOn Ω (fun χ => b.val χ.val • β χ) := by
  obtain ⟨b, hb, hpoly⟩ := (hT.bilinearPrecomp hS).exists_regular_stableLimit_numerator
    bilinearEvalSpan (fun χ => bilinearEvalSpan_comp_mem (T χ) (S χ))
    bilinearEvalSpan_separates
  exact ⟨b, hb, fun β₀ β hlim =>
    hpoly β₀ β fun χ => bilinearEvalSpan_tendsto (T χ) (S χ) (hlim χ)⟩

end Families

end UnramifiedOperatorFamily

end Langlands.Plancherel
