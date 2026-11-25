/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Filtration

/-!
# Perfect pairings over a field from integral pairings with finite-level control

Let `R` be a principal ideal domain (in practice `ℤ_ℓ`), `ϖ ∈ R` a nonzero nonunit (`ℓ`) and
`P : A × B ⟶ R` a bilinear pairing of finitely generated `R`-modules (in practice the integral
cohomology groups `Hⁱ(X, ℤ_ℓ) × H^{2d-i}(X, ℤ_ℓ) ⟶ ℤ_ℓ` of a Poincaré pairing). This file
proves that the extension of `P` to a field `K ⊇ R` (in practice `ℚ̄_ℓ`) is a perfect pairing
as soon as `P` is perfect at a single finite level `R/ϖᵐ` up to a bounded defect:

* if `P` reduces at level `m` to a pairing `E × F ⟶ M` whose left adjoint is injective, along
  maps `ρ : A ⟶ E`, `σ : B ⟶ F` with `ker ρ ⊆ ϖᵐ A` and `ϖᵉ F ⊆ σ(B)` for some `e < m`, then the
  left kernel of `P` is torsion (`LinearMap.mem_torsion_of_finiteLevel`);
* if the left and right kernels of `P` are torsion, the extension of `P` to `K`-vector spaces
  spanned by the images of `A` and `B` is perfect (`LinearMap.isPerfPair_of_span_eq_top`).

The hypotheses on `ρ` hold for the reduction `ρ : Hⁱ(X, ℤ_ℓ) ⟶ Hⁱ(X, ℤ/ℓᵐ)` of `ℓ`-adic
cohomology, by the Bockstein sequence
`Hⁱ(X, ℤ_ℓ) --ℓᵐ--> Hⁱ(X, ℤ_ℓ) --ρ--> Hⁱ(X, ℤ/ℓᵐ) --δ--> Hⁱ⁺¹(X, ℤ_ℓ)`, as soon as `ℓᵉ` kills the
`ℓ`-power torsion of `Hⁱ⁺¹(X, ℤ_ℓ)` (`LinearMap.exists_eq_pow_smul_of_exact`,
`LinearMap.pow_smul_mem_range_of_exact`, `Submodule.exists_pow_smul_eq_zero_of_isNoetherian`).
This is the linear algebra by which the perfectness of the finite-level Poincaré pairings is
transported to `ℚ̄_ℓ`-coefficients (blueprint `theorem-poincare-duality--6`).
-/

@[expose] public section

open Function

namespace Submodule

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- In a Noetherian module, the `ϖ`-power torsion is killed by a single power of `ϖ`. -/
theorem exists_pow_smul_eq_zero_of_isNoetherian [IsNoetherian R A] (ϖ : R) :
    ∃ e : ℕ, ∀ x : A, (∃ n : ℕ, ϖ ^ n • x = 0) → ϖ ^ e • x = 0 := by
  classical
  let T : Submodule R A := torsion' R A (Submonoid.powers ϖ)
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian T
  have hgen (x : A) (hx : x ∈ s) : ∃ n : ℕ, ϖ ^ n • x = 0 := by
    obtain ⟨⟨_, n, rfl⟩, h⟩ := (hs ▸ subset_span hx : x ∈ T)
    exact ⟨n, h⟩
  choose! n hn using hgen
  have hspan (y : A) (hy : y ∈ span R (s : Set A)) : ϖ ^ s.sup n • y = 0 := by
    induction hy using span_induction with
    | mem y hy =>
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) hy)
      rw [hd, pow_add, mul_comm, mul_smul, hn y hy, smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul r y _ hy => rw [smul_comm, hy, smul_zero]
  refine ⟨s.sup n, fun x ⟨k, hk⟩ ↦ hspan x ?_⟩
  rw [hs]
  exact ⟨⟨ϖ ^ k, k, rfl⟩, hk⟩

end Submodule

namespace LinearMap

variable {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

section FiniteLevel

variable {E F M : Type*} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup M] [Module R M]

/-- **Finite-level step.** Let `Pₘ : E × F ⟶ M` have injective left adjoint and let
`σ : B ⟶ F` have image containing `r • F`. If `x ∈ E` pairs to zero with `σ(B)`, then
`r • x = 0`. -/
theorem smul_eq_zero_of_pairing_eq_zero (Pm : E →ₗ[R] F →ₗ[R] M) (hPm : Injective Pm)
    {σ : B →ₗ[R] F} {r : R} (hσ : ∀ y : F, r • y ∈ range σ) {x : E}
    (hx : ∀ b, Pm x (σ b) = 0) : r • x = 0 := by
  refine hPm (LinearMap.ext fun y ↦ ?_)
  obtain ⟨b, hb⟩ := hσ y
  rw [map_smul, smul_apply, ← map_smul, ← hb, hx, map_zero, zero_apply]

/-- **Reduction of the left kernel.** Let `P : A × B ⟶ R` reduce, along `ρ : A ⟶ E`,
`σ : B ⟶ F` and `φ : R ⟶ M`, to a pairing `Pₘ : E × F ⟶ M` with injective left adjoint. If
`ker ρ ⊆ ϖᵐ A` and `ϖᵉ F ⊆ σ(B)`, then `ϖᵉ` maps the left kernel of `P` into `ϖᵐ A`. -/
theorem exists_pow_smul_eq_of_pairing (P : A →ₗ[R] B →ₗ[R] R) (Pm : E →ₗ[R] F →ₗ[R] M)
    (hPm : Injective Pm) (ρ : A →ₗ[R] E) (σ : B →ₗ[R] F) (φ : R →ₗ[R] M)
    (hcompat : ∀ a b, Pm (ρ a) (σ b) = φ (P a b)) {ϖ : R} {e m : ℕ}
    (hker : ∀ a, ρ a = 0 → ∃ a', a = ϖ ^ m • a') (hrange : ∀ y : F, ϖ ^ e • y ∈ range σ)
    {a : A} (ha : P a = 0) : ∃ a', ϖ ^ e • a = ϖ ^ m • a' := by
  refine hker _ ?_
  rw [map_smul]
  exact smul_eq_zero_of_pairing_eq_zero Pm hPm hrange fun b ↦ by
    rw [hcompat, ha, zero_apply, map_zero]

/-- The kernel of `ρ` is `ϖᵐ A` when `A --ϖᵐ--> A --ρ--> E` is exact (the first part of the
Bockstein sequence). -/
theorem exists_eq_pow_smul_of_exact {ϖ : R} {m : ℕ} {ρ : A →ₗ[R] E}
    (hexact : Exact (fun a : A ↦ ϖ ^ m • a) ρ) {a : A} (ha : ρ a = 0) :
    ∃ a', a = ϖ ^ m • a' := by
  obtain ⟨a', rfl⟩ := (hexact a).1 ha
  exact ⟨a', rfl⟩

/-- The image of `ρ` contains `ϖᵉ E` when `A --ρ--> E --δ--> A'` is exact, `E` is killed by
`ϖᵐ` and `ϖᵉ` kills the `ϖ`-power torsion of `A'` (the second part of the Bockstein
sequence). -/
theorem pow_smul_mem_range_of_exact {A' : Type*} [AddCommGroup A'] [Module R A'] {ϖ : R}
    {m e : ℕ} {ρ : A →ₗ[R] E} {δ : E →ₗ[R] A'} (hexact : Exact ρ δ)
    (hE : ∀ y : E, ϖ ^ m • y = 0) (hA' : ∀ x : A', (∃ n : ℕ, ϖ ^ n • x = 0) → ϖ ^ e • x = 0)
    (y : E) : ϖ ^ e • y ∈ range ρ := by
  refine (hexact _).1 ?_
  rw [map_smul]
  exact hA' _ ⟨m, by rw [← map_smul, hE, map_zero]⟩

end FiniteLevel

section Torsion

variable [IsDomain R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- A torsion element of `A` pairs to zero with everything: `R` is a domain. -/
theorem apply_eq_zero_of_mem_torsion (P : A →ₗ[R] B →ₗ[R] R) {a : A}
    (ha : a ∈ Submodule.torsion R A) : P a = 0 := by
  obtain ⟨⟨r, hr⟩, hra⟩ := ha
  ext b
  have hra' : r • a = 0 := hra
  have h : r * P a b = 0 := by
    rw [← smul_eq_mul, ← smul_apply, ← map_smul, hra', map_zero, zero_apply]
  exact (mul_eq_zero.1 h).resolve_left (nonZeroDivisors.ne_zero hr)

/-- **Torsion left kernel.** Let `P : A × B ⟶ R` be a pairing over a Noetherian domain, with
`A` finitely generated, and `ϖ` a nonzero nonunit. If `ϖᵉ` maps the left kernel of `P` into
`ϖᵐ A` for some `e < m`, then the left kernel of `P` is torsion.

Indeed the left kernel is saturated, so if it contained a non-torsion element it would contain
one whose image in the free module `A/torsion` is not divisible by `ϖ`, by Krull's intersection
theorem; but `ϖᵉ x ∈ ϖᵐ A` forces that image to be divisible by `ϖ^{m-e}`. -/
theorem mem_torsion_of_pow_smul_eq [Module.Finite R A] (P : A →ₗ[R] B →ₗ[R] R) {ϖ : R}
    (hϖ : ¬IsUnit ϖ) (hϖ0 : ϖ ≠ 0) {e m : ℕ} (hem : e < m)
    (h : ∀ a, P a = 0 → ∃ a', ϖ ^ e • a = ϖ ^ m • a') {a : A} (ha : P a = 0) :
    a ∈ Submodule.torsion R A := by
  classical
  set T := Submodule.torsion R A
  set π := T.mkQ
  by_contra hna
  have hπa : π a ≠ 0 := by rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  set I : Ideal R := Ideal.span {ϖ}
  have hI : I ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  have hmem (n : ℕ) (x : A ⧸ T) : x ∈ I ^ n • (⊤ : Submodule R (A ⧸ T)) ↔
      ∃ y, x = ϖ ^ n • y := by
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, _, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, trivial, hy.symm⟩⟩
  -- Krull: `π a` is not divisible by every power of `ϖ`
  have hex : ∃ n, ¬ π a ∈ I ^ n • (⊤ : Submodule R (A ⧸ T)) := by
    by_contra! hall
    have := (Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree (M := A ⧸ T) I hI).le
      (Submodule.mem_iInf _ |>.2 hall)
    exact hπa ((Submodule.mem_bot R).1 this)
  set n₀ := Nat.find hex
  have hn₀ : n₀ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [show Nat.find hex = 0 from h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul] at this
    exact this trivial
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
  obtain ⟨f₀, hf₀⟩ := (hmem s _).1 (not_not.1 (Nat.find_min hex (by omega : s < n₀)))
  have hf₀' : ¬ ∃ y, f₀ = ϖ • y := by
    rintro ⟨y, rfl⟩
    have := Nat.find_spec hex
    refine this ((hmem _ _).2 ⟨y, ?_⟩)
    rw [show Nat.find hex = s + 1 from hs, hf₀, smul_smul, pow_succ]
  -- a lift `f` of `f₀` lies in the left kernel, the latter being saturated
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective T f₀
  have hdiff : ϖ ^ s • f - a ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
    rw [sub_eq_zero]
    exact hf₀.symm
  obtain ⟨⟨r, hr⟩, hrd⟩ := hdiff
  have hrd' : r • (ϖ ^ s • f - a) = 0 := hrd
  have hPf : P f = 0 := by
    have h1 : (r * ϖ ^ s) • P f = 0 := by
      rw [← map_smul, mul_smul, ← sub_add_cancel (ϖ ^ s • f) a, smul_add, map_add, hrd',
        map_zero, zero_add, map_smul, ha, smul_zero]
    have hne : r * ϖ ^ s ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hr) (pow_ne_zero _ hϖ0)
    exact (smul_eq_zero.1 h1).resolve_left hne
  obtain ⟨f', hf'⟩ := h f hPf
  -- in the torsion-free quotient, `ϖᵉ π f = ϖᵐ π f'` gives `π f = ϖ^{m-e} π f'`
  apply hf₀'
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hem
  refine ⟨ϖ ^ d • π f', smul_right_injective (A ⧸ T) (pow_ne_zero e hϖ0) ?_⟩
  have h2 := congrArg π hf'
  rw [map_smul, map_smul] at h2
  simp only [smul_smul, ← pow_succ', ← pow_add] at h2 ⊢
  rw [h2, add_assoc]

/-- **Torsion left kernel from a single finite level.** If `P : A × B ⟶ R` reduces, along
`ρ : A ⟶ E` and `σ : B ⟶ F`, to a pairing with injective left adjoint, where `ker ρ ⊆ ϖᵐ A`
and `ϖᵉ F ⊆ σ(B)` with `e < m`, then the left kernel of `P` is torsion. -/
theorem mem_torsion_of_finiteLevel {E F M : Type*} [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M] [Module.Finite R A]
    (P : A →ₗ[R] B →ₗ[R] R) (Pm : E →ₗ[R] F →ₗ[R] M) (hPm : Injective Pm) (ρ : A →ₗ[R] E)
    (σ : B →ₗ[R] F) (φ : R →ₗ[R] M) (hcompat : ∀ a b, Pm (ρ a) (σ b) = φ (P a b)) {ϖ : R}
    (hϖ : ¬IsUnit ϖ) (hϖ0 : ϖ ≠ 0) {e m : ℕ} (hem : e < m)
    (hker : ∀ a, ρ a = 0 → ∃ a', a = ϖ ^ m • a') (hrange : ∀ y : F, ϖ ^ e • y ∈ range σ)
    {a : A} (ha : P a = 0) : a ∈ Submodule.torsion R A :=
  mem_torsion_of_pow_smul_eq P hϖ hϖ0 hem
    (fun _ ha' ↦ exists_pow_smul_eq_of_pairing P Pm hPm ρ σ φ hcompat hker hrange ha') ha

end Torsion

section Field

variable [IsDomain R] [IsPrincipalIdealRing R] {K V W : Type*} [Field K] [Algebra R K]
  [FaithfulSMul R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

omit [IsPrincipalIdealRing R] [Module K V] [Module R V] [IsScalarTower R K V] in
/-- A torsion element is killed by an `R`-linear map to a `K`-vector space. -/
theorem map_eq_zero_of_mem_torsion (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
    [Module K V] [Module R V] [IsScalarTower R K V] (ι : A →ₗ[R] V) {a : A}
    (ha : a ∈ Submodule.torsion R A) :
    ι a = 0 := by
  obtain ⟨⟨r, hr⟩, hra⟩ := ha
  have h : algebraMap R K r • ι a = 0 := by
    have hra' : r • a = 0 := hra
    rw [algebraMap_smul, ← map_smul, hra', map_zero]
  refine (smul_eq_zero.1 h).resolve_left ?_
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).2 (nonZeroDivisors.ne_zero hr)

omit [IsScalarTower R K W] in
/-- **One-sided perfectness over `K`.** Let `P : A × B ⟶ R` be a pairing of finitely generated
modules over a PID with torsion left kernel, and `Q : V × W ⟶ K` a pairing of `K`-vector spaces
extending it along `ι : A ⟶ V`, `κ : B ⟶ W`, where `ι(A)` spans `V`. Then the left adjoint of
`Q` is injective. -/
theorem injective_of_span_eq_top [Module.Finite R A] [Module.Finite R B] (ι : A →ₗ[R] V)
    (κ : B →ₗ[R] W) (hι : Submodule.span K (Set.range ι) = ⊤) (P : A →ₗ[R] B →ₗ[R] R)
    (Q : V →ₗ[K] W →ₗ[K] K) (hQ : ∀ a b, Q (ι a) (κ b) = algebraMap R K (P a b))
    (hl : ∀ a, P a = 0 → a ∈ Submodule.torsion R A) : Injective Q := by
  classical
  -- bases of the free quotients `A/torsion` and `B/torsion`, and lifts of their elements
  let TA := Submodule.torsion R A
  let TB := Submodule.torsion R B
  let bA := Module.Free.chooseBasis R (A ⧸ TA)
  let bB := Module.Free.chooseBasis R (B ⧸ TB)
  let a (i : Module.Free.ChooseBasisIndex R (A ⧸ TA)) : A :=
    (Submodule.mkQ_surjective TA (bA i)).choose
  have ha (i) : TA.mkQ (a i) = bA i := (Submodule.mkQ_surjective TA (bA i)).choose_spec
  let b (j : Module.Free.ChooseBasisIndex R (B ⧸ TB)) : B :=
    (Submodule.mkQ_surjective TB (bB j)).choose
  have hb (j) : TB.mkQ (b j) = bB j := (Submodule.mkQ_surjective TB (bB j)).choose_spec
  -- every element is a combination of the lifts, up to torsion
  have hdecA (x : A) : x - ∑ i, bA.repr (TA.mkQ x) i • a i ∈ TA := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, ha, Module.Basis.sum_repr, sub_self]
  have hdecB (y : B) : y - ∑ j, bB.repr (TB.mkQ y) j • b j ∈ TB := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hb, Module.Basis.sum_repr, sub_self]
  -- the rows of the Gram matrix are linearly independent over `R`
  have hrows : LinearIndependent R (fun i j ↦ P (a i) (b j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set x := ∑ i, c i • a i
    have hx : P x = 0 := by
      ext y
      have hy := apply_eq_zero_of_mem_torsion P.flip (hdecB y)
      have hPy : P x y = ∑ j, bB.repr (TB.mkQ y) j * P x (b j) := by
        have := congr($hy x)
        simp only [map_sub, map_sum, map_smul, flip_apply, sub_apply, LinearMap.sum_apply,
          smul_apply, zero_apply, sub_eq_zero] at this
        simpa [smul_eq_mul] using this
      rw [hPy, zero_apply]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hj := congr_fun hc j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
      have : P x (b j) = 0 := by
        simp only [x, map_sum, map_smul, LinearMap.sum_apply, smul_apply, smul_eq_mul]
        exact hj
      rw [this, mul_zero]
    have hx0 : TA.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hl x hx
    have : ∑ i, c i • bA i = 0 := by
      rw [← hx0]
      simp [x, map_sum, map_smul, ha]
    exact Fintype.linearIndependent_iff.1 bA.linearIndependent c this
  have hrowsK := (linearIndependent_algebraMap_comp_iff (S := K)).2 hrows
  -- `V` is spanned by the images of the lifts
  have hspan : ∀ v : V, ∃ c : _ → K, v = ∑ i, c i • ι (a i) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range fun i ↦ ι (a i)) := by
      have hle : Set.range ι ⊆ Submodule.span K (Set.range fun i ↦ ι (a i)) := by
        rintro _ ⟨x, rfl⟩
        have h0 := map_eq_zero_of_mem_torsion K ι (hdecA x)
        rw [map_sub, sub_eq_zero, map_sum] at h0
        rw [h0]
        refine Submodule.sum_mem _ fun i _ ↦ ?_
        rw [map_smul, ← algebraMap_smul K]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have := Submodule.span_le.2 hle
      rw [hι] at this
      exact this trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
    exact ⟨c, hc.symm⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨c, rfl⟩ := hspan v
  have hc : c = 0 := by
    refine funext (Fintype.linearIndependent_iff.1 hrowsK c ?_)
    ext j
    have := congr($((LinearMap.mem_ker).1 hv) (κ (b j)))
    simp only [map_sum, map_smul, LinearMap.sum_apply, smul_apply, hQ, zero_apply,
      smul_eq_mul] at this
    simpa [Finset.sum_apply, Function.comp] using this
  simp [hc]

/-- **Perfectness over `K`.** Let `P : A × B ⟶ R` be a pairing of finitely generated modules
over a PID whose left and right kernels are torsion, and `Q : V × W ⟶ K` a pairing of
`K`-vector spaces extending it along `ι : A ⟶ V`, `κ : B ⟶ W` whose images span. Then `Q` is a
perfect pairing; in particular `V` and `W` are finite-dimensional of the same dimension. -/
theorem isPerfPair_of_span_eq_top [Module.Finite R A] [Module.Finite R B] (ι : A →ₗ[R] V)
    (κ : B →ₗ[R] W) (hι : Submodule.span K (Set.range ι) = ⊤)
    (hκ : Submodule.span K (Set.range κ) = ⊤) (P : A →ₗ[R] B →ₗ[R] R)
    (Q : V →ₗ[K] W →ₗ[K] K) (hQ : ∀ a b, Q (ι a) (κ b) = algebraMap R K (P a b))
    (hl : ∀ a, P a = 0 → a ∈ Submodule.torsion R A)
    (hr : ∀ b, P.flip b = 0 → b ∈ Submodule.torsion R B) : Q.IsPerfPair := by
  have : FiniteDimensional K V := by
    classical
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
    have hle : Set.range ι ⊆ Submodule.span K (ι '' (s : Set A)) := by
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span R (s : Set A) := hs ▸ Submodule.mem_top
      have := Submodule.mem_map_of_mem (f := ι) hx
      rw [Submodule.map_span] at this
      exact Submodule.span_le_restrictScalars R K _ this
    refine Module.finite_def.2 ⟨s.image ι, ?_⟩
    rw [Finset.coe_image]
    exact top_unique (hι ▸ Submodule.span_le.2 hle)
  exact .of_injective (injective_of_span_eq_top ι κ hι P Q hQ hl)
    (injective_of_span_eq_top κ ι hκ P.flip Q.flip (fun b a ↦ hQ a b) hr)

end Field

end LinearMap
