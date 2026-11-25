module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Tactic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The order of vanishing of a norm

All rings are commutative with unit. The data is a ring map `A → B` in which `A` is a Noetherian
local domain of Krull dimension `1` and `A ⊆ B` is a finite extension of domains, so `A → B` is
injective, `B` is an integral domain, and `B` is finite as an `A`-module. Write `K = Frac A` and
`L = Frac B` for the fraction fields, so that `L/K` is a finite field extension.

The main result: for `y ∈ L*` with `x = Nm_{L/K}(y) ∈ K*`, and `m₁, …, m_n` the maximal ideals of
the semi-local ring `B`,

`ord_A(x) = ∑_{i=1}^{n} [κ(mᵢ) : κ(m_A)] · ord_{B_{mᵢ}}(y)`.
-/

@[expose] public section

open Ring

/-! ## The order of vanishing (Stacks 02MD)

Let `R` be a Noetherian local domain of dimension `1` with fraction field `K`. The order of
vanishing `ord_R : K* → ℤ` is the group homomorphism taking a nonzero `r ∈ R` to
`length_R (R / (r))`, extended to `K*` by `ord_R(x/y) = ord_R(x) - ord_R(y)`.

In Mathlib this is `Ring.ordFrac R : K →*₀ WithZero (Multiplicative ℤ)`, a monoid-with-zero
homomorphism sending `0` to `0`. For nonzero `x ∈ K*` the value `Ring.ordFrac R x` is a nonzero
element of `WithZero (Multiplicative ℤ)`, and the integer `ord_R(x)` is recovered by
`Multiplicative.toAdd (WithZero.unzero ...)`. The definition below packages that extraction into
an integer-valued order function.
-/

/-! ### Correctness of `ordInt`

The two statements below characterize `ordInt` as the order of vanishing: it is a group
homomorphism `K* → ℤ`, and on a nonzero `r ∈ R` it equals `length_R (R / (r))`, a length that
is finite under the standing hypotheses.
-/

/-! ### Norms, the local rings of `B`, and residue degrees

For the finite field extension `L/K` and `y ∈ L`, the norm `Nm_{L/K}(y) = det_K(mul_y)` is the
determinant of multiplication by `y` on the `K`-vector space `L`, which is `Algebra.norm K`.

Under the standing hypotheses `B` is semi-local, with finitely many maximal ideals, indexed here
by the finite type `MaximalSpectrum B`. For each `v`, the localization
`B_v = Localization.AtPrime v.asIdeal` is a Noetherian local domain of dimension `1` with
fraction field `L`, so `ord_{B_v}` is defined as above with `R = B_v` and `K = L`.

Let `m_A` be the maximal ideal of `A`. Each maximal ideal `mᵢ` of `B` lies over `m_A`, and the
residue degree `[κ(mᵢ) : κ(m_A)] = finrank_{A/m_A} (B/mᵢ)` is finite; it is
`Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) mᵢ`, which equals
`Module.finrank (A / m_A) (B / mᵢ)` when `mᵢ` lies over `m_A`.
-/

/-! ### The norm-length identity (Stacks 02MI)

For a nonzero `b : B`, the order of vanishing of its norm equals the `A`-length of the cyclic
quotient `B / bB`:

`ord_A (Nm_{L/K}(b)) = length_A (B / bB)`.

Let `μ_b : L → L` be multiplication by `y = algebraMap B L b`, a `K`-linear endomorphism of the
finite `K`-vector space `L`, so that `Nm_{L/K}(y) = det_K(μ_b)` by definition. Since `b` is a
nonzerodivisor of `B`, multiplication by `b` is an injective map `B → B` with cokernel `B/bB` of
finite `A`-length: `B/bB` is a finite `A`-module supported only at `m_A`, being killed by some
power of `m_A` because `dim A = 1` and `b ≠ 0`. The determinant `det_K(μ_b)` is, up to a unit, the
`A`-norm of `b`, an element of `A`, and `ord_A` of it is the length of `A / (Nm b)`.

Concretely, one pushes `Nm_{L/K}(y)` into `A`, as `algebraMap A K (Algebra.norm A b)` via
`Algebra.norm_localization`, applies `ordInt_algebraMap` to turn `ord_A` into
`length_A (A / (Nm b))`, and finally invokes the length identity
`length_A (A / (Nm b)·A) = length_A (B / bB)`.

The route through `Algebra.norm_localization` or `relNorm` is not available here: it needs
`[Module.Free A B]`, respectively `[IsIntegrallyClosed A]`, and `A` is only a one-dimensional
Noetherian local domain while `B` is finite and torsion-free but not free. An additivity-only
strategy is also genuinely insufficient: the discrepancy `D = length − ord ∘ Nm` is an additive
homomorphism vanishing on `A`, which does not force `D ≡ 0`. The decisive content is Stacks
02QH: for a finite `A`-module `M` and an `A`-linear endomorphism `φ` with `det_K(φ ⊗ K) ≠ 0`,
`ord_A(det_K(φ ⊗ K)) = length_A(coker φ)`. It is applied with `M = B` and `φ = lmul_A b`.

The identity is therefore assembled from `ordInt_baseChangeDet_eq_length_cokernel`, the 02QH
determinant-length kernel, and `baseChangeDet_lmul_eq_norm`, identifying the determinant of
`lmul_A b ⊗ K` with `Nm_{L/K}(b)` through the `K`-algebra isomorphism `B ⊗[A] K ≅ L`, together
with the inline identification `range (lmul_A b) = span {b}` making the cokernel `B/bB`.
-/

/-! ### Background on the matrix base case

For a square matrix `T` over a one-dimensional Noetherian local domain `A` with `det T ≠ 0`, the
`A`-length of the cokernel `Aᵐ ⧸ T·Aᵐ` equals `ord_A(det T) = length_A(A/(det T))`.

An additivity-only strategy cannot reach this. The two functions `L(T) = length_A(Aᵐ/T·Aᵐ)` and
`Δ(T) = ord_A(det T)` are both additive under matrix multiplication and agree on scalar matrices
`cI` and on `GLₘ(A)`, but that yields only the single relation `δ(T) + δ(adj T) = 0` for
`δ = L − Δ`, which does not force `δ ≡ 0`; and triangularizing to a pivot would require a
principal ideal domain, which `A` is not. The correct route is a filtration and dévissage
argument, or base change to the completion `Â`, where `ℓ_A(N) = ℓ_Â(N̂)` for finite-length `N`.

The reusable building blocks are: additivity of length along short exact sequences; the
isomorphism `Aᵐ/aAᵐ ≅ (A/aA)ᵐ`, giving `L(aI) = m·ord_A(a)`; multiplicativity
`L(T₁T₂) = L(T₁) + L(T₂)` via `0 → T₁Aᵐ/T₁T₂Aᵐ → Aᵐ/T₁T₂Aᵐ → Aᵐ/T₁Aᵐ → 0` together with the
isomorphism `Aᵐ/T₂Aᵐ ≅ T₁Aᵐ/T₁T₂Aᵐ` for injective `T₁`; and the chain
`(det T)Aᵐ ⊆ TAᵐ ⊆ Aᵐ` with `Matrix.adjugate_mul` and `Matrix.det_adjugate`, giving
`L(T) + L(adj T) = m·ord_A(det T)`.
-/

/-! ### Multiplicativity of the cokernel length under matrix product

For square matrices `T₁ T₂` over a one-dimensional Noetherian local domain `A`, with both
determinants nonzero, so that both `toLin'` are injective over the domain `A`,
`length_A(Aᵐ/range(toLin'(T₁*T₂)))`
`= length_A(Aᵐ/range(toLin' T₁)) + length_A(Aᵐ/range(toLin' T₂))`.
The route: `Matrix.toLin'_mul` turns `toLin'(T₁*T₂)` into the
composition `toLin' T₁ ∘ₗ toLin' T₂`; the nested-submodule SES
`0 → range φ ⧸ range(φ∘ψ) → Aᵐ ⧸ range(φ∘ψ) → Aᵐ ⧸ range φ → 0` (`Module.length_eq_add_of_exact`)
plus the iso `range φ ⧸ range(φ∘ψ) ≅ Aᵐ ⧸ range ψ` (from `LinearEquiv.ofInjective φ` and
`Submodule.Quotient.equiv`) give the additivity.
-/

/-! ### The dévissage step

This is the conceptual crux of the matrix base case, for a block-triangular or, more generally,
`N`-preserving endomorphism.

For an `A`-linear endomorphism `φ` of `M` that maps a submodule `N` into itself (`hφN`), inducing
`φ̄ := N.mapQ N φ hφN` on the quotient `M ⧸ N`, IF `φ̄` is injective then the cokernel length is
additive along the flag `N ⊆ M`:
  `length(M ⧸ range φ) = length(N ⧸ range(φ|_N)) + length((M ⧸ N) ⧸ range φ̄)`.

This comes from the snake lemma applied to `0 → N → M → M ⧸ N → 0` with the `φ`-action: the
boundary map `ker φ̄ → coker(φ|_N)` vanishes because `φ̄` is injective (`ker φ̄ = 0`), leaving the
genuine short exact sequence of cokernels
  `0 → N ⧸ range(φ|_N) → M ⧸ range φ → (M ⧸ N) ⧸ range φ̄ → 0`,
whose additivity (`Module.length_eq_add_of_exact`, in `ℕ∞`, unconditional) gives the identity.
THIS is the piece that defeats the "additivity-only is insufficient" obstruction (it splits the
cokernel along a flag, not merely under a product).  No domain/local/finite-length hypothesis is
needed (the identity holds over any `CommRing`, in `ℕ∞`).
-/

/-! ### Additivity of `length (A ⧸ span{·})` under multiplication

This is the span side of the determinant
relation).  Over a domain `A`, for nonzero `a b`, the SES
`0 → A/span{b} →(·a) A/span{a*b} → A/span{a} → 0` (`Module.length_eq_add_of_exact`) gives
`length (A/span{a*b}) = length (A/span{b}) + length (A/span{a})`.
-/

/-! ### The matrix base case in length form (Stacks 02QH)

For a square matrix `T` over a one-dimensional Noetherian local domain `A` with `T.det ≠ 0`, the
`A`-length of the cokernel of `T : Aᵐ → Aᵐ` equals the `A`-length of `A ⧸ (det T)`.

This is the analytic content of the matrix base case, stated without the `ordInt` and `.toNat`
wrappers so that the proof works purely with `Module.length`, valued in `ℕ∞`, which is additive
over short exact sequences with no finiteness bookkeeping at intermediate steps.

Both sides are multiplicative under matrix product and agree on scalar matrices, and the closure
is an induction on `m` by Schur clearing, needing no Smith normal form or principal ideal domain.
The pieces are: multiplicativity `cokerLen (T₁ * T₂) = cokerLen T₁ + cokerLen T₂`; the scalar
case `cokerLen (a • 1) = m * length (A ⧸ span {a})`; the dévissage step for a block-triangular
`T`, resting on the short exact sequence of cokernels
`0 → coker(φ|_N) → coker φ → coker φ̄ → 0` for an `N`-preserving endomorphism; and the induction
on `m` wiring these together with the Schur clearing `E₋ · T` block-upper-triangular,
`det E₋ = t₁₁ᵐ`, and Schur complement `S = t₁₁ T₀ - w vᵀ` with `det S ≠ 0`, peeled off by
multiplicativity.

Both `cokerLen` and `length (A ⧸ span {det})` are finite, since `det T ≠ 0` makes `toLin' T`
injective over a domain and so the cokernel torsion of finite length, but the `ℕ∞` statement
needs no `.toNat` juggling.
-/

/-! ### The inductive step of `matrix_cokerLen_eq_spanLen`

Given the identity for all `n × n` matrices as induction hypothesis, prove it for an
`(n+1) × (n+1)` matrix `T` with `T.det ≠ 0`. This is the Schur clearing step:

  * Permutation reduction (II.4b): a permutation `P` (an isomorphism, `cokerLen P = 0`, and
    `det P = ±1` a unit so `length (A/span{det P}) = 0`) moves a row with nonzero first entry to
    the top, so WLOG `T 0 0 ≠ 0`.  Peel `P` via `matrix_cokerLen_mul` + `length_span_mul`.
  * Schur clearing: left-multiply `T` by the block-lower-triangular clearing matrix
    `E₋ = [[t₀₀, 0], [-w, t₀₀ • I]]` (`w` the first column below `t₀₀`); `det E₋ = t₀₀^(n+1)` and
    `E₋ T` is block-UPPER-triangular with diagonal blocks `t₀₀²` (a `1×1`) and the Schur
    complement `S = t₀₀ • T₀ - w ⬝ vᵀ ∈ M_n(A)`, with `det (E₋ T) = t₀₀² · det S` and
    `det (E₋ T) = t₀₀^(n+1) · det T`, so `det S ≠ 0`.
  * Block-upper-triangular dévissage (II.4a, via `matrix_cokerLen_devissage` with `N = A·e₀`):
    `cokerLen (E₋ T) = length (A/span{t₀₀²}) + cokerLen S`, and by `IH` on `S`,
    `cokerLen S = length (A/span{det S})`.
  * Recombine on the span side with `length_span_mul` using the two determinant relations.
-/

/-! ## Inputs for the 02QH kernel `ordInt_baseChangeDet_eq_length_cokernel`

The proof works with the integer
**defect** of an injective endomorphism `ψ` of a finite torsion-free `A`-module `N` whose base
change is a `K`-automorphism:

  `Δ(N,ψ) := (length_A (N ⧸ range ψ)).toNat  −  ordInt A (det (ψ.baseChange K))`.

The goal `ordInt_baseChangeDet_eq_length_cokernel` is exactly `Δ(M,φ) = 0`.

The argument (Route γ) is:
* (Lemma C) `Δ` of an endomorphism of a finite-length module is `0` (`length ker = length coker`);
* (Lemma B) `Δ(Aʳ, T) = 0` for a matrix `T` with `det T ≠ 0` — this is the PROVEN matrix base
  case `ordInt_matrix_det_eq_length_cokernel`;
* (Step 1) a full-rank free submodule `F ≅ Aʳ ⊆ M` with finite-length quotient `Q = M/F`;
* (Lemma A) `Δ` is additive over the SES `0 → F → M → Q → 0` when the endomorphism preserves `F`;
* (Step 2) replace `φ` by `ψ = a·φ` (`a ≠ 0 ∈ A`) so that `ψ` preserves `F`; then
  `Δ(M,ψ) = Δ(F,ψ|F) + Δ(Q,ψ̄) = 0 + 0 = 0` (Lemmas A,B,C);
* (Lemma D) the scalar identity `Δ(M, a·id) = 0` (same machinery, A+B+C);
* (comp) `Δ` is additive under composition `Δ(M, a·φ) = Δ(M, a·id) + Δ(M, φ)`,
  hence `Δ(M,φ) = Δ(M,ψ) − Δ(M, a·id) = 0`.

The reusable analytic content is packaged as the four lemmas
`length_ker_eq_length_coker_finiteLength`, `length_quot_smul_eq_rank_mul_ord`,
`exists_fullRank_free_submodule` and `defect_devissage_free`, assembled in the kernel proof.
-/

/-
## Sub-lemma (Step D = Stacks Tag 02M0, Lemma 10.52.12): localization decomposition of length.

For a nonzero `b : B`, the residue-degree-weighted sum of the local orders equals the `A`-length
of `B / bB`:

    Σ_v [κ(m_v):κ(m_A)] · ord_{B_v}(b) = length_A (B / bB).

INFORMAL ARGUMENT. Two ingredients:
(a) For each maximal ideal `m_v` of `B`, `ord_{B_v}(b) = length_{B_v}((B/bB)_{m_v})` by definition
    of `ord` (Definition 1) applied to the 1-dim Noetherian local domain `B_v = B_{m_v}` with
    fraction field `L`: indeed `ord_{B_v}(algebraMap B_v L b) = length_{B_v}(B_v / b·B_v)`
    (`ordInt_algebraMap` for `R = B_v`), and `(B/bB)_{m_v} ≅ B_v / b·B_v`.
(b) Change of rings for length along the residue field: if `M` is a finite-length module over the
    local ring `B_v` with residue field `κ(m_v)`, then `length_A(M) = [κ(m_v):κ(m_A)] ·
    length_{B_v}(M)` — because `A → B_v` is local with residue extension `κ(m_A) → κ(m_v)` of
    degree `[κ(m_v):κ(m_A)] = inertiaDeg`, and length multiplies by the residue degree under such
    a finite local extension (Jordan–Hölder: each `B_v`-composition factor `κ(m_v)` has
    `A`-length `[κ(m_v):κ(m_A)]`). Applied to `M = (B/bB)_{m_v}`:
        length_A((B/bB)_{m_v}) = [κ(m_v):κ(m_A)] · length_{B_v}((B/bB)_{m_v}).
(c) Tag 02M0 (Lemma 10.52.12): a finite-length module over the semilocal `B` is the (finite)
    direct sum of its localizations at the maximal ideals, so length is additive:
        length_A (B/bB) = Σ_v length_A((B/bB)_{m_v}).
    (`B/bB` is Artinian — finite `A`-length, killed by a power of `m_A` — hence its support is the
     finite set of maximal ideals of `B`, and `M ≅ ⊕_v M_{m_v}`.)
Combining (a)+(b)+(c):
    length_A(B/bB) = Σ_v length_A((B/bB)_{m_v}) = Σ_v [κ(m_v):κ(m_A)] · length_{B_v}((B/bB)_{m_v})
                   = Σ_v [κ(m_v):κ(m_A)] · ord_{B_v}(b).
This is a substantial, separable lemma (its own subtree); the chief Mathlib gap is the
finite-direct-sum-of-localizations decomposition (02M0) and the residue-degree length change (b).
-/

/-- If `B` is a module-finite extension of a one-dimensional local domain `A`, with `A → B`
injective, then the fraction field `L` of `B` is finite-dimensional over the fraction field `K`
of `A`. -/
theorem finiteDimensional_fractionRing_of_finite
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (hAB : Function.Injective (algebraMap A B)) :
    Module.Finite K L := by
  -- B is integral (hence algebraic) over A since it is module-finite.
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  -- The image of `A \ {0}` lies in `B \ {0}` (injectivity + domain).
  have hMN : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro x ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    have : a ≠ 0 := nonZeroDivisors.ne_zero ha
    rw [ne_eq, ← (algebraMap A B).map_zero]
    exact fun h => this (hAB h)
  -- Every nonzero `n : B` divides a nonzero element of `A` (it is algebraic over `A`):
  -- by `exists_smul_eq_mul`, `d • 1 = n * c` with `d ≠ 0`, so `n ∣ algebraMap A B d`.
  have hdvd : ∀ n ∈ nonZeroDivisors B,
      ∃ m ∈ Algebra.algebraMapSubmonoid B (nonZeroDivisors A), n ∣ m := by
    intro n hn
    obtain ⟨c, d, hd, hdc⟩ :=
      Algebra.IsAlgebraic.exists_smul_eq_mul A (1 : B) (b := n) (nonZeroDivisors.ne_zero hn)
    refine ⟨algebraMap A B d, ?_, ?_⟩
    · rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
      exact ⟨d, mem_nonZeroDivisors_of_ne_zero hd, rfl⟩
    · rw [Algebra.smul_def, mul_one] at hdc
      exact ⟨c, hdc⟩
  -- Hence inverting `A \ {0}` in `B` already produces all of `L = Frac B`.
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (nonZeroDivisors B) hMN hdvd).mpr inferInstance
  -- `Module.Finite A B` localizes to `Module.Finite K L`.
  exact Module.Finite.of_isLocalization A B (nonZeroDivisors A)
