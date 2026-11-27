# Residue data of two fields with the same graded centralizers

Let `F` be a nonarchimedean local field, `V` a finite-dimensional `F`-vector
space and `𝓛` an `𝔬_F`-lattice chain in `V`, with `𝔓^t = 𝓛.endFiltration t`.
Let `E₁`, `E₂` be fields finite over `F` acting on `V`, with `E_i^×`
normalizing `𝓛`. Put `𝔔_i^t = 𝔓^t ∩ End_{E_i}(V)`. The module derives the
conclusions (i)–(iii) of Lemma (5.2) of BK94 from the hypothesis

`GradedEq 𝓛 E₁ E₂`: `𝔔₁^t + 𝔓^{t+1} = 𝔔₂^t + 𝔓^{t+1}` for every `t ∈ ℤ`,

which is (5.8) of BK94. All results are proved, in the namespace
`GradedCentralizer`.

## Main results

- `exists_integer_sub_mem` (BK94 (5.2)(i)): every `a ∈ 𝔬_{E₁}` is congruent
  modulo `𝔓` to some `b ∈ 𝔬_{E₂}`.
- `exists_primeElement_congr` (BK94 (5.2)(ii)): there are prime elements `π₁`
  of `𝔬_{E₁}` and `π₂` of `𝔬_{E₂}` (`RingPrimeElement`) and `u ∈ U¹(𝔄)` with
  `π₂ = π₁ u`.
- `exists_tameCorestriction_congr` (BK94 (5.2)(iii)): there are tame
  corestrictions `s_i` relative to `E_i/F` with `s₁(x) ≡ s₂(x)` modulo
  `𝔓^{t+1}` for every `t ∈ ℤ` and `x ∈ 𝔓^t`.

## Auxiliary results

- `embedding_mem_fieldCommutant`, `embedding_mul_comm`: elements of `E` act
  `E`-linearly and commute with `End_E(V)`.
- `fieldCommutantEnd`, `restrictScalars_mem_fieldCommutant`: passage between
  `E`-linear elements of `End_F(V)` and `End_E(V)`; `restrictScalars_smul`.
- `embedding_mem_endFiltration_shift`,
  `embedding_notMem_endFiltration_shift_add_one`: a nonzero `a ∈ E` lies in
  `𝔓^d` but not in `𝔓^{d+1}`, where `d` is its shift
  (`StratumEquivalence.shift`).
- `embedding_mem_order`, `embedding_mem_endFiltration_one`: `𝔬_E ⊆ 𝔄` and
  `𝔭_E ⊆ 𝔓`.
- `one_notMem_endFiltration_one`: `1 ∉ 𝔓`.
- `unitSmul`, `restrictScalars_unitSmul`: the product of a tame corestriction
  with a unit of `𝔬_E` is a tame corestriction.
- `restrictScalars_mem`, `exists_eq`: a tame corestriction maps `𝔓^n` onto the
  `E`-linear part of `𝔓^n` (from `tameCorestriction`).
- `maximalIdealInField_add`: `𝔭_F` is closed under addition.
- `GradedEq.symm`, and `commutator_mem`: let `x ∈ 𝔓^d` commute with
  `End_{E₁}(V)`. Then `x y − y x ∈ 𝔓^{d+j+1}` for every `y ∈ 𝔔₂^j`. Indeed
  `y = z + p` with `z ∈ 𝔔₁^j` and `p ∈ 𝔓^{j+1}`, and `x` commutes with `z`.
- `restrictScalars_mem_of_graded`, `sub_mul_mem_of_eq_one`,
  `commutator_mem_of_eq_one`: steps of the proof of (iii), described below.

## Proofs

The main tool is `StratumEquivalence.exists_integer_sub_mem_of_commutator`
(module `CentralizerGradedScalar`). It says that if `b ∈ 𝔄` commutes with every
`𝔔_i^j` modulo `𝔓^{j+1}`, then `b` is congruent modulo `𝔓` to an element of
`𝔬_{E_i}`.

**(i).** Let `a ∈ 𝔬_{E₁}`. Then `a ∈ 𝔔₁^0`, so `a = c + p` with `c ∈ 𝔔₂^0` and
`p ∈ 𝔓`. By `commutator_mem`, `a` commutes with each `𝔔₂^j` modulo
`𝔓^{j+1}`, hence so does `c`. The main tool, for `E₂`, gives `b ∈ 𝔬_{E₂}` with
`c ≡ b`, so `a ≡ b` modulo `𝔓`.

**(ii).** Let `ϖ_i` be uniformizers of `𝔬_{E_i}`. Their shifts agree, by
`StratumEquivalence.shift_uniformizer_eq_of_sup_eq` applied to the case `t = 0`
of the hypothesis; call the common shift `d`. Write `ϖ₂ = z + p` with
`z ∈ 𝔔₁^d` and `p ∈ 𝔓^{d+1}`, and put `b₁ = ϖ₁⁻¹ z ∈ 𝔄`. For `y ∈ 𝔔₁^j`,
`b₁ y − y b₁ = ϖ₁⁻¹ (z y − y z)`. Here `z y − y z ∈ 𝔓^{d+j+1}`, by
`commutator_mem` for `ϖ₂` with the roles of `E₁` and `E₂` exchanged. The main
tool, for `E₁`, gives `a ∈ 𝔬_{E₁}` with `b₁ ≡ a` modulo `𝔓`. Then
`ϖ₂ − ϖ₁ a ∈ 𝔓^{d+1}`. If `a ∈ 𝔭_{E₁}`, then `ϖ₂ ∈ 𝔓^{d+1}`, which is false.
So `a` is a unit, and `π₁ = ϖ₁ a` is a prime element of shift `d`. Finally
`u = 1 + π₁⁻¹ (ϖ₂ − π₁) ∈ U¹(𝔄)` and `π₁ u = ϖ₂ = π₂`.

**(iii).** Fix any tame corestrictions `s₁`, `s₂`.

1. *Equal kernels* (`restrictScalars_mem_of_graded`). For `x ∈ 𝔓^t`,
   `s₁(x) ∈ 𝔓^{t+1}` implies `s₂(x) ∈ 𝔓^{t+1}`. By trace duality
   (`TameCorestriction.restrictScalars_mem_endFiltration_iff_trace`, module
   `TameCorestrictionKernel`), the condition for `s_i` is
   `tr(x y) ∈ 𝔭_F` for all `y ∈ 𝔔_i^{−t}`. These conditions agree, because
   `𝔔₁^{−t}` and `𝔔₂^{−t}` agree modulo `𝔓^{1−t}` and `tr(x 𝔓^{1−t}) ⊆ 𝔭_F`.
2. *A first comparison* (`sub_mul_mem_of_eq_one`). Choose `x₀ ∈ 𝔄` with
   `s₁(x₀) = 1`, and put `b = s₂(x₀)`. For `x ∈ 𝔓^t` write `w = s₁(x)` as
   `z + p`, with `z ∈ 𝔔₂^t` and `p ∈ 𝔓^{t+1}`. Then `s₁(x − x₀ w) = 0`, so
   `s₂(x − x₀ w) ∈ 𝔓^{t+1}` by step 1, and `s₂(x₀ z) = b z`. Hence
   `s₂(x) ≡ b s₁(x)` modulo `𝔓^{t+1}`.
3. *`b` is almost scalar* (`commutator_mem_of_eq_one`). For `y ∈ 𝔔₂^j`,
   `b y − y b = s₂(x₀ y − y x₀)`. Moreover `s₁(x₀ y − y x₀) ∈ 𝔓^{j+1}`, since
   `y` agrees with an element of `𝔔₁^j` modulo `𝔓^{j+1}`. By step 1,
   `b y − y b ∈ 𝔓^{j+1}`. The main tool gives `a ∈ 𝔬_{E₂}` with `b ≡ a` modulo
   `𝔓`.
4. *`a` is a unit.* Step 2 with the roles exchanged, for `x₀' ∈ 𝔄` with
   `s₂(x₀') = 1`, applied to `x = x₀`, gives `1 ≡ s₁(x₀') b` modulo `𝔓`. If
   `a ∈ 𝔭_{E₂}`, then `b ∈ 𝔓` and `1 ∈ 𝔓`, which is false.
5. With `s₂' = a⁻¹ s₂` (`unitSmul`),
   `s₁(x) − s₂'(x) = a⁻¹ ((a − b) s₁(x) − (s₂(x) − b s₁(x))) ∈ 𝔓^{t+1}`.

## Origin

Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), Lemma (5.2) and its proof, printed pp. 132–134 (PDF pp. 145–147),
literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`. There (5.8)
is derived, and (i)–(iii) are deduced from it, when `𝔄` is maximal among the
hereditary orders normalized by `F[γ_i]^×`. The general case is reduced to that
one through BK93 (3.6.1) and (5.1.16). In the proofs here, (i) and (ii) use the
graded-scalar lemma in place of the centre of `U(𝔅)/U¹(𝔅)` and of fixed points
of conjugation. Step 1 of (iii) uses trace duality in place of the duality of
character groups. None of these uses the maximality assumption, so no
reduction to the maximal case is needed.
