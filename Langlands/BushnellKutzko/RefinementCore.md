# The centralizer argument behind the refinement theorem

Internal helper module for the proof of BK93 (2.2.8) (`RefinementProof`). It holds the
algebraic core step and general tools about fields generated inside `A = End_F(V)`. The core
step is a direct, filtration-level replacement for the book's use of (1.4.x) and (2.2.3) in the
proof of (2.2.8). Notation: `𝔓^k = 𝓛.endFiltration k`, `𝔄 = 𝔓^0`.

## Core step

- `commutator_mem_endFiltration`: `[𝔓^m, 𝔓^n] ⊆ 𝔓^{m+n}`.
- `refinement_core`. Take an additive `s : A → A` that preserves every `𝔓^m`, kills
  `βX - Xβ`, and satisfies `s(Yz) = Y s(z)` and `s(zY) = s(z) Y` for `Y` commuting with `β`.
  Assume two inputs:
  - U1: if `X ∈ 𝔓^t` and `βX - Xβ ∈ 𝔓^{t-r}`, then there is a small error `x ∈ 𝔓^{t+1}`
    with `X - x` commuting with `β`. Equivalently, `X` is congruent mod `𝔓^{t+1}` to an
    endomorphism commuting with `β`;
  - V1: if `γ` commutes with `β`, `γ ∈ 𝔓^t` and `cγ - γc ∈ 𝔓^{t+1-r}`, then `γ ≡ γ₁`
    (mod `𝔓^{t+1}`) with `γ₁` commuting with `β` and `c`.

  Suppose `b' ∈ 𝔓^{-r}` with `s(b') ≡ c (mod 𝔓^{1-r})`. Then every `X ∈ 𝔓^t` with
  `(β + b')X - X(β + b') ∈ 𝔓^{t+1-r}` is congruent mod `𝔓^{t+1}` to an element commuting with
  `β` and `c`.

  Proof. U1 applies to `X`, because `[b', X] ∈ 𝔓^{t-r}` and hence `[β, X] ∈ 𝔓^{t-r}`. It gives
  `x ∈ 𝔓^{t+1}` such that `Y = X - x` commutes with `β`. Then `Y ∈ 𝔓^t`. Write
  `[β + b', X] = [β, X] + [b', Y] + [b', x]` and apply `s`. The first term is killed, the last
  maps into `𝔓^{t+1-r}` because `[b', x] ∈ 𝔓^{t+1-r}`, and `s([b', Y]) = [s(b'), Y]` by the
  bimodule property. Hence `[s(b'), Y] ∈ 𝔓^{t+1-r}`, and `[c, Y] ∈ 𝔓^{t+1-r}` because
  `s(b') - c ∈ 𝔓^{1-r}`. V1 applied to `Y` gives `γ₁` commuting with `β` and `c` with
  `Y - γ₁ ∈ 𝔓^{t+1}`. Finally `X - γ₁ = (Y - γ₁) + x ∈ 𝔓^{t+1}`, using the same error term
  `x ∈ 𝔓^{t+1}`.

## Units, depth and fields

- `mem_stabilizer_of_mem_order` and `mem_stabilizer_of_mem_unitFiltration`: units of `𝔄`
  (with inverse in `𝔄`), and in particular elements of `U^k(𝔄)`, normalize the chain.
- `subfieldEmbedding_mem_iff_le` and `inv_smul_lattice_shift`: for an element `a` of a field
  acting on `V` that shifts the chain by `d`, `a ∈ 𝔓^k ↔ k ≤ d`, and `a⁻¹` shifts by `-d`.
- `exists_depth`: every nonzero endomorphism has an exact depth `s` (`x ∈ 𝔓^s \ 𝔓^{s+1}`), by
  clearing denominators with a uniformizer and lattice depths of vectors.
- `isField_of_forall_ne_zero_isUnit`: a commutative subalgebra of a finite-dimensional algebra
  whose nonzero elements are units is a field (left multiplication is injective, hence
  surjective).
- `NormalizingUnits 𝓛 K` (internal definition): every nonzero element of the subalgebra `K` is
  a unit of `A` lying in the stabilizer `𝔎(𝓛)`. `isField_of_normalizingUnits`: then `F[y]` is
  a field whose units normalize `𝓛`. This is exactly the field part of `Stratum.IsPure`.
- `conj_mem_elementAlgebra`, `conj_mem_elementAlgebra'` and `normalizingUnits_conj`:
  conjugation by a unit `u` maps `F[z]` onto `F[u⁻¹zu]` and preserves normalizing units when
  `u` normalizes the chain.

## Approximation

- `Approx 𝓛 K K'` (internal definition): every `X ∈ K ∩ 𝔓^t` is congruent mod `𝔓^{t+1}` to an
  element of `K'`. The predicate is directional: it approximates `K` by `K'`. The refinement
  proof uses it in both directions, `Approx 𝓛 K K'` and `Approx 𝓛 K' K`.
- `conj_sub_mem` and `conj_mem`: for `g ∈ 1 + 𝔓` with `g⁻¹ ∈ 𝔄`, `g⁻¹Zg - Z ∈ 𝔓^{t+1}` when
  `Z ∈ 𝔓^t`.
- `approx_conj_left` and `approx_conj_right`: approximation survives conjugating either side
  by such `g`.
