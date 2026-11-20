# Proof of the refinement theorem (BK93 (2.2.8), printed p. 56; T6)

This module proves the published proposition
`Langlands.BushnellKutzko.RefinementStatement` exactly, as the theorem
`Langlands.BushnellKutzko.refinement : RefinementStatement.{uF, uV, uE}`. No premise is added.
The statement and its source correspondence are in `RefinementStatement.md`. Source:
Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), (2.2.8),
printed p. 56; the derived stratum is set up on p. 51.

The proof does not follow the book's route through (1.2.8), (2.2.3) and compactness. It uses an
algebraic centralizer argument in `End_F(V)`, built in the helper modules listed below. The
only published results it uses are the Library's T1 (`tameCorestriction`) and T2
(`adjointExactness`), together with the Library's lattice-chain, subfield and valuation
foundations.

## Notation

`𝓛 = S.chain`, `𝔓^k = 𝓛.endFiltration k`, `r = S.r`, `β = S.b`, and `c = C.b ∈ End_E(V)` with
restriction `c_F = c.restrictScalars F`. Also `E₁ = F[β, c_F]` and
`s' = restrictScalars ∘ s : End_F(V) → End_F(V)`. The derived-stratum hypothesis gives
`βE : E` with `subfieldEmbedding F E V βE = β` and `F[βE] = E`.

## Generic lemmas in this file

- `mem_criticalIndexSet_iff_of_approx`: suppose a predicate `Z` approximates the centralizer
  lattice `𝔔^0(γ)` modulo `𝔓^1` in both directions. Then `k` is a critical index of `γ`
  exactly when some `x ∈ 𝔑_k(γ)` is not congruent mod `𝔓^1` to an element satisfying `Z`.
  `mem_criticalIndexSet_iff_commute` is the special case `Z = (commutes with β)`.
- `mem_adjointLattice_iff_of_sub_mem`: if `γ - β ∈ 𝔓^{-r}` and `k ≤ -r`, then `𝔑_k(γ) = 𝔑_k(β)`.
- `criticalIndexSet_eq_empty_of_eq_bot`: a scalar has no critical index.
- `centralizerLattice_mul_adjointLattice_le`: `𝔔^m 𝔑_k ⊆ 𝔓^m`.
- `valuation_eq_of_depth`: if `x ∈ 𝔓^s \ 𝔓^{s+1}`, then the Library valuation of `x` is `s`.
- `transported_*` and `derived_*`: V1 (middle exactness of the third sequence), V3 (a
  normalized generator lying in `𝔓^r` has `r` as a critical index) and the existence of a
  greatest critical index, for the stratum `C` over `E`. `C.chain` is a chain over
  `subfieldIntegers F E`. The `derived_*` lemmas give `E` the Library's spectral local-field
  structure (`LocalField.FiniteExtension`) and transfer `C.chain` along `subfieldIntegerEquiv`
  to a chain over `𝒪[E]` with the same lattices (`RefinementChainTransport`). They then apply
  the generic results of `RefinementElementExactness`, which rest on T1 and T2 over `E`.
- Restriction of scalars: `restrictScalars_commute`, `exists_restrictScalars_of_commute` (an
  endomorphism commuting with `β` is `E`-linear), `exists_restrictScalars_of_mem_adjoin`
  (every element of `F[β, c_F]` is the restriction of an element of `E[c]`), `restrictUnit`,
  `mem_endFiltration_restrictScalars` and `restrictUnit_mem_stabilizer`. The last two compare
  filtrations and stabilizers of two chains with equal lattices over `E` and over `F`.
- `normalizingUnits_of_isField`, `isField_of_normalizingUnits_of_comm` and
  `range_subfieldEmbedding_subalgebra` translate between field subalgebras of `End_F(V)` and
  abstract fields acting on `V`.

## The main argument (`refinement_aux`)

1. **`E` normalizes `𝓛`.** `S` is pure, so `F[β]` is a field whose units normalize `𝓛`. The
   embedding of `E` lands in `F[β]`, because `F[βE] = E` (`AlgHom.map_adjoin_singleton`).
2. **`E₁` is a field normalizing `𝓛`.** Every element of `E₁` is the restriction of an element
   of `E[c]`. `C` is pure, so `E[c]` is a field whose units normalize `C.chain`. The lattices of
   `C.chain` equal those of `𝓛` as sets, so restrictions of these units lie in `𝓛.stabilizer`.
   Commutativity of `E[c]` gives commutativity of `E₁`.
3. **Inputs of the engine.**
   - `s'` preserves every `𝔓^m` by T1, kills `[β, ·]` (`adjointMap_eq_zero`), and is a bimodule
     map for endomorphisms commuting with `β`, since these are `E`-linear.
   - **U1** comes from T2's third sequence with `m = t + 1` and `k = -r - 1`, which is allowed
     because `k₀(β) < -r`. It gives an error `x ∈ 𝔔^{t+1} 𝔑_{-r-1} ⊆ 𝔓^{t+1}` with
     `[β, x] = [β, X]`, so `X - x` commutes with `β`. When `β` is scalar, U1 holds with `x = 0`.
   - **U2** comes from T2's fourth sequence with `m = 1` and `k = -r - 1`. When `β` is scalar, T1
     surjectivity and `ker s = range a_β = 0` (`range_adjointMap_eq_ker`) give `z ∈ 𝔓^{1-r}`
     directly.
   - **V1** is `derived_exists_commute_sub_mem` with `k = -r`. It is allowed because
     `k₀(c) < -C.r = 1 - r`.
   - `s'(b) - c_F ∈ 𝔓^{1-r}`, because `D.b = s(b)` lies in `C.coset` (the strata are
     equivalent).
4. **Construction.** `exists_refined_element` (`RefinementConstruction`) with `L = E₁` gives `γ`.
   It satisfies: `γ ≡ β + b (mod 𝔓^{1-r})`; `F[γ]` consists of normalizing units; `F[γ]` and
   `E₁` approximate each other; Claim X holds; and `F[γ] = F` if `[E₁:F] = 1`. Set
   `T = [𝓛, n, r - 1, γ]`.
5. **Valuation.** `β ∈ 𝔓^{-n} \ 𝔓^{1-n}` and `γ - β ∈ 𝔓^{-r} ⊆ 𝔓^{1-n}`. Hence `γ` has the same
   depth, and `v(γ) = v(β) = -n`.
6. **Coset.** `T.coset = {x | x - (β + b) ∈ 𝔓^{1-r}}`, because `γ ≡ β + b`.
7. **`e` and `f`.** `subfieldRamificationIndex_eq_of_approx` and
   `subfieldResidueDegree_eq_of_approx` (`RefinementInvariants`) apply to `F[γ]` and `E₁`.
8. **Critical exponent.** Let `Z(y)` mean "`y` commutes with `β` and `c_F`". `refinement_core`
   with `b' = γ - β` and `t = 0` gives (I): every `x ∈ 𝔑_{1-r}(γ)` is congruent mod `𝔓^1` to
   some `y` with `Z(y)`. In particular this holds on `𝔔^0(γ)`. Claim X gives the converse
   approximation. Therefore no `k ≥ 1 - r` is critical for `γ`, and for `k ≤ -r`, `k` is
   critical for `γ` exactly when `𝔑_k(β) ⊄ {Z} + 𝔓^1`.
   - **`c ∉ E`.** `c ∈ 𝔔_C^{-r}`, because `s(b) ∈ 𝔔^{-r}` by T1 and `s(b) - c ∈ 𝔔^{1-r}`. So V3
     gives `-r ∈ crit(c)`. With `k₀(c) < 1 - r` this gives `k₀(c) = -r`. Now suppose `-r` were
     not critical for `γ`. Every `E`-linear `x ∈ 𝔓^0` lies in `𝔑_{-r}(β)`, so `x` would be
     congruent mod `𝔓^1` to an element commuting with `β` and `c_F`. That element is
     `E`-linear. This would make `𝔑^C_{-r}(c) ≤ 𝔔^0_C(c) ⊔ 𝔔^1`, contradicting `-r ∈ crit(c)`.
     Hence `-r` is the greatest critical index of `γ`, and `k₀(γ) = -r = max(k₀(β), k₀(c))`.
   - **`c ∈ E`, `β ∉ F`.** `c_F` is the action of an element of `E`, so `Z(y)` reduces to "`y`
     commutes with `β`". Then the critical sets of `γ` and `β` coincide; above `-r` both are
     empty, because T2 gives `k₀(β)` as a greatest critical index `< -r`. Hence
     `k₀(γ) = k₀(β) = max(k₀(β), ⊥)`.
   - **`c ∈ E`, `β ∈ F`.** Then `E = F`, `c_F` is a scalar, `E₁ = ⊥` and `[E₁:F] = 1`. So
     `F[γ] = ⊥`, and both sides are `⊥`.

   In every case `k₀(γ) < -(r - 1)`, so `T` is simple.

`refinement` unpacks the statement and applies `refinement_aux` with `E₁` the stated subalgebra.
The hypotheses `S.chain.valuation b = -S.r` and `C.n = D.n` are not needed by this argument.
They are accepted and ignored, so the proved proposition is exactly the published one.
`refinement_aux` uses the finite option `maxHeartbeats 1000000`.

## Helper modules (dependency order)

`RefinementChainTransport`, `RefinementElementExactness`, `RefinementDiagonal`,
`RefinementCore`, `RefinementCentralizer`, `RefinementInvariants`, `RefinementConstruction`.
