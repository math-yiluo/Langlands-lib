# Proof of Stacks Lemma 16.10.2 (07FD): choosing regular parameters

`Langlands.CommutativeAlgebra.Popescu.regularParameterChoice :
RegularParameterChoiceStatement.{u}` proves the Library statement
`Langlands.CommutativeAlgebra.Popescu.RegularParameterChoiceStatement` (Stacks Project,
Chapter 16 *Smoothing Ring Maps*, Lemma 16.10.2, Tag 07FD, printed p. 24 of `smoothing.pdf`).

The hypotheses are those of the statement:

- `Λ : Type u` is a Noetherian commutative ring;
- `I ≤ q` with `q` prime;
- `(q ^ n).map (algebraMap Λ Λ_q) ≤ I.map (algebraMap Λ Λ_q)`, where `Λ_q = Localization.AtPrime q`;
- `Λ_q` is a regular local ring;
- `e > 0`.

For `d = (maximalIdeal Λ_q).spanFinrank`, the theorem produces `π : Fin d → Λ` with the
statement's four conditions:

1. the images `φ(πᵢ)` generate the maximal ideal of `Λ_q`;
2. they form a weakly regular sequence on `Λ_q`;
3. `πᵢⁿ ∈ I`;
4. `πᵢ² x ∈ Jᵢ → πᵢ x ∈ Jᵢ` for all `x : Λ`, where `Jᵢ = (π_j^e : j < i)`.

The theorem adds no hypotheses. The module imports:

- the statement module;
- `Langlands.CommutativeAlgebra.Popescu.RegularSequencePowersProof`, the Library proof
  `regularSequencePowers` of Stacks Lemma 10.68.9 (07DV), which imports
  `RegularSequencePowersStatement`;
- `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_RegularLocalRingFlatLocalAscent`.
  From this module it uses `RegularFlatLocalAscent.exists_isWeaklyRegular_ofList_eq_maximalIdeal`:
  the maximal ideal of a regular local ring `R` is `Ideal.ofList rs` for some weakly regular list
  `rs` of length `(maximalIdeal R).spanFinrank`.

The theorem uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Notation below: `φ = algebraMap Λ Λ_q`, `S = q.primeCompl = Λ \ q`, and indices are
zero-based elements of `Fin d`.

## Helper lemmas (namespace `Langlands.CommutativeAlgebra.Popescu.RegularParameterChoice`)

Unless stated otherwise, these hold for any commutative ring `R` (in any universe).

- `mem_take_ofFn_iff`, `ofList_take_ofFn`: the first `i` entries of `List.ofFn x` are the
  `x j` with `j < i`. Hence `Ideal.ofList ((List.ofFn x).take i) = Ideal.span (x '' {j | j < i})`.
- `isWeaklyRegular_ofFn_iff`: `List.ofFn x` is weakly regular on `R` iff for every `i` and `z`,
  `x i * z ∈ span (x '' {j | j < i})` implies `z ∈ span (x '' {j | j < i})`. The proof applies
  Mathlib's `Sequence.isWeaklyRegular_iff`, which tests the `i`-th term on
  `R ⧸ (ofList (take i)) • ⊤`, and `isSMulRegular_quotient_iff_mem_of_smul_mem`. It then rewrites
  the ideal by `ofList_take_ofFn` and `Ideal.mul_top`.
- `span_image_mul_units`: if every `u j` is a unit, then for any `T`, `span ((u j · x j) '' T)`
  equals `span (x '' T)`.
- `isWeaklyRegular_ofFn_mul_units`: multiplying the terms of a weakly regular `List.ofFn x` by
  units `u i` keeps it weakly regular. This follows from the ideal form above and
  `span_image_mul_units`: `x i * z = u i⁻¹ · (u i x i * z)`.
- `exists_mem_forall_mul_mem`: let `S` be a submonoid and `K`, `J` ideals with `K` finitely
  generated. If every `x ∈ K` has some `s ∈ S` with `s x ∈ J`, then a single `s ∈ S` works for
  all of `K`. The proof takes `s = ∏ t_g`, the product of the elements chosen for a finite
  generating set `G` of `K`, and proves `s x ∈ J` by `Submodule.span_induction`.
- `exists_mul_mem_of_algebraMap_mem_map`: for a localization `B` of `A` at `S` and an ideal `J`,
  if the image of `x` lies in `J B`, then `s x ∈ J` for some `s ∈ S`. The proof uses
  `IsLocalization.mem_map_algebraMap_iff` and `IsLocalization.eq_iff_exists`.
- `mem_of_mul_mem_span_pow`: let `R : Type u` be local, `x : Fin d → R` with all `x i` in the
  maximal ideal and `List.ofFn x` weakly regular, and let `e > 0`. Then
  `x i * z ∈ span (x_j^e : j < i)` implies `z ∈ span (x_j^e : j < i)`. It takes the 07DV
  statement as an explicit hypothesis `hpow : RegularSequencePowersStatement.{u}`.
  - Since the terms lie in the maximal ideal, `List.ofFn x` is regular
    (`Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`).
  - Apply `hpow` with `M = R` and exponents `ee j = e` for `j < i`, `ee j = 1` otherwise. So
    `List.ofFn (x_j^{ee j})` is regular, hence weakly regular.
  - Apply `isWeaklyRegular_ofFn_iff` at index `i`. There `x_i^{ee i} = x_i`, and the ideal
    `span (x_j^{ee j} : j < i)` equals `span (x_j^e : j < i)`.

## The construction

- `span_isWeaklyRegular_mul`: if `π` satisfies conditions 1 and 2, so does `j ↦ s j · π j` for
  any `s : Fin d → S`. The images `φ(s j)` are units of `Λ_q`
  (`IsLocalization.map_units`), so this follows from `span_image_mul_units` and
  `isWeaklyRegular_ofFn_mul_units`.
- `exists_initial` (conditions 1, 2 and 3):
  - Take `rs` from `exists_isWeaklyRegular_ofList_eq_maximalIdeal Λ_q` and write it as
    `List.ofFn y` with `y : Fin d → Λ_q`. Then `span (range y)` is the maximal ideal.
  - Clear denominators: `y i = mk' (a i) (b i)` with `b i ∈ S` (`IsLocalization.exists_mk'_eq`),
    so `φ(a i) = φ(b i) · y i` with `φ(b i)` a unit. By the unit lemmas, `a` satisfies
    conditions 1 and 2.
  - `φ(a i)ⁿ` lies in `(maximalIdeal Λ_q)ⁿ = (qⁿ)Λ_q ⊆ IΛ_q`
    (`IsLocalization.AtPrime.map_eq_maximalIdeal`, `Ideal.map_pow`). By
    `exists_mul_mem_of_algebraMap_mem_map` there is `t i ∈ S` with `t i · (a i)ⁿ ∈ I`.
  - Put `π i = t i · a i`. Conditions 1 and 2 hold by `span_isWeaklyRegular_mul`.
  - For condition 3, if `n = 0` then `t i = t i · (a i)⁰ ∈ I ⊆ q`, which contradicts
    `t i ∉ q`; so the case cannot occur. If `n = k + 1`, then
    `(t i · a i)^{k+1} = t iᵏ · (t i · (a i)^{k+1}) ∈ I`.
- `exists_stage` (requires `IsNoetherianRing Λ` and takes `hpow`): for every `k : ℕ` there is
  `π` satisfying conditions 1, 2 and 3, and condition 4 for every index `i` with `i < k`. The
  proof is by induction on `k`.
  - `k = 0` is `exists_initial`.
  - Step `k → k + 1`, with `π` from the induction hypothesis. If `k ≥ d` there is no new index
    and `π` works. Otherwise let `i₀ = k` and `J = span (π_j^e : j < i₀)`.
  - Let `K = comap φ (map φ J)`. It is finitely generated because `Λ` is Noetherian, and each
    of its elements is moved into `J` by an element of `S`
    (`exists_mul_mem_of_algebraMap_mem_map`). By `exists_mem_forall_mul_mem` there is one
    `s₀ ∈ S` with `s₀ K ⊆ J`.
  - Define `π' j = s j · π j`, where `s i₀ = s₀` and `s j = 1` for `j ≠ i₀`. Conditions 1 and 2
    hold for `π'` by `span_isWeaklyRegular_mul`. Condition 3 holds since `π'_jⁿ = s_jⁿ π_jⁿ`.
  - For every `i ≤ i₀`, `span (π'_j^e : j < i) = span (π_j^e : j < i)`, because `π'_j = π_j` for
    `j < i₀`.
  - Indices `i < i₀`: also `π'_i = π_i`, so condition 4 for `π'` at `i` is condition 4 for `π`
    at `i`, given by the induction hypothesis.
  - The index `i₀`: suppose `(s₀ π_{i₀})² x ∈ J`. Then
    `φ(π_{i₀}) · φ(s₀² π_{i₀} x) = φ((s₀ π_{i₀})² x) ∈ JΛ_q`. Here `JΛ_q = map φ J` is
    `span (φ(π_j)^e : j < i₀)` (`Ideal.map_span`).
  - The sequence `φ ∘ π` lies in the maximal ideal by condition 1 and is weakly regular by
    condition 2. So `mem_of_mul_mem_span_pow`, applied in `R = Λ_q`, gives
    `φ(s₀² · π_{i₀} x) ∈ JΛ_q`.
  - Since `φ(s₀²)` is a unit, `φ(π_{i₀} x) ∈ JΛ_q`, i.e. `π_{i₀} x ∈ K`. Hence
    `π'_{i₀} x = s₀ · π_{i₀} x ∈ J`.
- `regularParameterChoice_of_powers (hpow : RegularSequencePowersStatement.{u}) :
  RegularParameterChoiceStatement.{u}` applies `exists_stage` with `k = d`. Every `i : Fin d`
  satisfies `i < d`, so condition 4 holds for all `i`.
- `regularParameterChoice` is `regularParameterChoice_of_powers regularSequencePowers`.

## Relation to the source proof

The construction follows the source proof: choose generators, multiply by elements of `S` to
get `πᵢⁿ ∈ I`, then fix condition 4 one index at a time, each time multiplying only `π_{t+1}` by
an element of `S`. It differs in three places.

- **Regular sequence.** The source picks arbitrary `π₁, …, π_d` with (1) and cites Algebra,
  Lemma 10.106.3 (00NQ) for their regularity in `Λ_q`. The Lean proof does not use 00NQ. It
  starts from a weakly regular generating list supplied by the Library lemma
  `exists_isWeaklyRegular_ofList_eq_maximalIdeal`. All later changes multiply the images by units
  of `Λ_q`, which preserves weak regularity.
- **Ogoma's lemma.** The source applies Lemma 16.10.1 (Ogoma, Tag 07FC) to pass from the
  annihilator condition in `Λ_q/(π_j^e)` to one in `Λ/(π_j^e)` after replacing `π_{t+1}` by
  `s π_{t+1}`. The Lean proof does not use the Library statement `AnnihilatorStabilizationStatement`.
  It handles the cyclic module `Λ/J` directly, as above: an `s₀ ∈ S` with `s₀ K ⊆ J` for the
  finitely generated ideal `K = comap φ (JΛ_q)`, then `s₀ π_{i₀}`.
- **Powers.** As in the source, the condition in `Λ_q` comes from Algebra, Lemma 10.68.9 (07DV)
  applied to `π₁^e, …, π_t^e, π_{t+1}`. The Lean proof applies the Library theorem
  `regularSequencePowers` to the whole sequence with exponents `e, …, e, 1, …, 1`. It then reads
  off the needed nonzerodivisor condition at index `t + 1`.

## Authorship

Written by Worker 429 for Task 6408.
