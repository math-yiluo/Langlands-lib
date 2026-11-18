# The totally complex archimedean bridge for cuspidal complex-place parameters

Author: Worker 818. Statement contribution to Task 7463
(`665f4f54-6ef1-4d47-afd2-b5c1114af734`), revision 1, a statement child of Task 7343
(`d6ca8ef3-60ca-4650-a436-8b5a00655394`).

**Scope.** The module `Langlands.Automorphic.CuspidalComplexParameterBridgeStatement`
defines three propositions in the namespace `Langlands.Automorphic` and proves nothing.
Each has the single universe parameter `uF`, the universe of the number field.

| Proposition | Content |
|---|---|
| `CuspidalComplexParameterInfinitesimalCharacterTCStatement` | complex-place parameters of a cuspidal realization determine its infinitesimal character |
| `ComplexParameterRegularAlgebraicTCStatement` | a matching center character is regular algebraic exactly when the parameters are Clozel regular algebraic |
| `CuspidalComplexParameterBridgeTCStatement` | the existing parameter existence statement and the two statements above |

The principal declaration is `Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement`.
It is the named premise that the operator authorized beside the literal B7 statement, in the
trusted message `89b70579f7465ae3994e304e80cf284b`: (i) a cuspidal class has parameters at
each complex place, and these determine its infinitesimal character; (ii) that character is
regular algebraic exactly when the parameters are characters `z^a z̄^b` with Clozel's
integrality and regularity. Its proof belongs to archimedean representation work. Nothing in
this module, in the numerical examples quoted below, or in the Library's scalar-action theorem
for complex standard modules proves it.

## 1. Vocabulary

Everything is published Library vocabulary. The supporting definitions of Task 7455
(`0e2c3642-43ca-4d22-bd25-b95650fabbc0`) are in `Langlands.Automorphic.ComplexPlaceParameterWeights`.

- `Langlands.LocalFactor.Archimedean.ComplexCharacterData` (`ArchimedeanAttachment`): an actual
  continuous character of `ℂ^×` with signed integer weight `m` and complex exponent `t`, certified
  by `character z = (z / ‖z‖)^m · ‖z‖^(2t)`.
- `OperatorRealization.HasComplexPlaceParameter S v ds` (`ArchimedeanPlaceParameter`): the
  `U(n)`-finite functions of the complex standard module of the list `ds` (of length `n`) embed
  injectively into the actual realization, compatibly with the compact action and the Lie action
  at the complex place `v`. It has only the field universe.
- `ArchimedeanGL.EnvelopingCenter F n`, `ArchimedeanGL.IsHighestWeightCharacter`,
  `ArchimedeanGL.IsRegularAlgebraicCharacter`, `OperatorRealization.HasInfinitesimalCharacter`,
  `OperatorRealization.IsRegularAlgebraic` and `CuspidalOperatorRealization.IsoClass.IsRegularAlgebraic`
  (`RegularAlgebraic`). The center character `χ` is an actual `ℂ`-algebra homomorphism on the
  actual center of the enveloping algebra of the complexified Lie algebra of `GL_n(F ⊗ ℝ)`.
  `IsRegularAlgebraicCharacter F n χ` says that `χ` is the central character of a highest-weight
  vector whose weight `μ` is integral and antitone (dominant for the upper triangular Borel) at
  every embedding index. These highest weights are *unshifted*.
- From Task 7455: `ComplexCharacterData.zExponent d = t + m/2` and
  `ComplexCharacterData.zBarExponent d = t − m/2`; `ComplexPlaceParameter.rho n i = (n−1)/2 − i`
  (indices from `0`); `ComplexPlaceParameter.MatchesHighestWeight n ds μz μz̄` (`ds` has length
  `n`, its `z`-exponents are a permutation of `μz + rho n`, and, by an independent permutation,
  its `z̄`-exponents are a permutation of `μz̄ + rho n`);
  `ComplexPlaceParameter.IsClozelRegularAlgebraic n ds` (`ds` has length `n`, every `z`- and
  `z̄`-exponent lies in `ℤ + (n−1)/2`, and both exponent lists have no repetition);
  `ComplexPlaceParameter.MatchesGlobalHighestWeight F n ds μ` (at every complex place `v`,
  `MatchesHighestWeight n (ds v) (μ (.inr (v, false))) (μ (.inr (v, true)))`); and
  `ComplexPlaceParameter.MatchesInfinitesimalCharacter F n ds χ` (some `μ` satisfies both
  `ArchimedeanGL.IsHighestWeightCharacter F n μ χ` and `MatchesGlobalHighestWeight F n ds μ`).
  The matching relation asserts neither existence nor uniqueness of `χ`.

In all three statements, `ds` is a family of lists of `ComplexCharacterData` indexed by the actual
complex places `{v : NumberField.InfinitePlace F // v.IsComplex}` of `F`.

## 2. The statements

**`CuspidalComplexParameterInfinitesimalCharacterTCStatement.{uF}`.** For every number field
`F : Type uF` with `[NumberField.IsTotallyComplex F]` and `[CompactSpace (AdeleQuotient F)]`,
every `r : ℕ`, every actual cuspidal realization `S : CuspidalOperatorRealization F r` and every
family `ds` with

`∀ v, OperatorRealization.HasComplexPlaceParameter S.realization v (ds v)`,

both of the following hold:

- `∃! χ : ArchimedeanGL.EnvelopingCenter F (r+1) →ₐ[ℂ] ℂ,
  ComplexPlaceParameter.MatchesInfinitesimalCharacter F (r+1) ds χ`;
- every `χ` with `ComplexPlaceParameter.MatchesInfinitesimalCharacter F (r+1) ds χ` satisfies
  `S.realization.HasInfinitesimalCharacter χ`: the actual center acts on the actual realization
  by the scalars `χ`.

So a full family of complex-place parameters determines an actual center character, and every
matching character acts by scalars on the realization. A `CuspidalOperatorRealization F r` is a
realization of `GL_(r+1)`, so the rank is `r+1` throughout, never `r`. No spectral presentation,
and no carrier universe of one, is an argument.

**`ComplexParameterRegularAlgebraicTCStatement.{uF}`.** For every number field `F : Type uF` with
`[NumberField.IsTotallyComplex F]`, every `n : ℕ`, every family `ds` and every
`χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ`,

`ComplexPlaceParameter.MatchesInfinitesimalCharacter F n ds χ →
  (ArchimedeanGL.IsRegularAlgebraicCharacter F n χ ↔
    ∀ v, ComplexPlaceParameter.IsClozelRegularAlgebraic n (ds v))`.

This is a comparison of center characters and numerical parameters. It involves no automorphic
realization and no compactness of the adele quotient. It uses the literal matrix rank `n`; the
cuspidal consumer applies it with `n = r+1`.

**`CuspidalComplexParameterBridgeTCStatement.{uF}`** is

`Langlands.Global.CuspidalArchimedeanParameterExistenceTCStatement.{uF} ∧
  CuspidalComplexParameterInfinitesimalCharacterTCStatement.{uF} ∧
  ComplexParameterRegularAlgebraicTCStatement.{uF}`.

The first conjunct is the published statement of
`Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement`, imported unchanged: every
actual cuspidal realization over a totally complex field has a complex-place parameter at every
complex place (its real-place clause is vacuous). Its proof belongs to Task
`a2cfc970-9e20-4d56-b053-8f91a2e0b5cc`. This module states no second existence assertion.

The exact-stabilizer CM and TC branches of Harris's Proposition 4.8 (Task 7343) use the aggregate
as their single named premise, instantiated at `.{0}`. Mathlib's `NumberField.IsCMField` carries
the instance `IsCMField.to_isTotallyComplex`, so the aggregate applies to CM fields and no separate
CM bridge is needed.

## 3. Use: the regular algebraic type of a cuspidal class

This section explains how the aggregate is used. It is not a theorem of the Library, and the
aggregate itself is unproved. Assume `CuspidalComplexParameterBridgeTCStatement.{uF}`, and let `F`
be totally complex with `[CompactSpace (AdeleQuotient F)]`, `S : CuspidalOperatorRealization F r`,
and `ds` a full family with `∀ v, HasComplexPlaceParameter S.realization v (ds v)`. (Such a family
exists by the first conjunct, by choosing a parameter at each place.) Then

`S.isoClass.IsRegularAlgebraic ↔ ∀ v, ComplexPlaceParameter.IsClozelRegularAlgebraic (r+1) (ds v)`.

By the second conjunct, there is a `χ` with `MatchesInfinitesimalCharacter F (r+1) ds χ`, and
`S.realization.HasInfinitesimalCharacter χ`. By the third conjunct at `n = r+1`, `χ` is regular
algebraic exactly when every `ds v` is Clozel regular algebraic.

- (⇐) If every `ds v` is Clozel regular algebraic, then `χ` is regular algebraic. With
  `HasInfinitesimalCharacter χ` this is `S.realization.IsRegularAlgebraic`, which is
  `S.isoClass.IsRegularAlgebraic` by `CuspidalOperatorRealization.isoClass_isRegularAlgebraic_iff`.
- (⇒) By `CuspidalOperatorRealization.isoClass_isRegularAlgebraic_iff`, there is a regular
  algebraic `χ'` with `S.realization.HasInfinitesimalCharacter χ'`. The carrier is nonzero
  (`CuspidalOperatorRealization.space_nontrivial`), so `OperatorRealization.HasInfinitesimalCharacter.unique`
  gives `χ' = χ`. So `χ` is regular algebraic, and every `ds v` is Clozel regular algebraic.

The converse direction compares two scalar actions on a nonzero carrier, so no further converse
scalar-action clause is needed in the bridge.

## 4. Normalization

The target is fixed against the current `ArchimedeanGL.IsRegularAlgebraicCharacter`, whose highest
weights are unshifted, integral and antitone, and against the orientation of
`ArchimedeanGL.embeddingComponent`: `embeddingComponent_inr_false` says that `.inr (v, false)` reads
the coordinate `z` at `v`, and `embeddingComponent_inr_true` says that `.inr (v, true)` reads its
complex conjugate `z̄`. Task 7455 compiles the examples below in Lean; this module repeats their
calculations and does not duplicate the Lean examples.

**Polar coordinates.** For `z = r e^{iθ}`, the character of `d = (m, t)` is
`(z/|z|)^m |z|^{2t} = e^{imθ} r^{2t}`. For complex `a, b` with `a − b ∈ ℤ`, write
`z^a z̄^b` for the single-valued polar character `r e^{iθ} ↦ r^{a+b} e^{i(a−b)θ}`. It is not a
product of two principal-branch complex powers. The character of `d` is `z^a z̄^b` exactly when
`a − b = m` and `a + b = 2t`, that is

`a = t + m/2 = zExponent d`, `b = t − m/2 = zBarExponent d`.

**Shift and Weyl permutations.** A highest-weight vector of weight `μ` has the infinitesimal
character of the Weyl orbit of `μ + ρ`; at a complex place the Weyl group is `S_n × S_n`, acting
separately on the two factors read through `z` and `z̄` (Clozel, Remark after Definition 1.8).
With indices from `0`, `ρ_i = (n−1)/2 − i`. The matching relation therefore compares the
`z`-exponents with `μ(.inr (v,false)) + ρ` and the `z̄`-exponents with `μ(.inr (v,true)) + ρ`,
each up to its own permutation. The pairing of the two exponents of one block is not recorded.
In Clozel's proof of Theorem 3.13 the blocks are ordered so that `a_1 > … > a_n`; his purity
lemma then gives `b_1 < … < b_n`, and the `z̄`-side dominant weight is compared with `b` through
the longest Weyl element `w_0`.

**Rank one.** `ρ = 0`. The block of weight `m = 3` and exponent `t = 1/2` has `a = 2`, `b = −1`:
the character `z^2 z̄^{−1} = (z/|z|)^3 |z|`. It matches the highest weights `2` at `.inr (v,false)`
and `−1` at `.inr (v,true)`, and it is Clozel regular algebraic (`(n−1)/2 = 0`, `p = 2`, `q = −1`).

**Rank two.** `ρ = (1/2, −1/2)`.

- The blocks of weight `0` and exponents `1/2`, `−1/2` have `z`-exponents `(1/2, −1/2)` and
  `z̄`-exponents `(1/2, −1/2)`, equal to `0 + ρ`. They match the zero highest weight at both
  embedding indices. They are Clozel regular algebraic: `1/2 = 0 + 1/2`, `−1/2 = −1 + 1/2`, and
  the entries are distinct.
- Two trivial blocks (weight `0`, exponent `0`) have the repeated exponent coordinates `(0, 0)`
  in both lists, and fail Clozel regularity (`0` is also not in `ℤ + 1/2`).
- Orientation check: the blocks of weights `1, 1` and exponents `2, −1` have `z`-exponents
  `(5/2, −1/2)` and `z̄`-exponents `(3/2, −3/2)`. Subtracting `ρ`, they match the highest weight
  `(2, 0)` at `.inr (v,false)` and `(1, −1)` at `.inr (v,true)`, both integral and antitone. The
  lists are Clozel regular algebraic. Exchanging the two embedding indices would give a different
  matching, so the example fixes which index carries `z`.

**The Lean examples.** These calculations are compiled in Task 7455's module
`Langlands.Automorphic.ComplexPlaceParameterWeightsExamples`, which this module imports and does not
duplicate. Every block there is the published actual character
`Langlands.Archimedean.characterOfParams m t` (weight `m`, exponent `t`). The declarations, all in the
namespace `Langlands.Automorphic.ComplexPlaceParameter.Examples`, are:

| Case | Data | Lean declarations |
|---|---|---|
| rank one, `m = 3`, `t = 1/2` | `rankOneData` | `rho_one`, `rankOne_exponents` (`a = 2`, `b = −1`), `rankOne_matches` (highest weights `2` and `−1`), `rankOne_regular` |
| rank two, weights `0`, exponents `1/2`, `−1/2` | `rankTwoData` | `rho_two`, `rankTwo_exponents`, `rankTwo_matches` (zero highest weights on both sides), `rankTwo_regular` |
| two trivial blocks | `twoTrivialData` | `twoTrivial_not_regular` |
| orientation, weights `1, 1`, exponents `2, −1` | `orientationData` | `orientation_exponents`, `orientation_matches` (`![2, 0]` on the `z` side, `![1, −1]` on the `z̄` side), `orientation_regular` |
| orientation of the embedding indices | `orientationHighestWeight` | `embedding_false_reads_z`, `embedding_true_reads_zBar`, `orientation_matchesGlobal` |

`embedding_false_reads_z` and `embedding_true_reads_zBar` restate the published
`ArchimedeanGL.embeddingComponent_inr_false` and `ArchimedeanGL.embeddingComponent_inr_true`.
`orientationHighestWeight` puts `![2, 0]` at every `.inr (v, false)`, `![1, −1]` at every
`.inr (v, true)` and zero at the real indices, and `orientation_matchesGlobal` proves
`MatchesGlobalHighestWeight F 2 (fun _ => orientationData) orientationHighestWeight`. None of these
examples involves a center character, a realization or an automorphic representation.

## 5. Fields with real places

Only the totally complex forms are stated. At a real place the complex parameters say nothing:
`MatchesInfinitesimalCharacter` leaves the weights at the indices `.inl w` unrestricted. Over a
field with real places a family of complex parameters therefore cannot determine the whole
global center character or give the global regular algebraic equivalence of §3. No
general-field determination is claimed.

## 6. Sources and provenance

Registered source `clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`: Clozel,
*Motifs et formes automorphes*, in *Automorphic Forms, Shimura Varieties, and L-functions*,
Vol. I (1990). Printed and PDF pages differ by eleven.

- Definition 1.8, printed pp.89–90 (PDF pp.100–101): `π ∈ Alg(n)` when each archimedean parameter
  is `χ_1 ⊗ … ⊗ χ_n` with `χ_i(z) = z^{p_i+(n−1)/2} z̄^{q_i+(n−1)/2}`, `p_i, q_i ∈ ℤ`. The Remark
  after it identifies the center of `U(𝔤)` with `S(𝔥)^W`, `W = S_n × S_n` at a complex place, and
  the infinitesimal character of `π_v` with the pair of exponent vectors of the characters of
  its parameter, an element of `ℂ^{2n}`.
- Definition 3.12, printed p.111 (PDF p.122): `π` is regular when the entries of its type at
  infinity are distinct at every embedding, equivalently when its infinitesimal character is
  regular.
- Proof of Theorem 3.13, printed pp.112–113 (PDF pp.123–124): for
  `π_v = π_ℂ(z^{a_1} z̄^{b_1}, …, z^{a_n} z̄^{b_n})`, `a_i = p_i + (n−1)/2`,
  `b_i = q_i + (n−1)/2`; the dominant weight `m_ι = a − δ`, with `δ = ((n−1)/2, …, −(n−1)/2)`;
  `m_ῑ + δ = w_0 b`; and the infinitesimal character of `τ_ι ⊗ τ_ῑ` is `(m_ι + δ, m_ῑ + δ)`, equal
  to `(a, b)` modulo the Weyl group.

Clozel's integrality and regularity motivate the parameter condition; his shift and Weyl group
motivate the matching relation. The aggregate and the matching formulation are an internal
interface implementing the operator's explicit request for a named bridge. They do not claim
that Clozel states these Lean predicates. The formal normalization is that of the published
`Langlands/Automorphic/RegularAlgebraic.{lean,md}` and of Task 7455's definitions.

## 7. Relation to other Library work

- `Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter` proves that
  the actual local enveloping center acts by scalars on a complex standard module. It does not
  identify these scalars with the exponent and highest-weight formula above, and it does not
  relate the local center to `ArchimedeanGL.EnvelopingCenter`. That comparison remains an
  obligation of a proof of the bridge.
- Task 7435 (`6bc88750-e530-4fde-bca8-eecd80d4dc2e`,
  `Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport`) supplies the literal B7
  transport vocabulary. The bridge asserts neither weak base change compatibility nor
  weak induction.
- The original Harris statements and the cohomological A2 fallback are unchanged.
