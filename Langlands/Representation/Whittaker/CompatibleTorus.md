# Character-compatible monomial representatives

Author: Worker 267.

This pair defines Shalika's character-compatibility condition for a matrix and the
set of diagonal parameters whose monomial representative satisfies it. It also proves
the elementary algebraic and topological laws of that set. All declarations are in
`Langlands.Whittaker`. They use the published actual matrix group
`Langlands.GeneralLinear (n + 1) R`, the published subgroup `upperUnipotent`, the
character `standardCharacter`, the permutation matrices `GeneralLinear.permutation`
and the diagonal map `GeneralLinear.Iwasawa.diagonalUnits`, all imported without
modification. No new matrix group, permutation matrix or diagonal map is defined.

## Source

The registered original is `shalika-1974-multiplicity-one`: J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974), 171–193.
The copy at
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Two passages are used:

- Printed p.174 (PDF page 5), property (1.5): fix `s ∈ N(H)`; if `χ(u) = χ(s u s⁻¹)`
  for all `u ∈ U_s = U ∩ s⁻¹ U s`, then `θ(s) = s`. Only the hypothesis of (1.5) is
  formalized here, as `IsCharacterCompatibleRepresentative`; its conclusion is not.
- Printed p.177 (PDF page 8), just before Proposition 1.13: for `w ∈ W`, `H_χ` is the
  set of `h ∈ H` with `χ(w h u h⁻¹ w⁻¹) = χ(u)` for all `u ∈ U_w⁺`, where
  `U_w⁺ = U ∩ w⁻¹ U w` (printed p.174). `compatibleTorus ψ n w` is this set, with `h`
  written as `Iwasawa.diagonalUnits d`.

In the proof of Proposition 1.13 Shalika uses the function
`h ↦ χ(w h u⁻¹ h⁻¹ w⁻¹) χ(u)` for fixed `u ∈ U_w⁺`. The function
`compatibilityDefect` below is `h ↦ χ(w h u h⁻¹ w⁻¹) χ(u)⁻¹`. Because `χ` is a
character, on `U_w⁺` this is the reciprocal of Shalika's function, so both equal one at
the same points. That reciprocal relation is a remark only; it is not stated in Lean.

## Conventions and signs

The source fixes a nontrivial additive character `ψ` of `k` and writes each character
of `U` as `χ(u) = ψ(a₁ x₁₂ + ⋯ + a_{n−1} x_{n−1,n})` (printed pp.173–174). In the
source, `θ` is the anti-automorphism of `G`, not a character. `standardCharacter ψ n u`
is `ψ` applied to `∑ i : Fin n, u i.castSucc i.succ`, the sum of the
first-superdiagonal entries. So it is the source's character for the supplied `ψ` with
every `aᵢ = 1`.

The parameter `ψ` has the imported type `UnitaryAdditiveCharacter R`. That bundle
makes `ψ` continuous, unitary and nontrivial: it has the field
`nontrivial : ψ.toAddChar ≠ 1`. So no declaration in this pair accepts a trivial
additive character. The proofs here never use the nontriviality field, but the
interface keeps it. The rank-one results below are a different matter: there the
superdiagonal sum is empty, so the induced character `standardCharacter ψ 0` is trivial
even though `ψ` is not.

`permutation m R w` is the published permutation matrix sending `e_j` to `e_(w j)`.
Its conjugation law, the imported `permutation_conjugate_entry`, gives entry
`g (w⁻¹ i) (w⁻¹ j)` at `(i, j)`. The source's matrix `w` is `permutation (n + 1) F w`
itself, not the matrix of `w⁻¹`, and the diagonal factor stands to its right:
`s(w, d) = permutation (n + 1) F w * Iwasawa.diagonalUnits d` is the source's `w h`.
Hence `s(w, d) * u * s(w, d)⁻¹` is the source's `w h u h⁻¹ w⁻¹`. The source's condition
`u ∈ U_w⁺` is the condition `p * u * p⁻¹ ∈ U` for `p = permutation (n + 1) F w` and
`U = upperUnipotent (n + 1) F`. This is the published `permutationUnipotentPlus`
of `Langlands.Group.GL.UpperBruhatCells`, reached through
`monomial_conj_mem_upperUnipotent_iff_mem_permutationUnipotentPlus`.
`monomial_conjugate_entry` proves the entry formula

`(s(w, d) * g * s(w, d)⁻¹) i j = d (w⁻¹ i) * g (w⁻¹ i) (w⁻¹ j) * (d (w⁻¹ j))⁻¹`.

So the adjacent entries seen by the defect are
`d (w⁻¹ k) * u (w⁻¹ k) (w⁻¹ k') * d (w⁻¹ k')⁻¹` with `k = i.castSucc`, `k' = i.succ`.

## Declarations

Write `U = upperUnipotent (n + 1) R`, `χ = standardCharacter ψ n`,
`p = permutation (n + 1) F w` and `s = p * Iwasawa.diagonalUnits d`.

| Lean name | Meaning |
| --- | --- |
| `IsCharacterCompatibleRepresentative ψ n s` | For all `u v : U`, `s * u.val * s⁻¹ = v.val` implies `χ u = χ v`. This is the hypothesis of (1.5): the pairs `(u, v)` range exactly over `u ∈ U ∩ s⁻¹ U s` and `v = s u s⁻¹`. It is a plain proposition with no extra fields. |
| `compatibleTorus ψ n w` | The set of `d : Fin (n + 1) → Fˣ` such that `IsCharacterCompatibleRepresentative ψ n (p * Iwasawa.diagonalUnits d)`; Shalika's `H_χ` for the matrix `p`. |
| `compatibilityDefect ψ n w u d` | The complex number `ψ.complex (∑ i : Fin n, (s * u.val * s⁻¹) i.castSucc i.succ) * (χ u : ℂ)⁻¹`. |

The predicate is defined for every commutative ring `R` with a topology, in any
universe. The topology is needed only because `UnitaryAdditiveCharacter R` requires
it. Here `s` is any invertible matrix, not only an element of the normalizer `N(H)`.
`compatibleTorus` and `compatibilityDefect` need a field `F` with a topology,
in any universe, since the published `Iwasawa.diagonalUnits` is stated over fields.
Continuity and closedness also assume `IsTopologicalRing F`. The rank is `n + 1`
for every `n`, so rank one (`n = 0`) is included. The conjugation lemmas hold in
every rank `m`, including `0`.

## Results

Lemmas on the predicate, over `R`:

- `isCharacterCompatibleRepresentative_iff` is the literal unfolding.
- `isCharacterCompatibleRepresentative_iff_complex` evaluates both sides as
  `ψ.complex` of first-superdiagonal sums, using `standardCharacter_apply` and
  injectivity of the coercion `ℂˣ → ℂ`.
- `isCharacterCompatibleRepresentative_iff_mul_eq` replaces the conjugation equation
  by `s * u.val = v.val * s`, via `mul_inv_eq_iff_eq_mul`.
- `isCharacterCompatibleRepresentative_iff_conj_mem` quantifies over `u : U` together
  with a proof `h` that `s * u.val * s⁻¹ ∈ U`, and compares `χ u` with `χ` of the
  conjugate packaged with `h`. The converse direction takes `h` from `v.property` and
  identifies the two subgroup elements by `Subtype.ext`.
- `isCharacterCompatibleRepresentative_one` shows the identity is compatible, since
  then `u = v`.
- `isCharacterCompatibleRepresentative_rankOne` shows every matrix is compatible in rank
  one. There the imported `standardCharacter_rankOne` makes the character trivial.

Monomial conjugation, over a field `F` in any rank `m`:

- `monomial_conjugate_entry` is the entry formula displayed above. The proof
  rewrites `s * g * s⁻¹` as `p * (D * g * D⁻¹) * p⁻¹` with `D = Iwasawa.diagonalUnits d`,
  using `mul_inv_rev`, `map_inv` and the `group` tactic. It then applies the imported
  `permutation_conjugate_entry` and `Iwasawa.diagonalUnits_mul_mul_apply`.
- `monomial_conj_mem_upperUnipotent_iff` proves
  `s * g * s⁻¹ ∈ upperUnipotent m F ↔ p * g * p⁻¹ ∈ upperUnipotent m F`.
  Both sides are compared through `mem_upperUnipotent_iff` and the two entry formulas.
  A strictly lower entry vanishes for one exactly when it vanishes for the other, since
  the unit factors are nonzero. The diagonal entries agree, because
  `d k * x * (d k)⁻¹ = x`.
- `monomial_conj_mem_upperUnipotent` is the forward implication required by the task:
  if `p * g * p⁻¹ ∈ U` then `s * g * s⁻¹ ∈ U` for every `d`.
  `permutation_conj_mem_upperUnipotent_of_monomial` is the converse.
- `monomial_conj_mem_upperUnipotent_iff_mem_permutationUnipotentPlus` shows, for
  `u : upperUnipotent m F`, that `s * u.val * s⁻¹ ∈ upperUnipotent m F` iff
  `u.val ∈ permutationUnipotentPlus m F w`. This combines the previous equivalence
  with the imported `mem_permutationUnipotentPlus_iff`.

The compatible locus:

- `mem_compatibleTorus_iff` is the literal membership equivalence.
- `mem_compatibleTorus_iff_conj_mem` gives membership iff, for every `u : U` with
  `p * u.val * p⁻¹ ∈ U`, `χ u` equals `χ` of `s * u.val * s⁻¹`. The membership proof
  for the conjugate is `monomial_conj_mem_upperUnipotent`. Since the hypothesis on `u`
  does not involve `d`, the set of tested `u` is the same for every `d`.
- `mem_compatibleTorus_iff_permutationUnipotentPlus` is Shalika's `H_χ` form: for all
  `u : U` with `u.val ∈ permutationUnipotentPlus (n + 1) F w`,
  `χ(s * u.val * s⁻¹) = χ u`.
- `compatibleTorus_rankOne` shows the locus is all of `Fin 1 → Fˣ` in rank one.

The defect and closedness:

- `compatibilityDefect` is defined for every `u : U`. This is an internal convenience,
  so that the equalizers below are indexed by a subgroup element and a proof.
  Outside `U_w⁺` its first factor is just a complex number attached to the matrix
  `s * u.val * s⁻¹`, and no meaning is claimed for it.
- `compatibilityDefect_eq_div` shows that, when `p * u.val * p⁻¹ ∈ U`, the defect is
  `(χ ⟨s * u.val * s⁻¹, _⟩ : ℂ) / (χ u : ℂ)`, the ratio of the two actual unipotent
  character values. This holds by unfolding `standardCharacter_apply`.
- `compatibilityDefect_eq_one_iff` shows that, under the same hypothesis, the defect
  equals one exactly when the two character values are equal. The denominator is the
  value of a unit, hence nonzero.
- `mem_compatibleTorus_iff_defect`: `d ∈ compatibleTorus ψ n w` iff
  `compatibilityDefect ψ n w u d = 1` for every `u : U` with `p * u.val * p⁻¹ ∈ U`.
- `compatibleTorus_eq_iInter` writes the locus as
  `⋂ u, ⋂ (_ : p * u.val * p⁻¹ ∈ U), {d | compatibilityDefect ψ n w u d = 1}`.
- `continuous_compatibilityDefect` assumes `IsTopologicalRing F` and proves continuity
  in `d` for fixed `u`. `Fin (n + 1) → Fˣ` carries the product of Mathlib's topology on
  `Fˣ`. The map `d ↦ s * u.val * s⁻¹` is continuous by the published
  `continuous_diagonalUnits` and continuity of multiplication and inversion in the
  topological group `GL_(n+1)(F)`. Each entry is continuous by the published
  `GeneralLinear.entry`, and `ψ.complex` is continuous by `ψ.continuous_complex`.
- `isClosed_compatibleTorus` assumes `IsTopologicalRing F` and proves that the locus is
  closed. It is an intersection of preimages of the closed point `1 ∈ ℂ` under
  continuous maps. No local constancy of any character is used or claimed.

A final `example` applies `isClosed_compatibleTorus` to every canonical
`PadicField.{uF} p`, with the topology installed by `F.canonicalNormedField`.

## Provenance and scope

The predicate and the locus are the source's notions, as described above. The
following are internal elementary additions, not theorems of the source: the
commutative-ring and arbitrary-matrix generality of the predicate, the field
generality of the locus, the arbitrary-rank conjugation lemmas, the defect function as
a total function, and the continuity and closedness results.

The pair does not prove the conclusion `θ(s) = s` of (1.5), or that compatible
representatives are fixed by any anti-automorphism. It does not prove that any Bruhat
cell is stable, or give any combinatorial description of the locus. Nor does it prove
Proposition 1.13 or any support or vanishing statement for distributions. None of these
appears as an assumption or a field. No imported pair is modified.
