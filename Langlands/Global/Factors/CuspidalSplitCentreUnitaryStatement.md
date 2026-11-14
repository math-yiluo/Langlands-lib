# Cuspidal realizations trivial on `A_GL` have unitary central characters

Author: Worker 3657.

Lean module: `Langlands.Global.Factors.CuspidalSplitCentreUnitaryStatement`.

This module states one proposition,
`Langlands.Global.CuspidalSplitCentreUnitaryCentralCharacterStatement`. It is a
`Prop`-valued `def`, a statement target and not a proof: the module contains no
theorem. It imports `Global.Factors.CuspidalPairPoleStatement` (for
`CuspidalPairPoles.IsTrivialOnSplitCentre`) and
`Automorphic.AssociatedFactorStatement` (for `HasUnitaryCentralCharacter`). It
changes no published file and introduces no new predicate.

## Why this module exists

The Library uses two normalizations for the centre of a cuspidal realization `T`
of `GL_{r+1}`:

- `CuspidalPairPoles.IsTrivialOnSplitCentre T` (published
  `CuspidalPairPoleStatement` and `CuspidalIsobaricPoleOrderStatement`). This is
  Getz–Hahn's normalization before Theorem 11.7.1: every function of `T` is
  invariant under the scalar matrices `a I_{r+1}` with `a ∈ A_(G_m)`.
- `HasUnitaryCentralCharacter T` (published `AssociatedFactorStatement`, full
  name `Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter`).
  This is the hypothesis of the proved theorem
  `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`
  (module `Automorphic.CuspidalUnitaryForm`) and of the published p-adic
  statement `CuspidalUnitaryLocalUnitarityStatement`.

A consumer that starts from the first normalization and wants to use results
stated under the second needs the implication between them. The Library has no
such lemma. The Markdown of `CuspidalPairPoleStatement` ("Relation to Cog04's
unitarity") describes this implication in prose. This module states it, so a
proof can be supplied as a separate task. The same gap is recorded by the
archimedean component statements (module
`Automorphic.CuspidalArchimedeanComponentStatement`, submitted by the same
author and under review when this module was written), which assume unitary
central characters while the published pole statement assumes triviality on
`A_GL`.

## Sources

- Getz and Hahn, *An Introduction to Automorphic Representations*, Graduate
  Texts in Mathematics 300, Springer, 2024 (registered source
  `getz-hahn-2024-automorphic-representations`, PDF
  `/home/taskhub/central-library/Getz-Hahn--An introduction to automorphic representations (book)--2024.pdf`;
  in Chapter 2 the PDF page is the printed page + 17, in Chapter 6 + 14, in
  Chapter 11 + 11).
  - Display (2.20), printed page 68 (PDF page 85): for a number field, `A_G` is
    the neutral component of the real points of the greatest `ℚ`-split torus in
    `Res_{F/ℚ} Z_G`. For `G = G_m` it is "the image of the diagonal embedding
    `ℝ_{>0} → F_∞^×`, regarded as a subgroup of `𝔸_F^×`", and
    `A_{GL_n} = {a I_n : a ∈ A_{G_m}}` (printed pages 68–69).
  - Lemma 2.6.2, printed page 69 (PDF page 86): for `G` reductive over a number
    field, `A_G G(𝔸_F)^1 = G(𝔸_F)` and `A_G ∩ G(𝔸_F)^1 = 1`. For `G = G_m` this
    says `𝔸_F^× = A_{G_m} · (𝔸_F^×)^1`, where `(𝔸_F^×)^1` is the group of ideles
    of norm one (display (2.19), printed page 68).
  - Display (2.21), printed page 69: `[G] := A_G G(F) \ G(𝔸_F)`.
  - Display (6.20), printed page 168 (PDF page 182): the cuspidal subspace
    `L²_cusp([G]) ≤ L²([G])`. Theorem 6.5.3, printed page 169 (PDF page 183):
    `A^{A_G}_cusp(π) = L²_cusp(π)_fin`, the space of `K`-finite vectors of the
    `π`-isotypic subspace of `L²_cusp([G])`, and `(π, V) ↦ (π, V_fin)` is a
    bijection from the irreducible subrepresentations of `L²_cusp([G])` to the
    cuspidal automorphic representations of `A_G \ G(𝔸_F)` (up to
    isomorphism). So such a representation is the `K`-finite part of a unitary
    representation, and its central character is unitary. This is the source
    of the implication stated here.
  - Printed page 309 (PDF page 320), before Theorem 11.7.1: "Thus without loss
    of generality we can assume that `π` (resp. `π'`) is trivial on `A_{GL_n}`
    (resp. `A_{GL_m}`)."

## Notation

- `F` is a number field with `[CompactSpace (AdeleQuotient F)]`, the instance
  required by `CuspidalOperatorRealization`.
- `T : Automorphic.CuspidalOperatorRealization F r` is an actual irreducible
  cuspidal subspace of automorphic forms on `GL_{r+1}`, as in the published
  module `Automorphic.CuspidalOperatorRealization`. Irreducibility makes its
  carrier nonzero (`CuspidalOperatorRealization.space_nontrivial`).
- `CuspidalPairPoles.IsPositiveArchimedeanScalar a` says that the idele `a` has
  finite component `1` and the same positive real number `t` at every infinite
  place. These ideles form GH's `A_{G_m}`.
- `CuspidalPairPoles.IsTrivialOnSplitCentre T` says that for every such `a`,
  every function `f` of `T` and every `x ∈ GL_{r+1}(𝔸_F)`,
  `f(a I_{r+1} · x) = f(x)`.
- `HasUnitaryCentralCharacter T` says that there is a continuous character
  `χ : F^× \ 𝔸_F^× → ℂ^×` with `‖χ(x)‖ = 1` for all `x` such that
  `T.HasCentralCharacter χ`: every function of `T` transforms by `χ` under the
  scalar ideles.

## Declaration

### `CuspidalSplitCentreUnitaryCentralCharacterStatement.{u}`

For every number field `F : Type u` with `[CompactSpace (AdeleQuotient F)]`,
every `r : ℕ` and every actual cuspidal realization
`T : CuspidalOperatorRealization F r`: if
`CuspidalPairPoles.IsTrivialOnSplitCentre T`, then
`HasUnitaryCentralCharacter T`.

## Correspondence with the sources

- **GH's representations against `T`.** GH's cuspidal automorphic
  representation `π` of `GL_n(𝔸_F)` trivial on `A_{GL_n}` is a cuspidal
  automorphic representation of `A_G \ G(𝔸_F)`, and Theorem 6.5.3 realizes it in
  `L²_cusp([G])`. The Lean `T` is a space of cusp forms on
  `GL_{r+1}(F) \ GL_{r+1}(𝔸_F)`. Its square-integrability modulo `A_G` is not
  part of the hypothesis. The statement asks only for the consequence that GH's
  realization in `L²` implies for the centre: the central character is unitary.
- **The central character.** GH do not name the conclusion separately. A
  unitary representation has a unitary central character when it has one, and
  an irreducible cuspidal realization has one (published
  `OperatorRealization.existsUnique_hasCentralCharacter`, module
  `Automorphic.IrreducibleCentralCharacterProof`). The statement does not
  presuppose that theorem; it asserts the existence of the character as part of
  the conclusion.
- **`A_{GL_n}`.** `IsTrivialOnSplitCentre` follows GH (2.20) for `G_m` and
  `GL_n`; its Markdown in `CuspidalPairPoleStatement.md` (section "`A_GL`")
  gives the comparison. Nothing about it is restated here.

## Relation to Library modules

- `CuspidalPairPoleStatement` and `CuspidalIsobaricPoleOrderStatement` use
  `IsTrivialOnSplitCentre`. A consumer that has these hypotheses obtains, from
  this statement, the hypothesis of the results below.
- `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`
  (module `Automorphic.CuspidalUnitaryForm`, proved) and the published
  statement `CuspidalUnitaryLocalUnitarityStatement` assume
  `HasUnitaryCentralCharacter`.
- `hasUnitaryCentralCharacter_of_associatedCentralCharacter` (module
  `Automorphic.AssociatedUnitaryCentralCharacter`) derives the same conclusion
  from a different hypothesis (an associated Weil-group representation). It is
  not a duplicate.
- `compactSpace_normOneIdeleClasses` (module `Global.NormOneIdeleClassCompact`,
  proved) gives the compactness of `F^× \ (𝔸_F^×)^1` that the proof needs.

## Why the statement is true

This is the intended argument; none of it is proved in this module.

1. `T` is irreducible, so it has a continuous central character
   `χ : F^× \ 𝔸_F^× → ℂ^×` (`existsUnique_hasCentralCharacter`). Thus
   `f(z · x) = χ(z) f(x)` for every idele `z`, function `f` of `T` and `x`
   (`OperatorRealization.centralCharacter_evaluate`).
2. `T` is nonzero, so some function `f` of `T` and some `x` have `f(x) ≠ 0`.
   For `a ∈ A_{G_m}`, triviality on `A_{GL_{r+1}}` gives
   `χ(a) f(x) = f(a x) = f(x)`, so `χ(a) = 1`.
3. Every idele `z` is `a · y` with `a ∈ A_{G_m}` and `|y| = 1` (GH Lemma 2.6.2
   for `G_m`): take `a` with the real number `t = |z|^{1/[F:ℚ]}` at every
   infinite place, since the idele norm of such an `a` is `t^{[F:ℚ]}`.
4. `x ↦ ‖χ(x)‖` is a continuous homomorphism to `ℝ_{>0}`. On the compact group
   `F^× \ (𝔸_F^×)^1` (`compactSpace_normOneIdeleClasses`) its image is a compact
   subgroup of `ℝ_{>0}`, hence `{1}`. By steps 2 and 3, `‖χ(z)‖ = 1` for every
   idele class `z`.

## Intended proof child

One `lean.proof` task: prove
`CuspidalSplitCentreUnitaryCentralCharacterStatement` by the four steps above.
Only proved Library results are needed.

## What is not asserted

- No converse. A cuspidal realization with unitary central character need not
  be trivial on `A_{GL_n}`: the character `|det|^{iσ}` with `σ ≠ 0` is unitary
  and not trivial on `A_{GL_n}` (`CuspidalPairPoleStatement.md`, "Relation to
  Cog04's unitarity").
- Nothing about twisting an arbitrary cuspidal realization to one trivial on
  `A_{GL_n}` (GH p. 309's "without loss of generality").
- Nothing about `L²` realizations, Hilbert-space completions or square
  integrability modulo `A_{GL_n}`.

## Provenance

Derived. GH realize cuspidal representations trivial on `A_G` inside
`L²_cusp([G])` (Theorem 6.5.3), and unitarity of their central characters is the
consequence used here. The Lean statement is the form of that consequence for
the Library's actual cuspidal realizations and its two published central
normalizations. The intended proof is the standard decomposition
`𝔸_F^× = A_{G_m} · (𝔸_F^×)^1` (GH Lemma 2.6.2) together with the compactness of
`F^× \ (𝔸_F^×)^1`.

## Lean checks

`lean_check` of the module compiles with no errors or warnings. The declaration
is a `Prop`-valued definition with universe parameter `u`, and it depends only on
the axioms `propext`, `Classical.choice` and `Quot.sound`.
