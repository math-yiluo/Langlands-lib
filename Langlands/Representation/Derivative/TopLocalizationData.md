# Concrete matrix data for top character localization

This internal construction supplies actual subgroup copies, character
restrictions and determinant identities for comparing full upper-unipotent
character localization with the normalized top derivative. The algebraic
declarations assume `F : Type uF` and `[Field F]`; every natural rank is
allowed. The topological declarations additionally assume only
`[TopologicalSpace F]`. The final norm declarations specialize to every
`PadicField p` and every supplied `TopologicalData`.

This module constructs no representation quotient, tower equivalence, natural
isomorphism or rank-cast comparison. It makes no assertion about finiteness,
vanishing or dimensions of derivative or Whittaker spaces.

## Original convention and internal provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), §3.1, printed p.450 / PDF p.11, defines `P_r` by the final
row `(0,...,0,1)`, embeds `GL_(r-1)` by `diag(g,1)`, defines the radical
`V_r` by its first `r-1` identity columns, and uses the positive character
`theta(v) = psi(v_(r-1,r))`. These are the conventions of the unchanged
published matrix and character definitions used here. The source is registered
as `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
The original page was read and visually checked. No source-specific errata
note was found in the project notes, Library notes or
literature locations.

The Library's `mirabolic n F` is this `P_(n+1)` and `radical n F` is
`V_(n+1)`. Accordingly `Mirabolic.theta chi n` is on `V_(n+2)`.
`Whittaker.entrywiseCharacter psi d` is on the actual full upper-unipotent
subgroup of `GL_d`, including `d = 0`.

The results below are internal elementary derivations from the published
matrix definitions. Their field and all-rank generality is justified by the
implemented proofs. The original source fixes the convention and motivation;
no derivative, transitivity or classification theorem from it is assumed.

## The actual radical and smaller upper group

All new names are in `Langlands.Derivative.TopLocalization`.
Write `U_n = GeneralLinear.upperUnipotent n F`. The subgroup

```
upperLeviSubgroup n F = U_n.map levi
```

is inside the actual `mirabolic n F`, and `upperLeviSubgroup_le_upper`
places it inside `Mirabolic.upperUnipotent n F`. The proof reuses
`Whittaker.MirabolicQuotient.levi_mem_upperUnipotent`, whose proof checks
the smaller block, zero bottom entries and final diagonal entry.

`upper_eq_radical_sup` proves

```
Mirabolic.upperUnipotent n F =
  radical n F ⊔ upperLeviSubgroup n F.
```

For the forward inclusion, the published
`eq_radicalElement_mul_levi g` writes the actual matrix as
`u(lastColumn g) * levi(projection g)`. Its projection is in `U_n` by
`Whittaker.MirabolicQuotient.projection_mem_upperUnipotent`, proved by
reading the upper-left entries. Each factor belongs to its indicated
summand. The reverse inclusion uses the published radical inclusion and
`upperLeviSubgroup_le_upper`. No abstract semidirect decomposition or
representation theorem is used.

`upperProjection` restricts the actual upper-left `projection` to
`Mirabolic.upperUnipotent n F →* U_n`. `upperLevi` restricts `levi` in
the other direction, and `leviUpper` then forgets the redundant mirabolic
certificate to give `U_n →* U_(n+1)`. The `_val` lemmas record their
literal underlying matrices. `upperProjection_upperLevi` is the published
`projection_levi` with subtype extensionality.

`upperLeviEquiv : U_n ≃* upperLeviSubgroup n F` is `u ↦ diag(u,1)`;
its inverse is the actual projection. The right inverse unpacks membership
in the image and uses `projection_levi`. Both `_val` lemmas expose these
formulas.

For the successor step, `upperLeviSubgroup_le_successor` proves
`upperLeviSubgroup (n+1) F ≤ successorSubgroup n F`: every `U_(n+1)`
matrix lies in the smaller mirabolic by the published
`upperUnipotent_le_mirabolic`. `successorUpperSubgroup` takes the subgroup
copy inside this actual successor range, and
`successorUpperEquiv : U_(n+1) ≃* successorUpperSubgroup n F`
adds the two membership certificates. Its inverse again projects; its right
inverse uses two subtype extensionality steps and `projection_levi`.
`successorUpperSubgroup_map` proves that the image under the successor-range
inclusion is precisely `upperLeviSubgroup (n+1) F`. Thus these distinct
subtype groups are reconciled by explicit maps.

## Exact character restrictions

For every raw `psi : AddChar F ℂ`,
`superdiagonalSum_levi` proves that `diag(u,1)` has the same adjacent-entry
sum as `u : U_(n+1)`. Splitting the larger sum by
`Fin.sum_univ_castSucc`, its final term is zero by `levi_last`; every
earlier term is the smaller entry by `levi_first`.
`entrywiseCharacter_levi` consequently proves the exact homomorphism equality

```
(Whittaker.entrywiseCharacter psi (n+1)).comp leviUpper =
  Whittaker.entrywiseCharacter psi n.
```

Its `n = 0` case uses the published trivial rank-zero and rank-one
characters; its successor case applies the sum identity. No nontriviality,
unitarity or continuity is required for these two lemmas.

For a bundled `chi : UnitaryAdditiveCharacter F`,
`entrywiseCharacter_radical` proves

```
(Whittaker.entrywiseCharacter chi.complex (n+1+1)).comp
    radicalToUpperUnipotent = Mirabolic.theta chi n.
```

It rewrites with `entrywiseCharacter_eq_standardCharacter` and the
published `Mirabolic.theta_eq_standardCharacter_comp`. The latter is
proved from the fixed identity columns, which kill all adjacent entries
except the last. Both sides use the same positive character; no inverse or
complex conjugate occurs. The bundled character's continuity and
nontriviality are retained in this declaration's type.

## Inherited topologies

`continuous_upperProjection` and `continuous_upperLevi` compose the published
`continuous_projection` and `continuous_levi` with subtype inclusions and
codomain restrictions. `continuous_leviUpper` also composes the published
`upperUnipotentContinuousEquiv`.

`upperLeviContinuousEquiv` and `successorUpperContinuousEquiv` bundle exactly
the algebraic equivalences above. Their forward maps are restricted `levi`
maps; their inverses are restricted projections, with one or two subgroup
inclusions respectively. Only the topology on `F` is assumed. Continuity of
the imported projection uses coordinate extraction for both a matrix and its
inverse in the units topology; it requires no continuity of field inversion.

## Determinants and the published normalization characters

`determinant_upper` proves `GeneralLinear.determinant u.val = 1` for
every `u : U_n`. After extensionality on units, Mathlib's
`Matrix.det_of_isUpperTriangular` gives the product of diagonal entries.
Each is one by `UpperUnipotent.entry_diag`. This also proves the result
for the empty matrix.

For supplied `T : K.TopologicalData`, `determinantNorm_upper` unfolds the
published `T.determinantNorm n` as `T.normalizedAbsUnits` composed with
that determinant, and applies `map_one`. `realPowerCharacter_upper`
then uses the published `ker_le_realPowerCharacter_ker` to show triviality
for every real exponent `s`. Finally `realPowerCharacter_mirabolicUpper`
restricts the same determinant character along the actual mirabolic
inclusion and uses `upperUnipotentEquiv`:

```
realPowerCharacter
    ((T.determinantNorm (n+1)).comp (mirabolic n K.Carrier).subtype)
    s u.val = 1.
```

In particular this applies to `s = -(1/2)`, the determinant real-power
character in the published minus functor. No identification with a Haar
modulus, or inverse-half normalization bridge, is needed for this restriction
identity.

Every construction permits `n = 0`. The successor declarations at that
parameter concern `U_1` inside the successor range in `P_2`; the radical
character declaration concerns `V_2`. There is no declaration here that
replaces an arbitrary representation of the trivial `GL_0` by a
one-dimensional carrier. Representation carriers are absent from this module.

## Import and proof-dependency audit

The five direct imports are `Whittaker.MirabolicQuotientMeasure`,
`Derivative.MirabolicCharacter`, `Whittaker.EntrywiseCharacter`,
`Group.GL.NormalizedCharacter` and `Twist.RealPower` (with the common
`Langlands.Representation` prefix where applicable). Recursively reading their
actual project import declarations at Library commit
`81727e81ea12b8e578930ab79e9857e01bf72975` gave exactly the 65 modules listed
below; all 65 Lean/Markdown pairs also agree byte for byte with the later
Library commit `a081e0a279cb7346dce7f5afd3dee14f4fbaa60e`.

The actual new proof dependencies are the two entrywise membership lemmas
in `MirabolicQuotientMeasure`, the concrete factorization and projection
laws in `MirabolicProjection`, the subgroup and entry laws in
`MirabolicRadical`, `Mirabolic`, and `UpperUnipotent`, the two published
character equalities cited above, and the definitions and kernel law for
the determinant norm and real-power character. Their proof bodies are matrix
calculations, subgroup or units extensionality, finite sums, homomorphism laws
and continuity under composition. They contain no representation
classification or consumer conclusion.

Importing the existing membership lemmas also loads quotient-measure,
unimodularity and averaging infrastructure. That infrastructure constructs
group measures, translations and quotient integrals; none of its measure
results is used in the new proofs. The Whittaker interfaces in the closure
define character covariance, functional submodules and change of character;
they supply no forbidden finiteness or uniqueness theorem.
`Category.Basic.HasFiniteLength` is only a definition of finite composition
length, not a finite-length theorem and not used here. Occurrences of
`Module.finrank` in field normalization and `NormalizedCharacter` concern
field extensions or the residue field, not representation dimensions.

The following table audits every excluded family of results against
both the actual import closure and these proof dependencies. In each row,
the named conclusions, the modules that prove them and downstream consequences are absent
as proof inputs. The reasoning is substantive: no proof in this module takes
a representation as input or invokes a theorem about one.

| Excluded family | Audit result |
| --- | --- |
| `SegmentHeadProductIrreducibility`; `GenericSegmentProductUniqueness`; individual special-head/reverse-socle and segment-socle/reverse-head existence | No segment, head or socle module in the closure; only literal matrix subgroups and characters are used. |
| Multisegment exhaustion, ordered strong-head existence, quotient coverage, ordered conversion | No multisegment, ordering or coverage result; the image and join arguments are elementary subgroup arguments. |
| Tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable exhaustion, regular exhaustion, analytic segment classification, `SegmentSpecialEssentialSquareIntegrability` | No classification or square-integrability import or input. Group measure infrastructure is independent of these representation conclusions. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `SegmentSocleProductIrreducibility`, juxtaposed structure and quotient-Hom | No socle, irreducibility, product-structure or quotient-Hom theorem. The matrix product in the subgroup factorization is unrelated to products of representations. |
| Adjacent socle commutation, two-segment commutation, linked gluing, `OrderedMultisegmentSocleExistence`, socle exhaustion | No socle commutation, gluing or exhaustion module or proof input. |
| `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`; all segment derivative formulas | No segment/Jacquet formula or segment derivative input. `Jacquet.Localization` supplies only the general relation-quotient definitions used by the imported character module. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `TwoSupercuspidalProductStructure`; Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No two-supercuspidal, segment criterion, analytic or derivative-formula input. No BZ77 derivative theorem is assumed. No inverse-half/Haar bridge is imported. |
| `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`, the dependent mirabolic finite-length route, `SupercuspidalCoinvariantFinitenessStatement` | No representation finiteness premise or conclusion. The unused finite-length predicate and arithmetic degree facts described above are the only broad finite-length/finrank scan matches. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` | No classification module in the closure. In particular neither `UpperUnipotentCharacterFactorization` nor `TopDerivativeCoinvariantComparison`, whose closure reaches the vanishing half of `SupercuspidalDerivatives` (`Classification.SupercuspidalDerivativeVanishing`), is imported. The needed factorization instead comes from the elementary `MirabolicProjection` proof. |
| Plus, adjunction, duality, derivative filtration, pairing, or unproved general derivative comparisons | No such result is a proof input. The imported dual definitions merely describe linear functionals; no duality theorem is used. The tower equivalence and the top-derivative adapter are constructed separately, in `TopLocalizationStep` and `TopLocalizationComparison`. |

### Complete transitive project import list

The list excludes this new entry module and includes all five direct imports.

```text
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.RankOneQuotient
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentQuotient
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
