# Second adjointness from natural induction and Jacquet duality

Author: Worker 733.

This module derives normalized second adjointness
(`Langlands.Parabolic.NormalizedSecondAdjointnessStatement`, both the standard
`GL_n` clause and the refined product-Levi clause) from two published
statements, taken here as hypotheses:

- natural same-parabolic induction duality,
  `NaturalNormalizedInductionDualityStatement`
  (`Parabolic.NaturalInductionDualityStatement`), and
- natural upper/opposite Jacquet duality,
  `NaturalNormalizedJacquetDualityStatement`
  (`Parabolic.NaturalJacquetDualityStatement`).

The closing theorem is `Langlands.Parabolic.SecondAdjointness.secondAdjointness_of_dualities`.
It is conditional: this module proves neither duality statement and makes no
claim that they hold. The unconditional result is obtained only by applying it
to proofs of the two statements.

## Route

For admissible `σ` (on the Levi) and `π` (on the ambient group), write `D` for
the Library's `smoothContragredient`. The equivalence is the composite

\[
 \operatorname{Hom}(i_P\sigma,\pi)
 \xrightarrow{D} \operatorname{Hom}(D\pi, D(i_P\sigma))
 \xrightarrow{E_I\circ-} \operatorname{Hom}(D\pi, i_P(D\sigma))
 \xrightarrow{\text{first adj.}} \operatorname{Hom}(r_P(D\pi), D\sigma)
 \xrightarrow{-\circ E_J^{-1}} \operatorname{Hom}(D(r_{\bar P}\pi), D\sigma)
 \xrightarrow{D^{-1}} \operatorname{Hom}(\sigma, r_{\bar P}\pi).
\]

The ingredients are admissible Hom duality for the ambient group, the induction
duality equivalence `E_I`, first adjointness
(`Langlands.Representation.Parabolic.NaturalFirstAdjointness`), the Jacquet
duality equivalence `E_J`, and the inverse of admissible Hom duality for the
Levi. Casselman, Chapter III (`casselman-2019-jacquet-module`, revision April
29, 2019) supplies the source ingredients: III.1.1 (contragredient of an
induced representation), III.3.5 (Frobenius reciprocity) and III.6.2-3
(canonical pairing for Jacquet modules). The combined natural family and its
naturality proof are derived here; they are not a verbatim theorem of that
chapter.

## Generic helpers

Section `Generic`, for representations of a topological group `G`.

- `homDuality hcof hρ hσ`: for smooth `ρ`, admissible `σ` and compact open
  subgroups cofinal among open subgroups (`hcof`), the linear equivalence
  `Hom(ρ, σ) ≃ₗ[ℂ] Hom(Dσ, Dρ)` with underlying map `contragredientMap`.
  Bijectivity is the published `contragredientMap_bijective_of_bidual`. Its
  bidual hypothesis is supplied by `smoothBidual_injective_of_compact_cofinal`
  and `smoothBidual_surjective_of_compact_cofinal`. `homDuality_apply` records
  that the map is `contragredientMap` (by `rfl`).
- `postcomp E` and `precomp E`: postcomposition with an equivalence of
  representations and precomposition with its inverse, as linear equivalences
  of Hom spaces, with simp lemmas `postcomp_apply` and `precomp_apply`.

## Compact open cofinality

The `hcof` arguments use the existing cofinality theorems and the refined
transport in section `Cofinal`.

- `GeneralLinear.compactOpen_cofinal` from
  [`Category.Contragredient`](../Category/Contragredient.md) and
  `UnitaryDualJacquetSupport.levi_compactOpen_cofinal` from
  [`UnitaryDualJacquetSupportAdapters`](../Exponents/UnitaryDualJacquetSupportAdapters.md)
  supply the ambient and full-Levi cases. Both follow from the published
  compact open neighbourhood constructions.
- `refinedLevi_compactOpen_cofinal'` transports `T.leviCompactOpen` for the
  flattened block shape `B.flatten S` along the topological group isomorphism
  `flattenedLeviEquivContinuous F.Carrier B S` onto `refinedLevi F.Carrier B S`,
  with comaps of open subgroups and the image of a compact set under a
  homeomorphism. The ring topology instance on `F.Carrier` needed by that
  isomorphism is `IsModuleTopology.isTopologicalRing (Padic p) F.Carrier` for
  `T.moduleTopology`.

## Standard clause

Section `Standard`. The section variables `EI` and `EJ` are the equivalence
families of `StandardNaturalInductionDualityClause` and
`StandardNaturalJacquetDualityClause` for fixed `T` and `B`.

- `oppositeJacquetMap T B b` is the opposite Jacquet functor on an intertwiner
  `b : π → π'`, as an intertwiner of the representations
  `CuspidalJacquetMultiplicity.oppositeJacquet T B π`. Its underlying linear map
  is the pointwise `Jacquet.map` used in the statement, and
  `oppositeJacquetMap_apply` records this (by `rfl`). The intertwining property
  is taken from `Jacquet.normalizedMapOfModulus` with the same character, at
  `B.leviEquiv m`.
- `family T B EI EJ σ π hσ hπ` is the composite above. It uses
  `T.isSmooth_normalizedParabolicInduced`, `FirstAdjointness.equiv` (with
  smoothness of `Dπ` from `isSmooth_smoothContragredient`), and admissibility
  of the opposite Jacquet module from the published
  `Parabolic.isAdmissible_standardOppositeJacquet`.
- `contragredientMap_family`: the contragredient of `family … f` is
  `FirstAdjointness.equiv (E_I ∘ D f) ∘ E_J^{-1}`. This is the inverse law of
  the last `homDuality`.
- `family_inducedMap` takes the naturality hypothesis of `EI`. Since the last
  `homDuality` is injective, it suffices to compare contragredients. The
  `contragredientMap_family` lemma and the published `contragredientMap_comp`
  turn both sides into first-adjointness images. The naturality of `EI`, in
  pointwise form `h1`, moves `D(i_P a)` past `E_I` to `i_P(D a)`.
  `FirstAdjointness.equiv_inducedMap` then pulls `i_P(D a)` out as `D a`.
- `family_comp` takes the naturality hypothesis of `EJ`, with the same
  reduction to contragredients. `contragredientMap_comp` and
  `FirstAdjointness.equiv_comp` produce `r_P(D b) ∘ E_J(π')^{-1}`. The
  naturality of `EJ`, in the form `h2`, rewrites this as
  `E_J(π)^{-1} ∘ D(oppositeJacquetMap b)`. `h2` is checked by applying the
  injective `E_J(π)` and comparing the resulting functionals on each
  opposite-Jacquet vector.
- `standardSecondAdjointness_of_dualities` destructs both clauses at
  `(p, F, T, n, B)` and supplies `family` with the two naturality equations,
  evaluated at a vector.

## Refined clause

Section `Refined`. `EI` and `EJ` are now the families of the refined clauses for
fixed `T`, `B` and `S`. The inducing representation is an arbitrary
representation of `refinedLevi F.Carrier B S`, and the ambient one is a
representation of `B.Levi F.Carrier`.

- `refinedFamily`, `contragredientMap_refinedFamily`,
  `refinedFamily_inducedMap` and `refinedFamily_comp` repeat the standard
  constructions and proofs. They use `UnitaryDualJacquetSupport.levi_compactOpen_cofinal`,
  `refinedLevi_compactOpen_cofinal'`, `T.isSmooth_normalizedRefinedInduced`,
  `FirstAdjointness.refinedEquiv` and its naturality lemmas, and the published
  `isAdmissible_normalizedRefinedOppositeJacquet`. The ambient naturality uses
  the Library map `T.normalizedRefinedOppositeJacquetMap B S b` directly, as in
  the statement.
- `refinedSecondAdjointness_at` proves the refined conclusion for one `(B, S)`
  from given `EI`, `EJ` and their naturality, as an explicit anonymous
  constructor.
- `refinedSecondAdjointness_of_dualities` eliminates the two refined clauses
  with term-mode `Exists.elim` and applies `refinedSecondAdjointness_at`.
  Tactic `cases`/`obtain` on these clauses is very slow here: it exceeded the
  default heartbeat limit. The term-mode elimination fits within the default
  limit.

## Closing theorem

`secondAdjointness_of_dualities hI hJ` pairs the standard and refined results.
It preserves the independent universes `uF` (field), `uV` (inducing carrier)
and `uW` (ambient carrier). The induction duality statement is used at
`{uF, uV}`, and the Jacquet duality statement at `{uF, uW}`.
