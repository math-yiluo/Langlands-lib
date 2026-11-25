# Pseudo-coefficients of square-integrable representations from the twisted statement

This module proves that the Library statement
`PseudoCoefficientExistenceStatement` (Kazhdan 1986, Theorem K(a), with a
fixed central character as in Henniart–Lemaire 2011, II.5.13, for `E = F`,
`σ = 1`) follows from two premises:

1. `TwistedPseudoCoefficientExistenceStatement` (Library), at the universes `.{v, v, w}` (both fields in the same
   universe);
2. `SquareIntegrableNotInducedStatement` (module
   `Langlands.BaseChange.SquareIntegrableNotInducedStatement`): an irreducible
   square-integrable representation of `GL_n(F)` is not isomorphic to a
   representation smoothly induced from a proper standard block parabolic
   subgroup.

Neither premise is proved here. The reduction is the specialization `E = F`,
`σ = 1`, `l = 1` of the twisted statement, with the identity intertwiner, as
in HL II.1.7 (printed p. 59: for `E = F` and `σ = Id` the σ-discrete series
are the discrete series) and HL II.5.13.

## Declarations

### Generic: twisted pseudo-coefficients for `θ = id`

`isPseudoCoefficient_of_isTwistedPseudoCoefficient_of_eq_refl`: for a group
`G` with the topological and measure-theoretic structure of the Library's
`IsPseudoCoefficient`, an automorphism `θ : G ≃* G` with
`θ = MulEquiv.refl G`, an intertwiner `A : π ≅ π ∘ θ` whose underlying linear
map is the identity, and a twisted pseudo-coefficient `f` of `(π, A)` for `θ`,
`f` is a pseudo-coefficient of `π`. Proof: substitute `θ = refl` (the equation
is a hypothesis, so `subst` applies) and use the Library's
`isPseudoCoefficient_of_isTwistedPseudoCoefficient_refl`.

### `σ = 1` on `GL_n`

- `entrywiseAut_one_eq_refl`: the entrywise action `entrywiseAut 1 n` of the
  identity automorphism of `F` on `GL_n(F)` equals `MulEquiv.refl`; by
  extensionality from the Library's `entrywiseAut_one_apply`. This equality is
  propositional, not definitional, which is why the generic lemma above takes
  `θ = refl` as a hypothesis.
- `sigmaIntertwinerOne n π : SigmaIntertwiner 1 n π`: the identity linear
  equivalence of `V`, as an isomorphism from `π` to `π ∘ entrywiseAut 1 n`;
  compatibility with the actions is `entrywiseAut_one_apply`.
- `sigmaIntertwinerOne_toLinearMap`: its linear map is `LinearMap.id`
  (by `rfl`).

### Square-integrable implies σ-discrete series for `σ = 1`

- `isTemperedRep_of_isSquareIntegrable`: a square-integrable representation
  of `GL_n(F)` (`JacquetLanglands.IsSquareIntegrable`) is tempered
  (`IsTemperedRep`). `IsSquareIntegrable` quantifies over Haar measures on
  `GL_n(F)/Z` for the Borel σ-algebra, and so does `IsTemperedRep`; for each
  such measure the Library's `isTemperedModCenter_of_squareIntegrable`
  (`Langlands.Representation.Classification.LeviDiscreteSeriesTemperedProof`)
  turns square-integrability modulo the centre into temperedness modulo the
  centre.
- `isSigmaDiscreteSeries_one_of_isSquareIntegrable`: assuming
  `SquareIntegrableNotInducedStatement.{u, uV}`, an irreducible
  square-integrable representation `π` of `GL_n(F)`, `F` of characteristic
  zero, satisfies `IsSigmaDiscreteSeries 1 n π`. The five clauses:
  admissibility (part of `IsSquareIntegrable`), irreducibility (hypothesis),
  temperedness (previous lemma), σ-stability (`sigmaIntertwinerOne`), and
  non-inducedness from the premise (the extra hypothesis
  `IsLeviSigmaStable 1 B Ξ` is not used).

### The reduction

`PseudoCoefficientExistenceReductionStatement.{v, w} : Prop` is

`TwistedPseudoCoefficientExistenceStatement.{v, v, w} →
SquareIntegrableNotInducedStatement.{v, w} →
PseudoCoefficientExistenceStatement.{v, w}`,

and `pseudoCoefficientExistenceReduction` proves it for all universes. Proof:
given `F`, `n`, `V`, `π`, `hπ`, irreducibility, square-integrability, the
central character `χ` and a Haar measure `μ` on `GL_n(F)`, apply the twisted
statement with `E = F`, `σ = 1`, `l = 1` (`isCyclicAlgebra_one`), the
σ-discrete-series property from the previous section, the same `χ`, the
intertwiner `sigmaIntertwinerOne n π` and `μ`. It gives
`φ : SchwartzBruhat (GL_n(F))` that is a twisted pseudo-coefficient for
`entrywiseAut 1 n`; the generic lemma, with `entrywiseAut_one_eq_refl` and
`sigmaIntertwinerOne_toLinearMap`, makes `φ` a pseudo-coefficient of `π`.

The instances agree without rewriting. The twisted statement, at `E = F`, uses
`IsTopologicalRing F` and `IsModuleTopology F F` (found by instance search),
the Borel σ-algebra on `GL_n(F)` and the topology lemmas
`generalLinear_*_of_finite F F n`. The target uses the Borel σ-algebra and
`LocalFieldTopology.generalLinear_*`. The topology on `GL_n(F)` is the same,
and the facts are propositions, so the proof terms are interchangeable.

## Provenance

Derived and internal: a conditional reduction of the Library statement
`PseudoCoefficientExistenceStatement` to the Library statement
`TwistedPseudoCoefficientExistenceStatement` and the new premise
`SquareIntegrableNotInducedStatement`. HL II.1.7 identifies the σ-discrete
series with the usual discrete series for `E = F` and `σ = Id`. For this
specialization and the **identity** intertwiner `A`, the twisted character
is the ordinary character: HL II.2.7 (printed p. 67, PDF p. 75) gives
`Θ^A_π(f) = trace(π(f) ∘ A)`, which then equals `trace(π(f))`.
