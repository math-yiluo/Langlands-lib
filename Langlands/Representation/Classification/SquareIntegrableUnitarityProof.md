# Unitarizability of square-integrable p-adic GL representations: proof

Author: Worker 438.

`Langlands.glSquareIntegrableUnitarity.{uF,uV}` proves exactly the closed
proposition `Langlands.GLSquareIntegrableUnitarityStatement.{uF,uV}` from
`Langlands.Representation.Classification.SquareIntegrableUnitarityStatement`.
The field and carrier universe parameters remain independent.

The theorem applies to every prime `p` with `Fact p.Prime`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, every
positive rank `n`, and every complex module `V : Type uV`. For the actual
representation `ρ : Representation ℂ (GeneralLinear n F.Carrier) V`,
irreducibility and the unchanged `T.IsSquareIntegrable ρ` imply
`IsUnitarizable ρ`, namely `Nonempty (InvariantPositiveForm ρ)` on the
original carrier.

## Implemented specialization

The proof introduces the statement's binders and installs `T.topology`.
It obtains the topological group, Hausdorff, locally compact and second
countable instances of the actual general linear group from the corresponding
`T.generalLinear...` declarations.

It installs `T.centralQuotientMeasurableSpace n` and
`T.centralQuotientBorelSpace n` on
`GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`.
These are the Borel measurable structure and quotient topology determined
by the supplied `T`. The theorem `T.exists_isHaarMeasure_centralQuotient n`
provides a measure `μ` and its Haar instance. The published
`glCentralQuotientHaarRightInvariant p F T n hn μ` supplies right invariance
of this same measure on this same full central quotient.

`GeneralLinear.compactOpen_cofinal F T n` supplies a compact open subgroup
inside every open subgroup of the actual general linear group. The
all-measures hypothesis `hsq : T.IsSquareIntegrable ρ` specializes to
`hsq μ : IsSquareIntegrableModCenter ρ μ`.

The proof now applies
`squareIntegrableUnimodularUnitarity.{uF,uV}` to this group, this compact-open
cofinality proof, the original `V` and `ρ`, the chosen `μ`, irreducibility
and `hsq μ`. All topological and measure hypotheses of that generic theorem
have thus been proved for the supplied field data. Its conclusion is exactly
the required `IsUnitarizable ρ`.

## The imported integral construction

The mathematical construction is implemented in the imported
`Langlands.Representation.Unitary.SquareIntegrableProof`. That proof extracts
smoothness, a scalar unitary central character `c` and the actual `L²`
coefficient hypotheses from `IsSquareIntegrableModCenter`. Compact-open smooth
bidual separation and irreducibility provide a nonzero
`ℓ : SmoothDual ρ`.

The published `c.coefficientProduct ℓ.1 u v` descends
`conj (ℓ.1 (ρ g u)) * ℓ.1 (ρ g v)` to the actual full central quotient:
the two central-character factors cancel by unitarity. Its continuity gives
measurability, and the two `L²` coefficient-norm bounds give integrability
by Hölder with exponents `2, 2`. The imported
`c.coefficientProductForm` integrates this function. Its Hermitian laws are
conjugate-linear in the first argument, as required by
`InnerProductSpace.Core ℂ V`. Right invariance of `μ` proves invariance of the
form under the given action.

The diagonal is the integral of the squared coefficient norm, hence is
nonnegative. A zero diagonal gives almost-everywhere vanishing. Continuity
and positivity of Haar measure on nonempty open sets make it vanish
everywhere. The coefficient kernel of the chosen nonzero functional is
a proper subrepresentation, so irreducibility makes it zero. This establishes
definiteness. The result is an actual `InvariantPositiveForm ρ` on `V`.
These steps are implemented by the imported generic proof; this file
specializes it without repeating those helpers.

## Dependencies and provenance

The direct imports are the unchanged target statement,
`Langlands.Representation.Unitary.SquareIntegrableProof`,
`Langlands.Representation.Category.Contragredient` and
`Langlands.Group.GL.CentralQuotientUnimodularityProof`. The latter proves
right invariance for the specified Borel quotient by applying the existing
GL central-quotient Haar theorem; it does not infer right invariance from
left invariance alone.

This is an internal specialization of those Library results to the published
GL target. Its source motivation is Casselman's *Introduction to the theory
of admissible representations of p-adic reductive groups*, draft of 1 May 1995,
§2.5, printed/PDF pp.28–29, Proposition 2.5.4, as documented in the target
and generic proof companions. The registered source is
`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The implemented conjugate-first form reverses Casselman's displayed
arguments and has the same diagonal.

The proof introduces no topology, norm, completeness or dimension bound on
`V`, no supplied functional or form, and no unitarity premise. It uses no
tempered-unitarity, tempered-exhaustion or equal-exponent-grouping result.
The analytic predicate, target pair and all imported existing pairs are
unchanged.
