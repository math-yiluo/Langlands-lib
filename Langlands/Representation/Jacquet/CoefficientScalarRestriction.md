# Native coefficient representations and their actual complex Jacquet quotients

Worker 1755, with interface and reuse guidance from Worker 1751. Internal
scalar restriction and actual quotient comparisons for the coefficient-family
stability argument in Renard 2026 VI.9.2, printed p.199 / PDF p.205.
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The scalar-restriction and quotient-comparison constructions are derived
implementation content, not a new verbatim source statement.

Let `R` be a commutative complex algebra. The given additive group `V`
has both its native `R`-module and complex module structures, with
`IsScalarTower ℂ R V`. Let `σ : Representation R G V`.
All declarations are in `Langlands.Jacquet.CoefficientRestriction`.
The coefficient, group and representation-carrier universes are independent.

`complexRepresentation σ` restricts each actual group operator to complex
scalars on the same carrier. Its operator value is unchanged, and native
`R`-linearity gives `HasCompatibleCoefficients R` for the complex action.
`isSmooth_complexRepresentation` states equivalence of smoothness for
the two actions: the fixedness conditions are the same.
`complexFixedVectorsEquiv` is the identity on the fixed-vector carriers,
with their common native coefficient action.

`coefficientRelations_eq_native` identifies the complex Jacquet relation
set, regarded as an `R`-submodule by the earlier construction, with the
native `R`-relation submodule. For the forward inclusion, the native
relation submodule restricted to complex scalars contains each generator,
and hence the whole complex span. For the reverse inclusion, every native
generator belongs to the coefficient-stable complex relation submodule,
which therefore contains the whole `R`-span.

Equality of these actual submodules gives `coinvariantsEquiv`, the
coefficient-linear equivalence of the literal complex and native Jacquet
quotients. Its value on a quotient representative is the same native
quotient representative, by `coinvariantsEquiv_mk`.
`coinvariantsEquiv_action` proves that this equivalence intertwines the
actual unnormalized normalizer actions, by choosing a representative and
using their quotient action formulas.

`representationOverCoefficients` regards a compatible complex action as
an `R`-linear group action without changing its operator functions.
`jacquetRepresentationEquiv` packages the quotient equivalence as an
equivalence of the actual `R`-representations.
`jacquetFixedVectorsEquiv` restricts that equivalence to any subgroup of
the normalizing subgroup, giving the precise coefficient-linear fixed-space
comparison. None of these constructions uses finite generation or
Noetherianity.

The final corollary `compressedAction_eventuallyStable_of_native_finite`
additionally assumes that `R` is Noetherian, `σ` is smooth, `K` is compact
open, and the actual Iwahori contraction, normalizer and Levi-centrality
hypotheses hold. Its two representation-finiteness inputs are native
`Module.Finite R (fixedVectors σ K.toSubgroup)` and native finite generation
of `fixedVectors (action σ N M hMN) (K.toSubgroup.comap M.subtype)`.
The two fixed-space equivalences transfer these to the exact complex
carriers needed by the earlier localization criterion. That criterion then
proves `EventuallyStable` for the compact compressed action of the
restricted complex representation, with a positive exponent and both
kernel and range square equalities.

The two native coefficient-finiteness assertions remain hypotheses of
this corollary. They must be proved for the actual universal-family models
before applying it. No representation-uniform exponent or unconditional
instance of the host uniform stabilization theorem is supplied.
