# Actual source model transports and comparison target

This derived module constructs the prescribed
model transports and states the exact remaining comparison of their
source-normalized character Haar and integrals.

## Source and preceding interfaces

Waldspurger (2003), registered `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
I.1, printed pp.240–241 (PDF pp.6–7), fixes the source measures.
VI.1, printed pp.295–296 (PDF pp.61–62), VI.3, printed pp.302–305
(PDF pp.68–71), and VII.2, printed p.319 (PDF p.85), use the actual
normalized coefficient sections, packets and inverse-degree products.
The Lean model adapters are internal constructions and precise
transport obligations for those source objects.

Declarations are in
`Langlands.HarishChandraSchwartz.RationalSemistandard.SourceModelComparison`.
The field is arbitrary nonarchimedean local, the ambient group is
affine, locally of finite type and connected reductive, and field and
representation-carrier universes are independent. Two actual
`LeviModel`s represent the same intrinsic all-test semistandard Levi.
The genuine cocharacter presentation, inducing representation and
compact picture are fixed throughout.

The exact preceding smoothness input is
`Langlands.HarishChandraSchwartz.RationalSemistandard.ModelSmoothComparisonStatement`,
from `RationalSemistandardOrbitSections`. The source split-center input `hc` is the actual equality
`m.splitCenter a = n.splitCenter b`. It is precisely the corresponding
instance of the same module's
`Langlands.HarishChandraSchwartz.RationalSemistandard.SplitCenterChoiceIndependenceStatement`
at the two models and their displayed algebraic split components.
Both are structural comparisons; this module neither proves them nor
makes them permanent external hypotheses. They are proved as
`modelSmoothComparison` (`RationalSemistandardModelSmoothComparisonProof`)
and `splitCenterChoiceIndependence`
(`RationalSemistandardSplitCenterIndependenceProof`).

## Prescribed transports and proved laws

`smoothModelChange` restricts the existing
`m.orbitSectionsModelEquiv n pi` to the two actual smooth submodules,
using the displayed `ModelSmoothComparisonStatement` witness.
Its value theorem identifies the restricted map with that exact
reindexing. Both sides use the same `CompactData`; no comparison across
different compact normalizations is silently imposed.

`unitaryModelHomeomorph` is the existing
`m.unitaryCharactersEquiv n` with continuous subtype maps. It fixes
every value of every actual unitary unramified character. The underlying
subgroup equality is the published equality of the actual norm kernels,
not a supplied character equivalence.

`quotientModelHomeomorph` uses `quotientContinuousMulEquiv` for the
identity automorphism of the literal Levi and the exact subgroup
equality `hc`. Its evaluation theorem fixes every quotient of a
literal Levi point. `quotientModelHaar` is the pushforward of the
original literal quotient Haar through this prescribed map. Its Haar
and inverse-invariance laws are proved; there is no separately chosen
second Haar normalization.

`squareIntegrable_modelHaar` proves square integrability of the same
actual inducing representation on that second quotient. It applies the
published `isSquareIntegrableModCentralSubgroup_comp_iff` to the literal
group identity and this exact Haar pushforward. The remaining
representation identity is proved by monoid-homomorphism extensionality.

`coefficient_model` proves equality of the actual normalized coefficient
at every inducing object before and after `smoothModelChange`, with
the source quotients and square-integrability witnesses just described.
The proof evaluates both coefficient maps at the same actual object
through `m.representativeModelEquiv n pi`; their underlying coefficient
values agree by reduction. No coefficient comparison map is supplied
as input.

## Exact remaining target

`ModelSourceComparisonStatement` is an **unproved Prop-valued target**.
The actual valuation-image finite-index conditions for both split
components remain explicit. Its first conclusion identifies the
pushforward of `SourceMeasure.unitaryCharacterHaar m a ...` through
`unitaryModelHomeomorph` with the actual source character Haar for
`n, b`. This preserves the original I.1 mass, without replacing either
Haar by a probability measure.

Its remaining conclusions, at a displayed actual source-special compact
equal to both the coefficient and scalar compacts, identify the actual
packet functions and `SourceForm.weightedOrbitForm` after
`smoothModelChange`. The second quotient Haar and square-integrability
witness are the prescribed constructions above. Both orbit integrals
use `SourceMeasure.normalizedOrbitMeasure`, retaining the reciprocal
unramified self-twist-stabilizer factor. The scalar data are the same
actual `OrbitPacketData r pi` on the same literal Levi: all preceding
reflection, central-split-character, compact-factorization,
continuation, open-domain, generic-irreducibility and full-unitary
inverse-regularity obligations remain visible.

The target concludes these actual measure and integral comparisons;
it does not take them as hypotheses. It adds no free map, weight,
Schwartz-valued synthesis or positive form. General compact-normalization
transports, inter-parabolic invariance and averaging require separate
prerequisites and constructions. The source formal-degree model target
(`RationalSemistandardSourceFormalDegree`) and the representative-integral
target (`RationalSemistandardSourceRepresentativeComparison`) are stated
separately. The first is proved as `formalDegreeTransport`; the Library has
no proof of the representative-integral target or of the model source
target.
