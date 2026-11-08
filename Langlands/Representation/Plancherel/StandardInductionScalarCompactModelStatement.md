# Conditional compact-model independence of actual canonical scalars

## Declaration and provenance

`Langlands.Plancherel.ConditionalStandardInductionScalarCompactModelStatement`
is a proposition-valued definition, specifying an exact proof target. This
contribution states the target; it does not prove it.

This is an internal independence target for the published construction
`standardInductionCompositeCanonicalRationalScalar` in
`StandardInductionCanonicalScalar`. It compares two compact realizations of
the same actual normalized inductions and the same actual standard integral
operators. It makes no new claim of translation from the original literature.
Its purpose is to remove the auxiliary compact subgroup from this particular
canonical rational fraction. The actual compact-model equivalences and their
polynomial transition families provide the intended comparison route; those
transitions depend on the unramified parameter.

## Fixed mathematical setting

The scalar field of the representations is the complex numbers. The local
field `F` is arbitrary among the nonarchimedean local fields in the existing
interface, with no characteristic-zero or splitness restriction. The field,
ambient-group and representation-carrier universes are independent.

The displayed inputs are a connected reductive group scheme `L` over `F`,
a topology on its actual rational points and continuity of the rational
valuation-image projection, and a locally compact, Hausdorff, nonarchimedean
group `G`. The target also assumes that `G` is separable. An actual
multiplicative homeomorphism `e` identifies the rational points of `L` with
the literal Levi subgroup `M` of `G`. The norm family consists of the actual
rational norm characters of `L`, with their continuity supplied, transported
to `M` along `e`.

The two literal parabolic subgroups `P₀`, `P₁`, their common literal Levi `M`,
and their radicals `U₀`, `U₁` are fixed. Both semidirect decompositions, closed
parabolics, closed radicals, closed Levi, continuous Levi projections and
radical unimodular-modulus hypotheses are explicit. The same canonical
`SmoothRep` inducing representation `A` is used throughout.

The quotient measures in both directions and all four radical/intersection
Haar measures are fixed. Their measurable and Borel structures, regularity,
right invariance, quotient-integration compatibility and the two squared
modulus compatibility hypotheses are displayed. Neither measures nor the
normalization are changed in the comparison.

There are two compact open subgroups `K₀`, `K₁`, with their compactness and
all four factorizations `G = Pᵢ Kⱼ` supplied. No containment or conjugacy
between `K₀` and `K₁` is required. Their actual compact pictures share the
same ambient normalized induced representation at every parameter.

## Continuation and irreducibility hypotheses

For each compact model, the target quantifies over independent whole-operator
continuation data in both directions: `p₀`, `q₀`, `p₁`, `q₁`. Each is
`RationalOperatorContinuationData` for the compact conjugation of the actual
`standardInductionIntertwinerFamily` on its original
`standardIntertwiningFullDomainRegion`. This is not an arbitrary operator
family. These original full domains use the ambient induced carriers and
therefore do not depend on the compact subgroup. They require both the scalar
integrals and their representability in the target original induced carrier.
The four continuation numerators and denominators are not identified or
assumed compatible.

For each model and direction the statement retains an independently chosen
nonempty open subset of the corresponding original full domain. In `Dⱼ₁₀`
and `Dⱼ₀₁`, the first subscript labels the compact model and the last two
subscripts label the direction. These subsets need not intersect each other.
In particular, the statement does not assume simultaneous convergence of the
two opposite-direction integrals on a nonempty set.

A nonempty open subset `D₀` consists of parameters at which the actual
`P₀` normalized induction of the twist of `A` is irreducible. A separate
nonempty subset `D₁` of irreducible parameters may select the second canonical
extraction; `D₁` need not be open. The actual induction in these hypotheses is
independent of the compact subgroup. This is generic induced irreducibility,
not an assumption that every tempered induction is irreducible. There is no
requirement that an irreducibility subset intersect a convergence subset.

No scalarity premise, comparison square, polynomial transition premise or
coefficient normalization chosen by the caller is included. The coefficients
are chosen internally by the existing canonical construction.

## Conclusion and limits

The conclusion is equality in `rationalUnramifiedFunctionField L hp hL` of
`standardInductionCompositeCanonicalRationalScalar` computed using
`K₀`, `p₀`, `q₀` and the first witnesses, and the same construction using
`K₁`, `p₁`, `q₁` and the second witnesses. This compares actual rational
fractions, rather than just values on one chosen regular region.

This target assumes initial whole-operator continuations, nonempty open
convergence subsets, generic induced irreducibility and the displayed generic
structural and measure inputs. It does not establish those assumptions or
their rational-point realizations. It changes neither the inducing
representation, the parabolic pair nor measures. It neither identifies the
fraction with source-normalized `j` or `mu`, nor states nonvanishing,
positivity, Weyl invariance, parabolic independence, the Plancherel formula or
completion of the standing program. Proof and independent publication of
this target remain required.
