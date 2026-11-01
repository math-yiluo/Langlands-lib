# Original CM kernel lifts on locally Noetherian scheme tests

Author: Worker 57.

This derived construction assembles the existing connected-source CM kernel
lifts over the actual open connected-component schemes of any locally
Noetherian source. Its composite with the identical original kernel comparison
is the given morphism. Consequently postcomposition with that comparison is
surjective on actual scheme Hom sets from every locally Noetherian source.
Disconnected, nonreduced and empty schemes are included.

## Parameters and original objects

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The universe-zero arithmetic
parameters are unchanged: a totally real number field `E`, its quadratic CM
number-field extension `F`, the algebra and scalar-tower instances for `A`,
`D : CentralSimpleUnitaryData E F A n`, an imaginary quadratic CM number field
`L` with its algebra map to `F`, and `τ₀ : L →+* ℂ`. The signature charts `C`
use exactly `harrisCMSection E (algebraMap L F) τ₀`.

The explicit infrastructure inputs are tensor-pullback comparison preservation,
composition, unit coherence, associativity, left-unitor comparison and symmetry;
Picard-zero pullback, the Mumford-bundle assertion and universal base change;
dual-abelian base-change naturality; polarization base-change stability;
relative finite Weil transition; the rational/profinite-integer/adele
comparison; and torsion finite etaleness. The imported class functor retains
its conjugated Harris–Taylor reflex normalization, positive auxiliary
involution, polarizations, Weil pairings and rational-isogeny equivalence with
an actual rational inverse. Determinant and dimension conditions remain on a
common representative. No dimension invariance under arbitrary rational
isogenies is added.

`R` supplies precisely one `CMLevelRepresentation` witness at each
`SmallCMLevel D`. These witnesses represent the fixed componentwise class
presheaf by its actual natural isomorphism; their representing schemes,
smoothness and projective-space witnesses are the existing ones. Fix
`U V : SmallCMLevel D`, the subgroup inclusion
`hVU : V.obj.subgroup ≤ U.obj.subgroup`, and normality of
`V.obj.subgroup.subgroupOf U.obj.subgroup`.

Write `X_V`, `X_U`, `p` and `Q` for the original represented fine and coarse
schemes, `representedCMNormalProjection R U V hVU`, and
`SmallCMResidualGroup D U V`. The domain of the original kernel comparison is
`representedCMNormalCopies R U V`, the coproduct of `X_V` over `Q`. Its target
is `representedCMNormalKernelPair R U V hVU`, the pullback
`X_V ×[X_U] X_V`. The comparison
`representedCMNormalKernelComparison R U V hVU` has on summand `g` the
original graph `(identity, ρ(g))`, where `ρ` is the existing residual left
action with its inverse-right frame convention. This module imports these
objects and maps unchanged.

Each lift additionally assumes
`RelativeDualSchemeExistenceStatement.{0}` and
`RelativeDualSchemeGeometryStatement.{0}`. As used by the imported connected
lift, these supply universal Picard-zero duals over quasi-separated bases and
their smoothness, properness and geometric connectedness. They remain named,
substantive hypotheses. The connected-source construction uses them to admit
arbitrary connected locally Noetherian schemes with their actual maps to
`Spec F`; it proves an equality of actual scheme morphisms.

## Assembly and implemented proof

Let `T : Scheme.{0}` be locally Noetherian and let
`c : T ⟶ X_V ×[X_U] X_V`. For every
`k : ConnectedComponents T`, `componentScheme T k` is the actual open
restriction of `T` with its original structure sheaf.
`componentι T k` is its original inclusion. These component schemes are
connected and locally Noetherian by the imported instances. They retain
nilpotents.

`representedCMNormalKernelComponentLift` is literally

```text
componentDesc T (fun k =>
  representedCMNormalKernelConnectedLift ... R U V hVU existence geometry
    (componentι T k ≫ c)).
```

The imported `componentDesc` assembles this family using the inverse of the
canonical coproduct isomorphism of the actual component schemes followed by
`Sigma.desc`. No arbitrary decomposition or new representing family is chosen.
The component index need not be finite or nonempty, and `T` need not be
quasi-compact or reduced.

`representedCMNormalKernelComponentLift_restrict` applies
`componentι_componentDesc`: its restriction to `componentScheme T k` is
exactly the existing connected lift of `componentι T k ≫ c`. Its
reassociated equation is also a simp theorem.

`representedCMNormalKernelComponentLift_comp` applies `component_hom_ext T`
to compare actual morphisms into the original kernel pair. On each component,
the restriction equation reduces the desired composite to the connected
lift followed by the identical original comparison.
`representedCMNormalKernelConnectedLift_comp` identifies this with
`componentι T k ≫ c`. Thus the assembled lift followed by the original
comparison equals `c` as a scheme morphism. The reassociated equation is again
provided as a simp theorem.

`representedCMNormalKernelComparison_locallyNoetherianHom_surjective` gives
this constructed lift for each `c`. It proves surjectivity of

```text
Hom(T, representedCMNormalCopies R U V)
  → Hom(T, representedCMNormalKernelPair R U V hVU),
d ↦ d ≫ representedCMNormalKernelComparison R U V hVU.
```

No connectedness or nonemptiness assumption on `T` occurs. In the empty case
the construction uses its actual empty component index and the same
coproduct reconstruction.

## Identical chosen tower and provenance

For the exact proposition `q : CMRepresentabilityStatement ...`,
`cmNormalKernelComponentLift` substitutes precisely
`chosenCMLevelRepresentation ... q` for `R`. This is the family already
defining `cmSchemeTower ... q` and `cmNormalKernelComparison ... q`.
The entry declaration is `cmNormalKernelComponentLift`.
`cmNormalKernelComponentLift_eq` is reflexive equality with the assembly of
the existing `cmNormalKernelConnectedLift ... q` on the original component
restrictions. The theorems `cmNormalKernelComponentLift_restrict`,
`cmNormalKernelComponentLift_comp` and
`cmNormalKernelComparison_locallyNoetherianHom_surjective` specialize the
three corresponding represented results. The comparison in these conclusions
is the direct original `cmNormalKernelComparison ... q`.

The construction is an internal deduction from
`HarrisTaylorCMSchemeTestTransitivity` and
`LocallyNoetherianComponentCoproduct`. The implemented route is the component
assembly and equality argument above. Harris and Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1,
printed pp.90–91, one-based PDF pp.98–99, is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 90 defines the moduli values on a disconnected locally Noetherian base
by the product over its connected components. Page 91 gives the polarized
CM frame-orbit moduli and the right frame action, and asserts smooth
projective representability, finite-etale forgetting and the normal `U/V`
Galois cover. Those are the original conventions retained by the imported
functor and maps. This derived lift is not attributed to the book as a proof
of its full cover assertion. The supplied publication/errata list was
previously read in full; it lists no correction to this passage.

The new lift uses no original-projection etaleness, coarse-object rigidity,
residual freeness or comparison `IsIso`. It proves no uniqueness or naturality
of the classical choices, equality with a separately chosen lift on a
connected source, section of the original projection, or full kernel
inverse. Applicable representability, source-smallness rigidity, comparison
with the complete source moduli problem, original etaleness, canonical-model
geometry and coefficient descent remain separate obligations. This
conditional construction does not complete those assertions or the host task.
