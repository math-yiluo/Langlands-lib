# Actual splittings of the original CM kernel comparison

Author: Worker 57.

This derived construction proves that the original CM kernel pair is locally
Noetherian and applies the existing component lift to its identity. The result
is an actual section of the identical original kernel comparison. Packaging
this section gives a split epimorphism, and composing with it gives lifts from
every universe-zero scheme source. Exact representation and both named
relative-dual assertions remain hypotheses.

## Parameters and the original comparison

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic parameters are
universe-zero types: a totally real number field `E`, a quadratic CM
number-field extension `F`, the displayed algebra and scalar-tower structures
for `A`, `D : CentralSimpleUnitaryData E F A n`, an imaginary quadratic CM
number field `L` with its algebra map to `F`, and `τ₀ : L →+* ℂ`. The
signature charts `C` use exactly
`harrisCMSection E (algebraMap L F) τ₀`.

The explicit infrastructure inputs are tensor-pullback comparison preservation,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback, the Mumford-bundle assertion and universal
base change; dual-abelian base-change naturality; polarization base-change
stability; relative finite Weil transition; the rational/profinite-integer/adele
comparison; and torsion finite etaleness. The imported functor retains its
conjugated Harris–Taylor reflex normalization, positive auxiliary involution,
polarizations, Weil pairings, and rational-isogeny equivalence with an actual
rational inverse. Determinant and dimension conditions still hold on a common
representative. This module adds no dimension invariance assertion.

`R` is a family of the existing `CMLevelRepresentation` witnesses at every
`SmallCMLevel D`. These represent the fixed componentwise CM class presheaf
by the existing natural isomorphisms and include actual schemes, smoothness
and projective-space witnesses. Let `U V : SmallCMLevel D`, let
`hVU : V.obj.subgroup ≤ U.obj.subgroup`, and assume normality of
`V.obj.subgroup.subgroupOf U.obj.subgroup`.

Write `X_V` and `X_U` for the original represented schemes, `p` for
`representedCMNormalProjection R U V hVU`, and `Q` for
`SmallCMResidualGroup D U V`. The original copies scheme is the coproduct
of `X_V` over `Q`, and the original kernel pair is
`X_V ×[X_U] X_V`. The original comparison `κ` is exactly
`representedCMNormalKernelComparison R U V hVU`. Its restriction to summand
`g` is the original graph `(identity, ρ(g))` of the existing residual action.
All these objects and maps are imported unchanged.

The section and its consequences additionally take
`RelativeDualSchemeExistenceStatement.{0}` and
`RelativeDualSchemeGeometryStatement.{0}`. These are the same substantive
hypotheses used by the imported connected-source and component lifts:
universal Picard-zero duals over quasi-separated bases, and smoothness,
properness and geometric connectedness of those duals. They are not
instantiated here. Local Noetherianity of the original kernel pair itself
does not require these two hypotheses.

## Local Noetherianity and the implemented section

`representedCMNormalKernelPair_locallyNoetherian` obtains local
Noetherianity of the original `X_V` directly from
`(R V).base.property.locallyNoetherian`. It unfolds the original kernel pair
to `pullback p p` and applies Mathlib's locally Noetherian pullback instance.
The required `LocallyOfFiniteType p` follows from the existing
`representedCMNormalProjection_isProper`, since `IsProper` extends
`LocallyOfFiniteType`. That properness theorem uses the actual projective-space
witness and the original tower equation over `Spec F`. It has no etaleness
hypothesis. This argument does not use the separate finite-fiber or original
etaleness results.

The new instance admits the original kernel pair as a source for
`representedCMNormalKernelComponentLift`. Thus
`representedCMNormalKernelSection` is literally

```text
representedCMNormalKernelComponentLift ... R U V hVU existence geometry
  (𝟙 (representedCMNormalKernelPair ... R U V hVU)).
```

It is a morphism from the actual original kernel pair to the actual original
copies scheme. The imported lift assembles connected lifts on the actual open
connected-component schemes and retains nilpotents. No replacement scheme or
new representation family is introduced.

`representedCMNormalKernelSection_comp` is the existing component lift's
comparison equation at that identity. It proves the scheme-morphism equation

```text
section ≫ κ = 𝟙 (X_V ×[X_U] X_V).
```

Its reassociated equation is also a simp theorem.
`representedCMNormalKernelSplitting` constructs `SplitEpi κ` with exactly
this `section_` and equation. The proposition
`representedCMNormalKernelComparison_isSplitEpi` follows by
`IsSplitEpi.mk'` applied to that constructed splitting.

For every `T : Scheme.{0}`, with no local Noetherianity or connectedness
assumption, `representedCMNormalKernelComparison_allHom_surjective` gives
the lift `c ≫ section` of each `c : T ⟶ X_V ×[X_U] X_V`.
Associativity, the right-inverse equation and the identity law prove that its
composite with `κ` is `c`. Hence postcomposition with the original comparison
is surjective on these actual scheme Hom sets. Local Noetherianity was needed
only for the original kernel pair when constructing its section; this
corollary does not strengthen the earlier base-admission theorem.

## Identical chosen family and source scope

For `q : CMRepresentabilityStatement ...`, the entry
`cmNormalKernelSection` substitutes precisely
`chosenCMLevelRepresentation ... q` for `R`. This is the same family already
defining `cmSchemeTower ... q`. The value equation
`cmNormalKernelSection_eq` is reflexive equality with the existing chosen
`cmNormalKernelComponentLift ... q` of the original kernel pair's identity.
`cmNormalKernelSection_comp` uses the direct original
`cmNormalKernelComparison ... q`.

`cmNormalKernelSplitting` constructs a splitting of that identical comparison,
and `cmNormalKernelSplitting_section` is reflexive equality identifying its
section with `cmNormalKernelSection`. The theorems
`cmNormalKernelComparison_isSplitEpi` and
`cmNormalKernelComparison_allHom_surjective` specialize the corresponding
represented conclusions to the same family.

This is an internal deduction from `HarrisTaylorCMComponentKernelLift`,
the actual projective witnesses, the proved properness and Mathlib's
locally Noetherian pullback construction. The implemented proof is described
above. Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99, is
registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage defines the moduli values by products over connected components,
specifies the polarized CM frame-orbit moduli and right frame action, and
asserts smooth projective representability, finite-etale forgetting and the
normal `U/V` Galois cover. These are the conventions retained by the imported
objects. The new conditional splitting is not presented as the book's proof
of that stronger cover assertion. The supplied publication/errata list was
previously read in full and lists no correction to this passage.

No original-projection etaleness, rigidity, residual freeness, monomorphism of
`κ` or comparison isomorphism is assumed. Only the displayed right-inverse
identity is proved; this module proves no left-inverse identity or uniqueness
or naturality of the classical choices. The section belongs to `κ`, not to
the original forgetting projection `p`. Applicable representability,
source-smallness rigidity, comparison with the complete source moduli problem,
original etaleness, a full kernel inverse, canonical-model geometry and
coefficient descent remain separate obligations. This contribution does not
complete those source assertions or the host task.
