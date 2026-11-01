# Original CM kernel scheme isomorphisms without original etaleness

Author: Worker 57.

This derived construction gives a full scheme inverse for the original CM
kernel comparison under exact representations, both named relative-dual
assertions and explicit geometric coarse rigidity. Its forward map is
reflexively the original comparison, and its inverse is reflexively the
already constructed actual section. Original projection etaleness is not a
premise.

## Parameters and unchanged objects

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The universe-zero arithmetic
inputs are a totally real number field `E`, its quadratic CM number-field
extension `F`, the displayed algebra and scalar-tower structures for `A`,
`D : CentralSimpleUnitaryData E F A n`, an imaginary quadratic CM number
field `L` with its algebra map to `F`, and `τ₀ : L →+* ℂ`. The signature
charts `C` use exactly
`harrisCMSection E (algebraMap L F) τ₀`.

The named infrastructure inputs remain tensor-pullback comparison preservation,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback, the Mumford-bundle assertion and universal
base change; dual-abelian base-change naturality; polarization base-change
stability; relative finite Weil transition; the rational/profinite-integer/adele
comparison; and torsion finite etaleness. The imported moduli functor retains
its conjugated Harris–Taylor reflex normalization, positive auxiliary
involution, polarizations, Weil pairings and rational-isogeny equivalence with
an actual rational inverse. Its determinant and numerical conditions remain
on a common representative. No dimension invariance under arbitrary rational
isogenies is introduced.

`R` is a family of `CMLevelRepresentation` witnesses, one for each
`SmallCMLevel D`, representing the fixed original componentwise CM class
presheaf by its exact natural isomorphisms. These witnesses include actual
schemes, smoothness and projective-space data. Fix
`U V : SmallCMLevel D`, the original subgroup inclusion
`hVU : V.obj.subgroup ≤ U.obj.subgroup`, and normality of
`V.obj.subgroup.subgroupOf U.obj.subgroup`.

Write `X_V`, `X_U`, `p` and `Q` for the original represented fine and coarse
schemes, `representedCMNormalProjection R U V hVU`, and
`SmallCMResidualGroup D U V`. The copies scheme `C_Q` is exactly
`representedCMNormalCopies R U V`, the coproduct of `X_V` over `Q`. The
kernel pair `K` is exactly `representedCMNormalKernelPair R U V hVU`,
the pullback `X_V ×[X_U] X_V`. Write `κ` for the identical original
`representedCMNormalKernelComparison R U V hVU`. On summand `g`, this is
the original graph `(identity, ρ(g))`, where `ρ` is the existing residual
left action with its inverse-right frame convention. No replacement
coproduct, action, pullback or comparison is introduced.

The explicit hypotheses
`RelativeDualSchemeExistenceStatement.{0}` and
`RelativeDualSchemeGeometryStatement.{0}` are the same ones used by the
imported lifts and geometric stabilizer theorem: universal Picard-zero duals
over quasi-separated bases and their smoothness, properness and geometric
connectedness. They remain substantive named premises, not constructions
instantiated in this module.

`hRigid` is exactly
`CMGeometricCoarseRigidity ... U.obj`. It asserts the existing
`CoarseLevelHasNoAutomorphisms` condition at every admitted spectrum of an
algebraically closed universe-zero field, with its actual structure morphism
to `Spec F`, identity geometric point, torsion conditions and original
representative tests. This hypothesis is not inferred from `SmallCMLevel`
or its local torsion-free smallness. No rigidity statement on arbitrary
scheme bases is added.

## Actual Hom injectivity

`representedCMNormalKernelComparison_connectedHom_injective` considers
actual morphisms `d,e : T ⟶ C_Q` from any connected universe-zero scheme
`T`, without local Noetherianity or reducedness. The generic
`connectedHom_factor_coproduct` factors each into an actual summand:

```text
d = a ≫ Sigma.ι g,     e = b ≫ Sigma.ι k.
```

If `d ≫ κ = e ≫ κ`, composing with the first original kernel projection
and using the proved graph equations gives `a = b` as scheme morphisms.
The second original projection then gives `a ≫ ρ(g) = a ≫ ρ(k)`.
Connectedness includes nonemptiness, so `HarrisGeometricPoint.ofResidue`
constructs the spectrum of an algebraic closure of a residue field and its
actual morphism `z.hom` to `T`. Precomposing the last equality with `z.hom`
lets the existing
`representedCMGeometricPoint_normalTranslate_injective`, under `hRigid`
and both dual hypotheses, prove `g = k`. Replacing these two indices and
`a = b` proves `d = e` as actual scheme morphisms.

The geometric point is used only to identify the residual indices. The
first-projection equality already determines the complete scheme morphism
to the fine level, including its structure-sheaf map. This does not discard
nilpotents or infer morphism equality merely from equality on geometric
points.

`representedCMNormalKernelComparison_locallyNoetherianHom_injective`
restricts `d` and `e` to every actual open connected-component scheme of a
locally Noetherian `T`. The preceding result gives equality on each
component, and `component_hom_ext` proves the original morphisms equal.
Disconnected, nonreduced and empty locally Noetherian sources are included.

## Monomorphism on all scheme tests

`representedCMNormalCopies_locallyNoetherian` uses the original summand
open cover `sigmaOpenCover` of `C_Q`. Each member is `X_V`, whose local
Noetherianity is supplied by
`(R V).base.property.locallyNoetherian`. The theorem
`isLocallyNoetherian_iff_openCover` therefore proves that the actual copies
scheme is locally Noetherian. No finiteness argument about `Q` is needed.

`representedCMNormalKernelComparison_locallyOfFiniteType` unfolds `κ`
to its original `Sigma.desc` of the original graph maps. Each graph is a
closed immersion by the existing
`representedCMNormalGraph_isClosedImmersion`, which uses the original
proper projection and its graph identities without original etaleness.
Thus every graph is locally of finite type.
`IsZariskiLocalAtSource.sigmaDesc` proves the same for the identical
original `κ`. Neither this instance nor the copies local Noetherianity
instance requires the relative-dual or rigidity hypotheses.

It follows by Mathlib's locally Noetherian pullback instance that the actual
self-pullback `P := C_Q ×[K] C_Q` of `κ` is locally Noetherian.
`representedCMNormalKernelComparison_mono_of_dualGeometry` applies the
proved locally Noetherian Hom injectivity with source `P` to its two
projections. The pullback condition gives equal composites with `κ`, hence

```text
pullback.fst κ κ = pullback.snd κ κ.
```

For arbitrary `T : Scheme.{0}` and `a,b : T ⟶ C_Q` with
`a ≫ κ = b ≫ κ`, their actual pullback lift into `P`, followed by the
two now equal projections, recovers `a` and `b`. This proves categorical
`Mono κ` on all scheme tests. No restriction on this final arbitrary `T`
is made.

## Constructed inverse and identical chosen specialization

The existing `representedCMNormalKernelSection ... existence geometry`
is an actual morphism `s : K ⟶ C_Q` with proved equation
`s ≫ κ = 𝟙 K`. It was constructed by applying the actual component lift
to the identity of the original locally Noetherian `K`.

`representedCMNormalKernelSchemeIso` sets its forward map to `κ` and
its inverse to exactly `s`. To prove the remaining equation
`κ ≫ s = 𝟙 C_Q`, it cancels postcomposition with the newly proved
monomorphism `κ` and applies associativity, `s ≫ κ = 𝟙 K` and the identity
laws. Thus both inverse equations are actual scheme-morphism equalities.
The theorems `representedCMNormalKernelSchemeIso_hom` and
`representedCMNormalKernelSchemeIso_inv` are reflexive value equations.
`representedCMNormalKernelComparison_isIso_of_dualGeometry` follows from
the constructed isomorphism's forward map.

For the exact proposition `q : CMRepresentabilityStatement ...`, the entry
`cmNormalKernelSchemeIso` substitutes precisely
`chosenCMLevelRepresentation ... q` for `R`. This is the family already
defining `cmSchemeTower ... q`. Its forward map is reflexively the direct
original `cmNormalKernelComparison ... q`, and its inverse is reflexively
the previously constructed `cmNormalKernelSection ... q`; the theorems
`cmNormalKernelSchemeIso_hom` and `cmNormalKernelSchemeIso_inv` record
those equalities. The chosen `cmNormalKernelComparison_mono_of_dualGeometry`
and `cmNormalKernelComparison_isIso_of_dualGeometry` specialize the proved
properties to the identical original comparison.

## Provenance and retained obligations

This is an internal deduction from the actual connected coproduct
factorization, geometric rigidity transfer, component constructions and
kernel section, using the exact implemented route above. It does not use the
earlier original-etaleness-dependent kernel-isomorphism construction.

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99, is
registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage gives local torsion-free smallness, the product over connected
components, polarized CM frame-orbit moduli, isogeny equivalence with
rational polarization multiplier and right frame composition. It asserts
smooth projective representability, finite-etale forgetting and the normal
`U/V` Galois cover. These conventions are retained by the imported
constructions. The new conditional scheme inverse is not attributed to the
book as a proof of all those assertions. The supplied publication/errata
list was previously read in full and lists no correction to this passage.

No original-projection etaleness or comparison isomorphism is assumed.
Applicable representability, the derivation of the exact geometric
coarse-rigidity hypothesis from source smallness, comparison with the complete
source moduli problem, original projection etaleness, canonical-model
geometry and coefficient descent remain separate obligations. The inverse
is a morphism for the kernel comparison, not a section of the forgetting
projection. This focused conditional construction does not complete the
source cover theorem or the host task.
