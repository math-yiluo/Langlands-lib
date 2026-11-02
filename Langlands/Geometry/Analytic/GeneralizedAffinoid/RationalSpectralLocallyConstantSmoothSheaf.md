# Smooth module-valued locally constant sheaves on spectral-invariant rational charts

Worker 13. Internal derived construction, using the original spectral-invariant
chart and compact-action diagrams and the generic smooth diagonal function module.
The entry declaration is
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.spectralInvariantLocallyConstantSmoothSheafCoefficientsIso`.

## Actual geometric and coefficient inputs

Fix a complete ultrametric normed field `K`, a `PresentedAffinoidAlgebra K`,
a topological group `G`, and a `DomainSpectralAction G A`. The last input is
an action by actual bounded algebra automorphisms continuous for the existing
represented-domain spectral topology. The open subgroup `H` retains its
original subspace topology. No norm-orbit continuity hypothesis is added.

The site is the existing `SpectralInvariantChart ρ H` with
`SpectralInvariantChart.finiteRationalTopology ρ H`. Its objects are the
original positive-radius rational quotient presentations with `H`-invariant
actual loci, and its arrows are all original bounded restrictions over the
base algebra. This construction retains the complete field hypothesis,
the original chart arrows, and every locally constant function.

For a smooth module representation `M` of `H`, the locus and quotient-spectrum
presheaves apply `CompactContinuousAction.locallyConstantModuleFunctor M` to
the opposite of the existing compact geometric diagrams. Thus the carrier is
the actual `LocallyConstant X M`, its action is
`(g f)(x) = M(g)(f(g⁻¹ x))`, and its maps are the original linear pullbacks.
Smoothness is the proved generic compact function-module construction, using
the finite function image and the spatial and coefficient stabilizers.

`spectralInvariantLocusLocallyConstantSmoothPresheaf` and
`spectralInvariantSpectrumLocallyConstantSmoothPresheaf` implement these
two presheaves. Their action and restriction evaluation lemmas display the
diagonal coefficient action, the actual geometric inverse operator and the
original locus or quotient-spectrum map. All identity, composition, linearity,
equivariance and smoothness obligations come from the generic function-module
functor and the existing compact geometric diagrams.

## Spectrum-locus comparison and categorical sheafness

The existing natural equivariant rational homeomorphism induces
`spectralInvariantLocallyConstantSmoothPresheafIso` by contravariant
whiskering. Its two evaluation formulas are pullback by the original
homeomorphism and its inverse. The two `SmoothForgetIso` definitions forget
the representation and module to recover the original ordinary locally
constant presheaves restricted to the invariant charts. Their component maps
are identities on the actual functions.
`spectralInvariantLocallyConstantSmoothPresheafIso_forget` identifies
the corresponding comparison with the original ordinary comparison.

Continuity of the invariant-chart inclusion and the ordinary locally constant
sheaf prove sheafness of the unchanged underlying sets of functions. The full
inclusion from smooth representations into representations reflects limits.
The forgetful functors from representations to modules and from modules to sets
reflect matching limits of the site's size. Applying Mathlib's categorical
sheaf reflection theorem successively proves the actual smooth-representation
sheaf condition. This uses reflection of limits; it does not assert that the
full smooth inclusion preserves arbitrary limits.

More precisely, the chart category has object and morphism universe `u`.
Representation-to-module limit reflection is shrunk from the function carrier
universe `max u w` to `(u,u)`. The module-to-set reflection instance is also
instantiated at `(u,u)`. The fully faithful smooth inclusion reflects limits
of all sizes. Three applications of `Presheaf.isSheaf_of_isSheaf_comp`
therefore establish
`spectralInvariantLocusLocallyConstantSmoothPresheaf_isSheaf`.
Transport by the actual presheaf isomorphism proves its spectrum counterpart.
No sheafness input is assumed.

`spectralInvariantLocusLocallyConstantSmoothSheaf`,
`spectralInvariantSpectrumLocallyConstantSmoothSheaf` and
`spectralInvariantLocallyConstantSmoothSheafIso` package these actual
presheaves and their comparison without changing the functions, actions or
restriction maps.

## Functoriality in smooth coefficients

`spectralInvariantLocusLocallyConstantSmoothPresheafCoefficients` and
its spectrum counterpart whisker the generic pointwise coefficient
postcomposition map with the original geometric diagrams. They retain every
equivariant linear map `a : M ⟶ N`. The two coefficient evaluation lemmas
state precisely `f(x) ↦ a(f(x))`; naturality under every chart restriction
is inherited from the generic coefficient map. Identity and composition hold
pointwise and are proved here.

`spectralInvariantLocallyConstantSmoothPresheafCoefficientsIso` proves
that the rational homeomorphism comparison is natural in coefficients:
postcomposition by `a` commutes pointwise with geometric pullback.
The two `SmoothSheafCoefficients` functors lift these presheaf functors
to the full sheaf subcategory using the proved categorical sheafness.
The entry declaration lifts the same coefficient-natural comparison
to actual smooth-representation-valued sheaves. Its component at `M` is
the sheaf isomorphism above, with the same original maps in both directions.

## Universes, provenance and scope

The field, group, coefficient ring and coefficient carrier have independent
universes `u`, `v`, `r` and `w`; the function carrier has universe `max u w`.
The coefficient ring is arbitrary commutative and the coefficient representation
is arbitrary smooth. No topology on coefficients, finite dimension,
admissibility, nonempty spectrum or reducedness hypothesis is imposed.
Empty loci and spectra give their actual full modules of functions.

The provenance is internal. The imported
`RationalSpectralLocallyConstantPresheaf` supplies the compact geometric
diagrams and their natural comparison;
`RationalSpectralInvariantRestrictionSite` supplies continuity of the
invariant-chart inclusion; and `RationalChartLocallyConstantSheaf` supplies
actual ordinary locally constant gluing. The imported
`Representation.LocallyConstant.CompactAction` constructs the full smooth
diagonal module and its functoriality. Pinned Mathlib's `Sites.Sheaf`,
`Rep.Basic`, `ModuleCat.Abelian` and `Limits.Preserves.Basic` supply categorical
sheaf and limit reflection tools. Their composition and the coefficient-natural
comparisons are implemented here. No new original-literature theorem is
claimed, and the imported pairs remain unchanged.

These are sheaves on the restricted finite spectral-invariant rational site.
They do not assert a full analytic or etale comparison, exactness, a support
condition, an arithmetic coefficient system, cohomology or Harris specialization.
