# Compact induction and subgroup Ext for actual induced-spectrum cohomology

Author: Worker 13.

This module connects the actual induced rational spectrum's full compact
sections, smooth sheaf compact sections, degree-zero Godement cohomology and
degree-zero sheaf-derived cohomology to compact induction of all local-spectrum
sections. It then identifies Ext from these degree-zero objects with subgroup
Ext and rewrites the zero row of their constructed hyperext second page.
The main page-two declaration is `compactHyperextZeroRowSubgroupAddEquiv` in
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.SmoothCohomology`.

This is an internal consumer of `InducedRationalCompactInduction`,
`InducedRationalDerivedComplex` and the published
`Cohomology.SupercuspidalExt.Reciprocity` construction. It composes their actual
maps and proved isomorphisms; no desired comparison is assumed as input. It
claims no new assertion from original literature. The imported Ext reciprocity
already proves the required exactness and preservation of injectives for open
subgroup restriction.

## Inputs and scope

The field `K : Type u` is complete, normed and ultrametric, `P` is a presented
strict affinoid algebra, and `G : Type u` is a topological group acting through
`ρ : RationalSpectralAction G P`. Let `X : ρ.OpenSubgroupTransport` and let
`H = X.subgroup.toSubgroup` be its open subgroup. `X.LocalSpectrum` is the actual
compact Hausdorff spectrum of its rational quotient algebra;
`X.InducedSpectrum` is the actual balanced quotient `G ×_H X.LocalSpectrum`.
The ring `R : Type u` is any commutative ring and coefficients
`M, W : SmoothRep.{u,u,u} R G` are arbitrary smooth representations. There is no
coefficient topology, dimension restriction, group local compactness, total
disconnectedness assumption or normality assumption on `H`.

The field, group, coefficient ring and module carriers are aligned in `u` in
this consumer because its sheaf and smooth Ext infrastructure uses that common
universe. The imported function-level compact-induction construction retains
its independently polymorphic universes. The sheaf branch explicitly requires
`HasStableNeighbourhoods G X.InducedSpectrum`; the function-level Hom and Ext
branch does not. The derived-complex and spectral-sequence branch additionally
requires `HasDerivedCategory.{w}` for the actual smooth sheaf category and
`HasDerivedCategory.{w'}` for the smooth representation category. These two
derived universes are independent of `u` and each other.

All sheaves here are constructed on ordinary open subsets of the actual
underlying topological space. The coefficient action remains the original
diagonal action throughout. The local representation, denoted `L_X(M)`, is the
full module of locally constant functions on `X.LocalSpectrum`, with

```
(h.s)(x) = M(h)(s(h⁻¹.x)).
```

Compactness proves smoothness of every local section in the imported module.
There is no replacement by a selected smooth-vector submodule.

## Actual Hom restriction and its inverse

`CompactSections.homSubgroupLinearEquiv X M W` is an `R`-linear equivalence

```
Hom_G(C_c(X.InducedSpectrum, M), W)
  ≃ Hom_H(L_X(M), restriction W).
```

Its construction first precomposes with the inverse of the full geometric
compact-induction isomorphism, then applies the existing linear Frobenius
reciprocity equivalence. The existing adjunction supplies both inverse laws.
`fromCompactInduction_unitFunction` proves that the finite-coset-sum inverse
sends the induction unit to actual zero extension from the unit chart. Its
proof applies the injective forward coordinate map and uses the two proved
unit-coordinate identities.

`homSubgroupLinearEquiv_apply` unfolds that adjunction and proves the exact
formula

```
T ↦ (s ↦ T(localChartExtension X 1 s)).
```

`homSubgroupLinearEquiv_symm_apply` states the inverse as the existing
`Induction.cosetSum` evaluated at the actual geometric coordinate function
`toCompactInduction X M f`. Thus it uses the finite sum of translates
`W(g⁻¹)(φ(F(g)))` over `H\G`, with covariance ensuring representative
independence. Finiteness and the right stabilizer of `F` are the proved fields
of the imported full compact-induction construction.

`homSubgroupLinearEquiv_naturality_target` proves that restriction along the
actual unit chart commutes with every smooth target intertwiner.
`homSubgroupIso` packages these linear equivalences into a natural isomorphism
of functors to `ModuleCat R`, so the coefficient module structure is retained.

`CompactSections.extSubgroupIso X M n` is the natural isomorphism in `W`

```
Ext_G^n(C_c(X.InducedSpectrum, M), W)
  ≅ Ext_H^n(L_X(M), restriction W).
```

It transports the first argument contravariantly along the actual geometric
compact-induction isomorphism and then uses the existing open-subgroup Ext
reciprocity isomorphism. It is constructed for every `n : ℕ`; the source
representation here is still the full degree-zero function module.

## Sheaf and derived degree zero

`sheafCompactSectionsInductionIso` composes the inverse of the full
function-to-sheaf-compact-section comparison with the geometric
compact-induction natural isomorphism. `godementZeroInductionIso` and
`derivedZeroInductionIso` do the same with the genuine degree-zero smooth
Godement compact cohomology and sheaf-derived compact sections, respectively.
Each is a natural isomorphism for all original coefficient intertwiners.

`godementDerivedZeroIso_hom_comp_derivedZeroInductionIso` proves that the
previously constructed Godement-to-derived degree-zero comparison commutes
with these compact-induction identifications. It cancels the intermediate
inverse isomorphisms; no additional comparison map is chosen.

`derivedZeroExtSubgroupIso` transports Ext contravariantly along the actual
degree-zero derived-cohomology identification, then applies `extSubgroupIso`.
The Ext index can be arbitrary, while the compact cohomology degree is zero.

`derivedComplexZeroInductionIso` identifies degree-zero homology of the actual
bounded-below derived compact-section object with the same full
compact-induction functor. The theorem
`compactDerivedComplexHomologyIso_hom_comp_derivedZeroInductionIso` proves its
compatibility with the existing natural cohomology comparison and
`derivedZeroInductionIso` by associativity of those very isomorphisms.

## The constructed hyperext second page

`compactHyperextZeroRowSubgroupAddEquiv X M W p` is the additive equivalence

```
E₂^{p,0} ≃+ Ext_H^p(L_X(M), restriction W).
```

Here `E₂` is the actual standard-t-structure hyperext spectral sequence of the
constructed unbounded derived compact-section object and the smooth target
`W` placed in degree zero. The proof composes the existing second-page zero-row
identification with `extSubgroupIso` evaluated at `W`. No arbitrary collection
of cohomology groups or spectral-sequence pages is supplied as data.

`compactHyperextOriginSubgroupHomAddEquiv` further applies the existing
`Ext^0 ≅ Hom` isomorphism on `H`, identifying `E₂^{0,0}` additively with the
actual subgroup-equivariant Hom module from `L_X(M)` to the restricted target.
The page-two comparisons are additive equivalences because the supplied
spectral sequence is valued in additive groups; the Hom and Ext functor
isomorphisms before that step are isomorphisms of `R`-modules.

This module identifies compact induction only in compact cohomological degree
zero. It does not identify higher compact cohomology with compact induction,
prove convergence or degeneration of the spectral sequence, compare ordinary
open and analytic/etale sheaves, compare higher Godement and derived
cohomology, construct the arithmetic level tower, or instantiate Harris's
particular groups and coefficient systems. Those remain separate construction
and theorem obligations of the wider task.
