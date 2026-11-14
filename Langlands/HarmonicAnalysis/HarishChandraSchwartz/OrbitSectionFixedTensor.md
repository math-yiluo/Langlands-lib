# Actual fixed coefficients and the section tensor map

This is an internal implementation of the fixed coefficient space and the
algebraic section map in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques*, VI.1, printed pp.295–296, and VI.3, printed p.301 (registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`;
PDF pp.61–62 and 67). VI.1 describes smooth sections by finite scalar-smooth
compact-picture families subject to the actual self-twist covariance. VI.3
uses the finite-dimensional fixed compact-picture coefficients to define
finite-product level topologies. This module supplies the actual algebraic
map needed for that comparison; it does not prove a topology comparison.

All declarations below are in `Langlands.HarishChandraSchwartz`.
The generic data are a topological nonarchimedean group `G`, a semidirect
decomposition `h : IsSemidirectDecomposition P M U`, an open subgroup `K`,
and an actual complex irreducible admissible representation `π` of `M`.
The coefficient carrier is the existing
`Langlands.Plancherel.ProductInducedCompactPicture h K π.obj`: its product
Levi object uses `π.obj` and its smooth contragredient, rather than a new
or independently supplied product representation.

## Fixed coefficients and finiteness

`orbitSectionFixedCoefficients h K π H` is the submodule fixed by
`compactFixedSubgroup (K.prod K) (H.prod H)` under
`Langlands.Plancherel.productInducedCompactRepresentation h K π.obj`.
It is defined for every open `H`. For `H ≤ K`,
`mem_orbitSectionFixedCoefficients_iff` proves that membership is exactly
invariance under every element of `H × H`, included into `K × K`.
Thus on the relevant levels it is precisely Waldspurger's fixed space.

The full target declaration
`Langlands.HarishChandraSchwartz.OrbitSectionFixedCoefficientsFiniteStatement`
asserts that compactness of `K` and `CompactOpenCofinal M` imply
finite dimensionality of this actual submodule for every open `H ≤ K`.
It does not assume finiteness or admissibility of a product or induced
representation.

`orbitSectionProductLevi_isAdmissible` derives admissibility of the actual
product Levi object. It applies
`Langlands.SmoothRep.isAdmissible_contragredient_iff` using compact-open
cofinality, then `Langlands.TwoFactorExternalTensor.admissible` to the
two admissible factors, and finally
`Langlands.isAdmissible_comp_continuousMulEquiv` along
`Langlands.HaarModulus.subgroupProdEquiv M M`.
`finiteDimensional_orbitSectionFixedCoefficients` proves the finiteness
conclusion by applying the published
`Langlands.Plancherel.finiteDimensional_compactFixedVectors` to `h.prod h`,
`K.prod K`, and `H.prod H`. The fixed submodule agrees definitionally
with its `CompactFixedVectors` input. These two adapters do not require
local compactness of `G` or an admissibility theorem for induction.

## The actual level map

The remaining constructions use the existing locally compact setup for
`OrbitSectionLevel`: a finite torus indexed by `J`, a character group
equivalence `e`, continuous valuation characters `ν`, closed `P` and `U`,
compact `K`, continuous semidirect projection and the covering `G = P K`.
No continuity premise on `e` is introduced.

`orbitSectionLevelFixedRestriction` is a complex-linear map from the
existing `OrbitSectionLevel ... H` to torus families in the actual fixed
coefficient submodule, for `H ≤ K`. Its underlying value at `q, z` is
exactly `Langlands.Plancherel.productInducedSmoothOrbitCompactRestriction`
applied to `OrbitSectionLevel.toSections ... q` at `z`. The published
`productInducedCompactRepresentation_orbitSectionCompactRestriction`
provides the fixed-vector proof; the compact restriction's linearity
provides linearity of this restricted map.

`orbitSectionLevelFixedRestriction_mem` proves that this family belongs to
`Langlands.Plancherel.finiteSmoothFamilies`. It uses the injective
coefficient inclusion and
`Langlands.Plancherel.mem_finiteSmoothFamilies_of_injective_linearMap`
to reflect the existing ambient smooth-family condition of `q`.
`orbitSectionLevelFixedFamily` is the corresponding linear map into that
submodule of families.

`orbitSectionLevelTensor` composes this map with the inverse of
`Langlands.Plancherel.smoothTensorFamilyEquiv`. Its codomain is the
algebraic tensor
`smoothFiniteTorusFunctions J ⊗[ℂ] orbitSectionFixedCoefficients h K π H`.
This construction needs neither a basis nor finite dimensionality.
`orbitSectionLevelTensor_evaluation` proves the pointwise formula:
applying `Langlands.Plancherel.smoothTensorEvaluation`, then the
coefficient inclusion, recovers the original compact restriction.
The proof evaluates `smoothTensorFamilyEquiv.apply_symm_apply`.
`orbitSectionLevelTensor_injective` then proves injectivity by the
published injectivity of compact restriction and of
`OrbitSectionLevel.toSections`.

The source remains the actual section level throughout, so its self-twist
covariance is retained. No assertion of surjectivity onto arbitrary smooth
fixed-valued families is made. The finite-product and inductive-limit
comparisons are separate Prop-valued targets in subsequent modules.
