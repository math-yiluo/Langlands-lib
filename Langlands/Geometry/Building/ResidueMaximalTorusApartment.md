# Generic maximality and apartments from a maximal residue torus

This internal construction uses one bounded generic maximal split torus and
one supplied integral split torus with maximal actual residue map. It
proves maximal splitness of the second generic map and conjugacy by an
actual model integral point. It also proves containment in the actual
transported apartment and specializes to the maximal unramified field.

## Statement

`Langlands.Geometry.Building.ResidueMaximalTorusApartmentStatement.{u}`
quantifies over the following data in arbitrary universe `u`, without a
characteristic restriction:

- A commutative noetherian Henselian valuation domain `R`, with algebraically
  closed residue field `k = IsLocalRing.ResidueField R` and fraction field
  `K`.
- A linearly ordered commutative value group with zero `Γ₀`, and a valuation
  `v : Valuation K Γ₀` taking value one on images of `R`-units.
- An affine connected reductive generic group scheme `G`, a supplied smooth
  integral model `M`, and connectedness of its actual full special fibre.
- A supplied generic commutative torus `T` and maximal split embedding
  `i : T.toGrp ⟶ G`, with the image of its character valuation kernel
  contained in `M.integralPoints`.
- A supplied integral commutative group scheme `U`, its split-torus
  structure, and a map `j : U.toGrp ⟶ M.group` whose actual base change to
  `k` is a maximal torus in the actual special fibre.

Then `J = M.genericTorusMap U j` is a maximal split torus. For every function
`ω : Kˣ → ℝ`, supplied apartment datum `D` for `i`, and subset `Y` of its
reduced building, suppose that `Y` lies in `Set.range D.apartmentMap` and
`M.integralPoints` fixes `Y` pointwise. There are an actual rational point
`g ∈ M.integralPoints` and an isomorphism of generic source tori
`e : T ≅ U_K` such that

```text
i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ J.
```

For this same `g`, `e`, and homomorphism equality `he`, each `y ∈ Y` admits
a coordinate `x : D.Apartment` with `y = g • D.apartmentMap x`, and

```text
Y ⊆ Set.range (D.conjugateApartmentMap e g he).
```

The statement first returns generic maximality and uses its induced
monomorphism instance to form this actual transported apartment map.
`residueMaximalTorusApartment` proves the exact closed proposition.
No nonemptiness or boundedness condition on `Y` is needed. The closed
statement quantifies `Γ₀` in `Type u`; the general helper theorems allow a
separate value-group universe.

Generic maximality of `J`, a character-kernel bound for `J`, and closedness
of the integral map `j` are not separate premises. Generic closedness is
included in the proved maximal splitness of `J`. The residue maximality
premise itself concerns an actual closed maximal torus.

## Construction and proof

`IntegralModel.exists_integralPoint_conjugacy_of_bounded_residueMaximal`
applies
`SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded`
from `GroupScheme/IntegralModel/SplitTorusBoundedPoints` to the first
generic torus. The hypotheses supply the required noetherian valuation
domain; algebraic closure makes the residue field infinite. The result is
an actual integral split torus `U₁`, a closed integral map `j₁`, an
isomorphism `e₁ : U₁_K ≅ T`, and the equality

```text
M.genericTorusMap U₁ j₁ = CommGroupScheme.groupHom e₁.hom ≫ i.
```

`IsMaximalSplitTorus.iso_comp` from
`GroupScheme/Torus/UnipotentQuotientMaximalSplit` transports the generic
maximality of `i` through `e₁`. The theorem
`IntegralModel.isMaximalTorus_specialFibre_of_generic` from
`GroupScheme/IntegralModel/SpecialFibreKernelTorus` then gives maximality
of the actual residue map of `j₁`.

Together with the supplied residue maximality of `j`, this allows
`exists_henselian_splitTorus_conjugacy` from
`GroupScheme/Torus/HenselianSplitConjugacy` to construct an actual integral
section `gR` and integral source isomorphism `eR : U₁ ≅ U`. Its smoothness,
affineness, connected residue fibre, algebraic closure and residue-map
surjectivity hypotheses all concern the supplied model and the actual
residue field.

`IntegralModel.genericTorusMap_conjugation` from
`Geometry/Building/IntegralModelSplitTorusApartment` transports this
integral equality through the model's actual generic identification.
Set `g = M.integralPointMap gR` and compose `e₁.symm` with the actual generic
base change of `eR`. Precomposing the transported equation with the
inverse of `e₁` and cancelling gives the desired equation for the original
generic source `T`. The range witness `(gR, rfl)` proves actual membership
in `M.integralPoints`.

This equation gives a genuine `SubgroupConjugate` relation between `i` and
`J`. The published `SubgroupConjugate.isMaximalSplitTorus_iff`, also from
`UnipotentQuotientMaximalSplit`, transfers maximal splitness from `i` to
`J`. No generic maximality of `J` was used to construct the conjugator.

`exists_conjugateApartment_contains_of_bounded_residueMaximal` applies
this algebraic construction and uses the pointwise-fixer inclusion to
show that the same `g` fixes every `y ∈ Y`. For an original apartment
coordinate `x`,
`KPApartmentData.conjugateApartmentMap_transport` from
`Geometry/Building/ConjugateApartmentRealization` realizes the transported
coordinate as `g • D.apartmentMap x`. This proves both coordinate equations
and actual map-range containment in the original reduced quotient.

## Maximal unramified specialization

`exists_conjugateApartment_contains_of_unramified_residueMaximal` uses a
nonarchimedean local field `F`, its actual inertia fixed field `K`, and
`fixedFieldIntegers F`. Its supplied data are:

- An affine `K`-group `H`, building datum
  `C : MaximalUnramified.BuildingData F H`, unramified zero datum `E`, and
  any subset `Ω` of `C.Apartment`.
- A smooth integral model `M` over the maximal unramified integers with
  connected actual full special fibre.
- A supplied integral split torus `U` and map `j` whose actual residue
  map is maximal.
- The inclusions
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤ M.integralPoints`
  and
  `M.integralPoints ≤ C.pointwiseFixer (C.apartmentMap '' Ω)`.

The building datum supplies connected reductivity and the first maximal
split torus. The published
`map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer` from
`BruhatTits/IntegralModels/UnramifiedModelKernelTorus` supplies its bound
after composition with the first inclusion. Published
`fixedFieldIntegersIsHenselian`, `fixedFieldResidueIsAlgClosure`,
`fixedFieldValuesFromBase` and `fixedFieldIntegersIsDVR_of_valuesFromBase`
supply Henselianity, algebraically closed residue and the discrete
valuation ring structure. The residue algebra is induced by
`residueToFixedField`. The theorem
`SpecialTorusIntegralModel.valuation_units_eq_one` supplies the required
unit values of `MaximalUnramified.valuation F`.

Applying the general helper proves maximal splitness of the actual
generic map of `j` and returns the same conjugacy, coordinates, and
actual transported-apartment containment for `C.apartmentMap '' Ω`.
No assumption that `K` is complete or a local field is needed.

## Provenance and retained obligations

This is an internal composition of the named Library constructions and
theorems, rather than a transcription of a separate literature statement.
It uses the integral-conjugacy construction of `HenselianSplitConjugacy`
and its generic transport in `IntegralModelSplitTorusApartment`. The
bounded first torus extension and the maximal residue map of the supplied
second torus supply their inputs.

The smooth integral model, the integral split torus with maximal residue
map, the first generic torus bound, original apartment containment and
integral-point fixation remain supplied. The unramified specialization
derives the bound from the supplied source inclusion. It constructs
neither that inclusion nor the second integral torus. It proves no
Galois stability, specialness, facet or segment comparison, or lifting of
a prescribed residue torus. In particular,
`UnramifiedFixedPointSplitTorusStatement` remains open. No prohibited
unramified building-descent statement or consumer is used.
