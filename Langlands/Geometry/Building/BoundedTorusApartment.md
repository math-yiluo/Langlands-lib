# Apartment containment from bounded generic tori

This internal result constructs the two integral split tori needed for
integral conjugacy from bounds on supplied generic tori. Its conclusion
retains the original generic source tori and their actual maps. It then
realizes apartment containment in the original reduced quotient, and
specializes the construction to the actual maximal unramified field.

## Statement

`Langlands.Geometry.Building.BoundedTorusApartmentStatement.{u}` quantifies
over the following data, without a characteristic restriction:

- A commutative noetherian Henselian valuation domain `R` with algebraically
  closed residue field and a fraction field `K`.
- A linearly ordered commutative value group with zero `Γ₀`, and a valuation
  `v : Valuation K Γ₀` that takes value one on the image of every `R`-unit.
- An affine connected reductive `K`-group scheme `G`, a supplied smooth
  integral model `M`, and connectedness of its actual full special fibre.
- Two supplied generic commutative tori `T₁`, `T₂` with maximal split
  embeddings `i₁`, `i₂` into `G`. For each embedding, the image of its
  character valuation kernel lies in `M.integralPoints`.

For every supplied function `ω : Kˣ → ℝ`, apartment datum `D` for `i₁`, and
subset `Y` of its reduced building, suppose that `Y` lies in the image of
`D.apartmentMap` and that `M.integralPoints` fixes `Y` pointwise. Then there
are a rational point `g ∈ M.integralPoints` and an isomorphism
`e : T₁ ≅ T₂` such that

```text
i₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ i₂.
```

For this same `g`, `e`, and equality `he`, each `y ∈ Y` has a coordinate
`x : D.Apartment` satisfying `y = g • D.apartmentMap x`, and

```text
Y ⊆ Set.range (D.conjugateApartmentMap e g he).
```

The conclusion uses the actual transported apartment map into the original
quotient. No nonemptiness or boundedness assumption on `Y` is needed.
`boundedTorusApartment` proves this exact closed proposition. Its value group
is quantified in `Type u`; the two general helper theorems also allow a
separate value-group universe.

## Construction and proof

`IntegralModel.exists_integralPoint_conjugacy_of_bounded_maximalSplitTori`
first applies
`SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded`
from `GroupScheme/IntegralModel/SplitTorusBoundedPoints` to each supplied
generic torus. The valuation ring is noetherian, and algebraic closure makes
its residue field infinite, as required by that construction. For each
source it supplies an actual split integral torus `U`, a closed map into
`M.group`, and an isomorphism from its actual generic fibre to the original
generic torus, with the stated equality of generic maps. Neither integral
torus is an input here.

`IsMaximalSplitTorus.iso_comp`, imported from
`GroupScheme/Torus/UnipotentQuotientMaximalSplit`, transports maximal
splitness through those source isomorphisms. The theorem
`IntegralModel.exists_integralPoint_genericTorusMap_conjugacy` from
`Geometry/Building/IntegralModelSplitTorusApartment` then gives an actual
integral-point conjugator and an integral isomorphism between the two
constructed tori. This theorem in turn uses actual residue maximality and
Henselian integral conjugacy; it does not assume conjugacy of the original
generic tori.

The proof base changes the integral source isomorphism and composes it with
the inverse of the first generic identification and the second
identification. Precomposing the obtained conjugacy equation with the actual
inverse of the first identification gives the required equality for
`i₁`, `i₂`.

`exists_integralPoint_conjugateApartment_contains_of_bounded` uses the
pointwise-fixer inclusion to show that this same `g` fixes every `y ∈ Y`.
For an original apartment coordinate `x`, the published
`KPApartmentData.conjugateApartmentMap_transport` identifies the transported
coordinate with `g • D.apartmentMap x`. This proves both the coordinate
equation and actual map-range containment.

## Maximal unramified specialization

`exists_integralPoint_conjugateApartment_contains_of_unramified_bounded`
uses a nonarchimedean local field `F`, its actual inertia fixed field `K`,
and `fixedFieldIntegers F`. The generic group `H` over `K` is affine.
The building datum `C : MaximalUnramified.BuildingData F H` supplies its
connected reductivity and first maximal split torus. The other data are:

- An unramified zero datum `E` and any subset `Ω` of `C.Apartment`.
- A smooth integral model `M` over `fixedFieldIntegers F` with connected
  actual special fibre.
- A supplied second maximal split generic torus and its character-kernel
  bound into `M.integralPoints`, using `MaximalUnramified.valuation F`.
- The inclusions
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤ M.integralPoints`
  and
  `M.integralPoints ≤ C.pointwiseFixer (C.apartmentMap '' Ω)`.

The published
`map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer` from
`BruhatTits/IntegralModels/UnramifiedModelKernelTorus` supplies the first
generic torus bound. The same module's arithmetic inputs give Henselianity,
the discrete valuation ring structure and algebraically closed residue
field of `fixedFieldIntegers F`.
`SpecialTorusIntegralModel.valuation_units_eq_one` supplies the required unit
values for the normalized valuation. The general helper allows its
value-group universe directly, so no change of valuation is needed.
The specialization concludes the same original-source conjugacy,
coordinates, and actual conjugate-apartment containment for
`C.apartmentMap '' Ω`. It does not require `K` to be a local field or
complete.

## Provenance and retained obligations

This is an internal composition of the named Library constructions and
theorems, not a transcription of a separate literature statement.
`IntegralModelSplitTorusApartment` and its
`HenselianSplitConjugacy` prerequisite supply the integral conjugacy step;
the present unit constructs its integral-torus inputs from generic bounds.

The integral model, the generic tori, their bounds and integral-point
fixation remain supplied. The unramified helper derives the first bound
from the supplied source inclusion, but constructs neither that inclusion
nor the second generic torus. There is no assertion of descent, Galois
stability, specialness, a facet or segment comparison, or a lift of a
prescribed residue torus. In particular,
`UnramifiedFixedPointSplitTorusStatement` remains open. No prohibited
unramified building-descent statement or consumer is used.
