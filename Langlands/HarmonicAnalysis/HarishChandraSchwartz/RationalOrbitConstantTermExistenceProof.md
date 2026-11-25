# Existence of the constant terms of the actual orbit coefficients

This module proves the published target
`Langlands.HarishChandraSchwartz.RationalOrbitConstantTermExistenceStatement`
(module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm`) as
the theorem `Langlands.HarishChandraSchwartz.rationalOrbitConstantTermExistence`.

## Statement proved

For a connected reductive `G` over a nonarchimedean local field `F`, a maximal split torus `S`
with a generic cocharacter, an actual standard parabolic `P = P_I(F) = M_I(F) U_I(F)` with a
compact open `K` such that `G(F) = P_0(F) K`, an irreducible admissible representation `π` of
`M_I(F)` that is square-integrable modulo a central subgroup `C`, a second actual standard
parabolic `P′ = P_{I′}(F)` and a compatible split component `A` of `M′ = M_{I′}(F)`: under a
standard cocharacter `ζ` of `I′` and Renard's V.5.2 data (`CompactOpenNormalBasis K0 B` with the
basis-member clauses `StandardParabolicBasisMember` of `P′`), every orbit coefficient
`f_ω = E^G_P ψ_ω` (`rationalInducedOrbitCoefficientMap`), for `ψ ∈ C^∞(O, P)` and `ω` in the
unitary unramified orbit `O` of `π`, has a constant term along `P′`:
`HasStandardConstantTerm hA f_ω`. That is, there is a function on `M′` that is finite under
right translation by the image of `A(F)` and agrees with `δ_{U′}^{-1/2} f_ω` on the cones of
`P′` (Waldspurger, Proposition I.6.2, for these coefficients).

## Proof

The Lean proof follows Waldspurger's remark that `f_ω` is a coefficient of the admissible
representation `I^G_P(ω)`, so Proposition I.6.2 applies to it.

1. **A representative of `ω`.** The published
   `unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective` gives an actual representative
   `R` (an admissible smooth representation `R.val.obj` of `M_I(F)`, a unitary unramified twist
   of `π`) whose class is `ω`. Then
   `rationalInducedOrbitCoefficientMap_representative` rewrites `f_ω` as
   `rationalInducedCoefficientMap … R.val.obj _ (ψ.val R)`, the coefficient map `E^G_P` of `R`
   applied to the value of the section `ψ` at `R`.
2. **`E^G_P Φ ∈ A(I^G_P R)`** (lemma
   `rationalInducedCoefficientMap_mem_coefficientFunctionSpace`, proved for every admissible `R`
   and every `Φ` in the product-induced space). By the published
   `range_rationalInducedCoefficientMap`, the range of `E^G_P` equals the range of
   `normalizedCoefficientMap`, which is by definition the tensor coefficient map
   `coefficientTensorMap` of the normalized induced representation
   `(normalizedInductionFunctor h hU).obj R`. The published `coefficientFunctionSpace_eq_map`
   identifies Waldspurger's coefficient space `A(·)` (`coefficientFunctionSpace`) with the image
   of `coefficientTensorMap` in `G(F) → ℂ`, so `E^G_P Φ` lies in it.
3. **Admissibility of the induced representation.** `P_I(F) \ G(F)` is compact
   (`compactSpace_leftQuotient_standardParabolicPoints_rootSet`, from the compact `K` and
   `G(F) = P_I(F) K`), the Levi projection is continuous (`continuous_projection_standard`), and
   `R.val.obj` is admissible, so `normalizedInductionFunctor_obj_isAdmissible` shows that the
   normalized induced representation is admissible.
4. **Proposition I.6.2.** The published `standardConstantTerm_spec` (for the actual standard
   parabolic `P_{I′}`, the split component `A`, the standard cocharacter `ζ` and the V.5.2 data)
   applies to the admissible induced representation and the coefficient from step 2. Its first
   component is `HasStandardConstantTerm hA f_ω`.

The proof needs no other input: the hypotheses `hζ`, `hB`, `hmem` of the target are exactly those
of `standardConstantTerm_spec`, and the hypotheses `hsq` (square integrability) and the orbit
structure enter only through the representative `R`.

## Declarations

- `rationalInducedCoefficientMap_mem_coefficientFunctionSpace` (auxiliary lemma): every
  coefficient `E^G_P Φ` of an admissible representation `R` of `M_I(F)` lies in
  `coefficientFunctionSpace` of `I^G_P R = (normalizedInductionFunctor h hU).obj R`.
- `rationalOrbitConstantTermExistence : RationalOrbitConstantTermExistenceStatement hG hi hν I
  hKc hPK π C hC mu hsq I′ hA` (the target).

## Check

`lean_check`: 0 errors, 0 warnings;
inspection of `rationalOrbitConstantTermExistence` reports level parameters `u, uV` and axioms
`propext`, `Classical.choice`, `Quot.sound`.
