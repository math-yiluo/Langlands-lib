# Finite integral descent data for inner-twisted coefficients

This internal construction specializes integral coefficient recovery to a finite
unramified subfield of the inertia fixed field. It uses the actual integer
rings, field inclusions, lifted automorphisms and finite overlap cover from
`Descent.FiniteUnramified`. Its provenance is the combination of
`FiniteUnramifiedIntegralDatum`, `InnerSemilinearCoefficientRecovery`,
`InnerSemilinearExtension` and `InnerSemilinearCoherence`, together with the
proved `smoothHomExtension` and its strictly Henselian fixed-field
specialization. No original-literature theorem is asserted by this module.

Let `F` be a nonarchimedean local field with the Library's compatible valuation
and topology, and let `E` be an intermediate field of its separable closure
contained in `inertiaFixedField F`. All fields have the same arbitrary universe.
Write `K` for the inertia fixed field, `A` for `fixedFieldIntegers F`, and `R`
for `extensionIntegers F E`. The local instances use the actual inclusions
`E → K` and `R → A`; the latter is flat and surjective on spectra by
`spectralIntegerMap_fpqc`.

The inputs include a group scheme `G` over `F`, integral models `N` over `R`
and `P` over `A`, and a supplied isomorphism from the coefficient extension of
`N` to `P`. This isomorphism has exactly the canonical
`finiteInertiaGenericIso` as generic comparison. The model `P` is smooth.
For each automorphism of `K/F`, a rational point `c σ` is supplied, with both
forward and inverse integral-point stability for the generic map
`g ↦ c σ * rationalConjugate σ g * (c σ)⁻¹`. The inverse condition is
`g ↦ rationalConjugate σ.symm ((c σ)⁻¹ * g * c σ)`.

A family `d` of rational points over `E` is supplied. Its relative extension to
`K` equals `c` at each selected `liftAutomorphism` of an `E/F` automorphism.
Neither this recovery nor the models' existence is inferred in this file.
The construction of individual integral maps does not require that `c` or `d`
be cocycles, or that `E/F` have finite degree.

`finiteInnerUpstairsIso` uses the proved fixed-field smooth homomorphism
extension theorem and the two stability conditions to construct the actual
integral inner twist on `P`. Its generic conjugator is exactly the relative
extension of `d σ`; the recovery equality transfers the given stability
conditions to that conjugator. No smooth-extension premise remains to be
provided by the caller.

`finiteInnerIntegralSemilinearIso` applies
`innerSemilinearIsoFromCoefficients` with the actual finite and fixed-field
integer automorphisms and the proved field and integer squares. This descends
the upstairs integral map through the supplied model recovery to an integral
isomorphism from the corresponding twist of `N` to `N`. Its generic map is
exactly `innerGaloisDescentIso F G σ (d σ)`. The theorem
`finiteInnerIntegralSemilinearIso_generic` records the resulting
`GenericSemilinearCompatible` square, using the generic compatibility of the
constructed model isomorphism.

For `finiteInnerIntegralDatum`, assume additionally that `E/F` is finite Galois
and arithmetically unramified, and that the supplied `d` satisfies
`d (σ * τ) = d σ * rationalConjugate σ (d τ)`. The actual finite overlap
components are indexed by the Library's `galoisIndexEquiv`.
`innerGaloisDescentIso_tower` converts this cocycle identity into the generic
tower law with the correct index multiplication. Then
`datumOfGenericSemilinear` uses the generic compatibility and separated
integral-model comparison to construct actual Čech descent data for
`integerMap F E` on `N.group`. Finally,
`pullIso_finiteInnerIntegralDatum` identifies each overlap component with the
constructed integral semilinear isomorphism through the actual
`semilinearComponent` comparison.

This is conditional construction of finite integral maps and descent data. It
does not supply a common finite field for an arbitrary cocycle and model,
construct an integral model of a point stabilizer, perform affine effectivity,
or establish a residue quotient, canonical Frobenius or chamber statement.
