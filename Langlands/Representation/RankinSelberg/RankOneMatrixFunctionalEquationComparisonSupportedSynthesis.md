# Supported matrix synthesis and compact weighted pairing

This internal helper retains the invertible ambient topological support of
the matrix test constructed by compact character synthesis. It derives
actual integrability and an iterated-integral expansion of the weighted
pairing. All declarations are in
`Langlands.RankinSelberg.CompactWhittakerSynthesis`.

## General supported synthesis

`exists_supported_matrix_characterOrbitIntegral_eq` works over a Hausdorff
topological division field, for every matrix size `r`, a compact-open
subgroup basis at the group identity, a closed subgroup `H`, and a
continuous scalar character `χ`. The supplied measure `μH` is a left Haar
measure and is also right invariant, with the subgroup's Borel measurable
space.

For every actual `CompactFunctions H (characterRepresentation χ)`, it
constructs a full-matrix Schwartz–Bruhat test whose ambient topological
support lies in the range of the actual `Units.val` map. At every group
element `g`, the inverse-character orbit integrand is integrable against
the same `μH`, and its integral is exactly the input function evaluated at
`g`.

The proof first uses the published `exists_characterOrbitIntegral_eq` to
obtain a group test. It extends that test by zero from the open invertible
locus using `groupTestToMatrixTest`. The published support lemma retains the
ambient support certificate, and `groupTestToMatrixTest_apply` preserves
every orbit value. Integrability follows from the published group-test
orbit-integrability theorem. This strengthens the existential API by
retaining a property of the actual constructed witness.

## Canonical compact matrix lift

`exists_supported_compactMatrixLift` specializes this construction to the
canonical p-adic field and actual upper-unipotent subgroup. Its
compact-open subgroup basis comes from
`generalLinearCompactOpen`; it uses upper-unipotent closedness, the
continuous standard character, and the fixed `unipotentHaar`.

`compactMatrixLift F ψ n f` chooses one such full-matrix test for the actual
compact induced function
`f : CompactFunctions (upperUnipotent (n+1) F.Carrier)
  (characterRepresentation (standardCharacter ψ n))`.
The choice depends only on these displayed arguments. In particular, the
same test is used for every second matrix test and every complex
determinant-weight parameter.

`compactMatrixLift_support` certifies ambient topological support in the
invertible locus. `compactMatrixLift_orbit_integrable` proves integrability
of its inverse-character orbit integrand at every group point, and
`compactMatrixLift_orbit` identifies that orbit integral with the original
value of `f`.

`compactMatrixLift_weighted_orbit` multiplies the orbit integral by the
second-test value `Φ(g.val)` and `determinantWeight abv g s`. Both factors
are constant in the subgroup variable. Taking them outside the integral
therefore gives exactly
`eval f g * Φ(g.val) * determinantWeight abv g s`.
Here `abv` is the canonical normalized absolute value.

## Genuine weighted pairing and expansion

`integrable_compact_matrix_pairing` proves actual Bochner integrability of

```text
g ↦ eval f g * Φ(g.val) * determinantWeight abv g s
```

against `generalLinearHaar F.Carrier n`, for every full-matrix second test
`Φ` and every `s : ℂ`. It applies the genuine joint product-integrability
bound to the supported lift, integrates the subgroup variable, and uses
the preceding weighted-orbit identity to identify the resulting function.
Thus integrability is derived without assuming any integral comparison.

`compact_matrix_pairing_eq_iterated` proves that the integral of this
weighted pairing is

```text
∫ u, ∫ g, standardCharacter(ψ,n,u)⁻¹
             * compactMatrixLift(F,ψ,n,f)((u*g).val)
             * Φ(g.val) * determinantWeight(abv,g,s).
```

The subgroup measure is precisely `unipotentHaar F.Carrier n`, and the
group measure is precisely `generalLinearHaar F.Carrier n`. Pointwise
substitution of the weighted orbit gives the opposite integral order;
Fubini, justified by actual product integrability, exchanges the measures.
There is no scalar factor and no change of the lift, character, test, or
parameter.

The section installs the canonical field topology, valuative relation,
local-field and Hausdorff instances, the published canonical GL second
countability and local compactness, the subgroup's corresponding
instances, and the actual Borel measurable spaces. These supply the needed
sigma-finiteness of the two fixed Haar measures. Every `n`, including `0`,
is allowed, with any supplied unitary additive character and any complex
parameter. No additive Haar measure, self-duality, nontriviality or
conductor normalization is required.

## Provenance and scope

This is an internal derivation from published group-test compact synthesis,
matrix extension by zero and its support theorem, the canonical p-adic
compact-open basis and unipotent Haar invariance, and the accompanying
ProductIntegrability helper. The integration steps use Mathlib
constant-multiple identities, integrability of an integral under a genuine
product-integrability hypothesis, and Fubini. No original-literature
assertion is introduced, and no Fourier comparison, matrix functional
equation, or gamma equation is assumed or proved.
