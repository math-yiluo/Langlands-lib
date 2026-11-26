# Artin conductor transport on a fixed finite subextension

The module proves two results. The first,
`Langlands.Henniart.PadicArtinTransport.existsArtinPresentationAt_iff`,
compares the p-adic and the general finite inertia presentations on one finite
Galois subextension. The second,
`Langlands.Henniart.Numerical.hasArtinConductor_iff_exists_padicPresentation`,
uses it to compute Henniart's Artin relation with p-adic presentations.

## The Artin relation through p-adic presentations

For `K : PadicField p`, `σ` an irreducible Weil class of rank `k + 1` and
`a : ℕ`, `Numerical.hasArtinConductor_iff_exists_padicPresentation K σ a`
states

```lean
HasArtinConductor K σ a ↔
  ∃ (A : FiniteRepresentation.{0, uK, uW} ℂ (Weil.Local.localWeilGroup K))
    (P : Ramification.Padic.FiniteInertiaPresentation K A)
    (hsurj : Function.Surjective
      (Ramification.Padic.weilInertiaRestriction K P.extension)),
    FiniteRepresentation.classOf A = weilClassForget K σ ∧
      P.artinConductor hsurj = (a : ℚ)
```

`HasArtinConductor K σ a` is `LocalNumerical.HasArtinConductor` at
`K.Carrier`, `AlgebraicClosure K.Carrier` and the canonical instances of `K`,
so it asks for a representative and a presentation
`Ramification.Local.SepClosed.FiniteInertiaPresentation`. The Library's results
on Artin exponents of p-adic Weil representations (for example
`Weil.Local.artinExponent_eq`, `Ramification.Padic.finiteInertiaConductorEquivalence`
and `Ramification.HerbrandBridge.continuousWeilFiniteInertiaPresentation`) are
stated for `Ramification.Padic.FiniteInertiaPresentation`; the equivalence lets
proofs about `HasArtinConductor` use them. The proof keeps the representative and
the class condition and applies `existsArtinPresentationAt_iff` at the
extension of the given presentation, in each direction.

## Presentations on a fixed finite subextension

`Langlands.Henniart.PadicArtinTransport.existsArtinPresentationAt_iff F L A a`
transfers witnesses for the Artin exponent of the Weil representation `A` over
the p-adic field `F`. Both sides require the same actual finite Galois
subextension `L` of `AlgebraicClosure F.Carrier`, surjective restriction of Weil
inertia, and Artin conductor equal to `a : ℚ`. The left side uses
`Ramification.Padic.FiniteInertiaPresentation F A`. The right side uses
`Ramification.Local.SepClosed.FiniteInertiaPresentation F.Carrier
(AlgebraicClosure F.Carrier) A` at the canonical local-field instances of `F`.

The two presentations extend different base norms to `L`. The p-adic
presentation extends the norm of `Padic p`, and the general presentation
extends `LocalGalois.localNormedField F.Carrier`. On `F.Carrier` the two resulting
norms have the same unit ball by `LocalGalois.localNormedField_le`, since the
given valuative relation is the one from the spectral norm over `Padic p`.
Uniqueness of the extended multiplicative norm and `spectralNorm.eq_of_tower`
identify the norm on `L` over `Padic p` with the extension of the spectral norm
on `F.Carrier`. For either norm on `F.Carrier`, the extended spectral norm of
`x : L` is at most one exactly when the norm of the constant coefficient of
`minpoly F.Carrier x` is at most one. This follows from
`spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` and positivity of the reciprocal
degree. Thus the norms on `L` have the same unit ball. The private lemmas
`spectralValuation_isEquiv` and `finiteValuativeRel_eq` derive equivalence of
the valuations and equality of their valuative relations.

`finiteRestriction_agree` identifies the images of the two restriction maps
in `Gal(L/F.Carrier)`. After identifying the valuative relations, the actual
integer ring, integer automorphism action and residue action are the same by
proof irrelevance. In `quotientArtin_exists_iff_of_same_valuation`, the two
inertia maps then agree by subgroup subtype extensionality. The kernel
condition, descended representation and Artin sum agree with that
identification. Two private lemmas unpack the presentation records to apply
this quotient result and then reassemble them over `L`.

The transport is internal compatibility for the Library's two spectral
realizations in [InertiaPresentation.lean](../LocalFactor/Ramification/InertiaPresentation.lean).
The finite Artin sum comes from Serre, *Local Fields* (1979), Chapter VI,
section 2, Proposition 2 and Corollary 1′, printed pages 100–101. The proof here
uses equality of the data entering that sum. The spectral uniqueness and
constant coefficient results are from Mathlib's
`Analysis.Normed.Unbundled.SpectralNorm`.
