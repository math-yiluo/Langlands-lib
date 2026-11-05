# The specified field at the generic point of a nonreduced model

This derived construction implements the residue-field identification in the
monic-model step of the proof of Stacks Project Lemma 37.24.8 (tag 0551),
registered source `stacks-generic-geometric-irreducibility-2026-11-04`,
`0551.html`, proof. It supports the geometric-fibre prerequisites used in the
Conrad adelic-points program. The comparison is proved for the actual lifted
model; its potentially nonreduced carrier is retained.

## General residue-field comparison

For a surjection `f : A →+* D` to a domain, a prime ideal `p = ker f`, and
a specified fraction field `F` of `D`, `residueFieldEquivOfSurjective`
constructs `p.ResidueField ≃+* F`. The quotient first-isomorphism equivalence
identifies `A / p` with `D`. Transporting the fraction-field structure on `F`
across that equivalence allows Mathlib's uniqueness of localization to identify
the two fields. The lemma `residueFieldEquivOfSurjective_algebraMap` proves
that the image of `a : A` is exactly `algebraMap D F (f a)`.
These ring-level comparisons allow three independent universes.

For rings and fields in one common scheme universe,
`residueFieldSpecIsoOfSurjective` combines this ring equivalence with Mathlib's
comparison between the scheme residue field of `Spec A` at `p` and the ideal
residue field. The result is an actual scheme isomorphism from `Spec F` to
the spectrum of that scheme residue field. Its composition with the actual
`fromSpecResidueField` morphism is proved to be the spectrum map of
`A → D → F`. The proof cancels the intermediate residue-field comparison
and applies the coefficient formula above.

## Application to the actual nilradical model

Let `R` have irreducible spectrum, let `K` be a specified fraction field of
the literal domain quotient `R / nilradical R`, and let `L` have compatible
quotient- and `K`-algebra structures. Given the actual model
`d : FiniteSeparableNilradicalModel R K L` and algebraicity of `L/K`,
`reductionTargetFractionRing` proves that `L` is the fraction field of the
actual domain subalgebra `d.quotientModel.Carrier`.

The existing localization of `L` at the nonzero elements of the quotient
base is enlarged to all nonzero elements of that domain subalgebra. Its
embedding in the original field `L` sends each such element to a nonzero,
hence invertible, element. No fraction-field structure on the potentially
nonreduced carrier `d.Carrier` is asserted.

`genericPrimeResidueFieldEquiv` then identifies the ideal residue field of
the actual generic prime with the originally specified `L`. Its coefficient
formula is the original reduction map followed by the subalgebra inclusion.
The predecessor module proves that this prime equals the carrier nilradical
and is generic for its whole spectrum.

In a common scheme universe, `modelScheme` is literally `Spec d.Carrier`,
and `modelGenericResidueFieldIso` identifies `Spec L` with the spectrum of
its actual scheme residue field at `d.genericPrime`. The first triangle
lemma identifies its composition with the residue-point morphism with
`Spec` of the reduction map followed by inclusion into `L`.

`toOriginalBase` is `Spec` of the actual coefficient map `R → d.Carrier`.
`originalGenericBaseMap` is `Spec` of `R → R / nilradical R → K`.
The final triangle proves that composing the model residue-point map with
`toOriginalBase` gives the original map `Spec L → Spec K → Spec R`.
Its proof uses the established reduction coefficient formula and the original
scalar tower, so it preserves the specified `K`-algebra structure on `L`.

## Scope

The algebraic comparison needs a supplied actual model and algebraicity;
its predecessor constructs that model from finite dimensionality and
separability. The scheme comparisons use one common universe and retain
all nilpotents in `R` and in the model. No reducedness or Noetherianity
hypothesis is added. This unit does not yet construct the principal-localized
scheme cover or transport it to a general irreducible scheme; those remain
consumer obligations, as do component splitting and full Stacks 0551.
