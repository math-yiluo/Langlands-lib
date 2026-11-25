# Generic archimedean standard-module components

`Langlands.Automorphic.cuspidalArchimedeanStandardGeneric` proves
`Langlands.Automorphic.CuspidalArchimedeanStandardGenericStatement.{u}`.
For an actual cuspidal realization over a number field with compact additive
adele quotient, each supplied real or complex place parameter has a standard
module with a nonzero Whittaker functional for a nondegenerate character.
[Published statement](CuspidalArchimedeanComponentStatement.md)

## Proof

1. The rank condition of the parameter gives a nonzero standard module by
   `realStandardKFinite_ne_bot` or `complexStandardKFinite_ne_bot`. For its
   injective parameter map `A`, `LinearEquiv.ofInjective` identifies the
   domain with `W = LinearMap.range A`. Hence `W ≠ ⊥`.
   [Standard-module nonvanishing](ArchimedeanPlaceParameterNontrivial.md)
2. The compact place-parameter lemma shows that each compact operator sends
   `A f` to the image of the right translate of `f`. The Lie place-parameter
   lemma gives the corresponding identity for `1 ⊗ X`. A pure tensor
   `c ⊗ X` acts by `c` times that action, and `TensorProduct.inductionOn`
   extends stability to the full complexified Lie algebra.
   [Place-parameter lemmas](CuspidalArchimedeanComponentUnitaryProof.md)
3. `cuspidalArchimedeanWhittakerFunctional` applied to the cuspidal realization
   and `W` gives coefficients `aᵢ` nonzero for `i + 1 < r + 1` and a functional
   `ℓ` nonzero at some `x ∈ W`. It satisfies the Whittaker identity on `W`
   with the real or complex coefficient formula for the place.
   [Whittaker functional on a stable subspace](CuspidalWhittaker/PlaceWhittaker.md)
4. Writing `x = A f` shows that `ℓ ∘ₗ A` is nonzero. The Lie intertwining
   identity sends the standard action of `1 ⊗ X` to the place action on `A f`.
   Thus the Whittaker identity on `W` gives the identity for `ℓ ∘ₗ A` on the
   standard module. The theorem pairs the real and complex proofs.

## Provenance

Getz and Hahn state the global genericity consequence of the Whittaker
expansion in the paragraph immediately before Theorem 11.3.6, printed p. 298
(PDF p. 309). They fix the local Whittaker-model identifications in §11.4
between (11.16) and (11.17), printed p. 301 (PDF p. 312), and use them in
Proposition 11.4.2, printed p. 302 (PDF p. 313). The Lean proof uses the
Library's stable-subspace version of the Whittaker construction and pulls back
along the supplied place parameter. The registered source is
`getz-hahn-2024-automorphic-representations`.
[Getz and Hahn, *An Introduction to Automorphic Representations*](https://doi.org/10.1007/978-3-031-41153-3)

The argument is the stable-image and pullback argument above. The module
imports the published nonvanishing proofs and uses the published
compact and Lie intertwining lemmas for the place parameters.
