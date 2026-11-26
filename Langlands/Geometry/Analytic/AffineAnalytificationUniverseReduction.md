# Moving affine analytification problems to the field universe

The affine analytification `localized K P` of a `K`-algebra `A` lies in
`SaturatedAtlasPresentation.LocalizedCategory.{u, u, u}`, where `K : Type u`,
whatever the universe of `A`. This module replaces a presented algebra by an
isomorphic algebra in the universe of `K` and shows that the algebraic and
analytic immersion properties of the immersion comparison are unchanged.

## Ring theory across universes

- `etale_comp`: étale ring maps compose, for rings in three arbitrary
  universes. It is Mathlib's `Algebra.Etale.comp` for the induced algebra
  structures.
- `etale_of_conj` and `epi_of_conj`: if `φ' ∘ e₁ = e₂ ∘ φ` for ring
  isomorphisms `e₁` and `e₂`, possibly across universes, then `φ'` is étale,
  respectively an epimorphism of commutative rings, when `φ` is. Étaleness
  uses `RingHom.Etale.of_bijective` and `etale_comp`. For epimorphisms, Mathlib's
  `CommRingCat.epi_iff_epi` gives `Algebra.IsEpi`, that is `1 ⊗ s = s ⊗ 1` in
  `S ⊗[R] S`. For two maps `g, k` out of `S'` with equal composites with `φ'`,
  `Algebra.TensorProduct.lift` of `g ∘ e₂` and `k ∘ e₂` sends these two
  tensors to `k` and `g` of `e₂ s`, so `g = k`.
- `isOpenImmersion_specMap_iff`: the spectrum of a ring map is an open
  immersion exactly when the map is étale and a ring epimorphism. Open
  immersions are étale and monic; conversely, Mathlib's
  `IsOpenImmersion.of_flat_of_mono` applies. Monicity of spectrum maps is
  compared with ring epimorphisms by `mono_specMap_of_epi` and
  `epi_of_mono_specMap` of `AffineAnalytificationMonomorphismComparison`.
- `isOpenImmersion_of_conj`: hence open immersions of affine spectra are
  invariant under conjugation by ring isomorphisms across universes.

## Models in the field universe

For a finite polynomial presentation `P` of `A`:
- `Model P` is `MvPolynomial (Fin P.arity) K ⧸ RingHom.ker P.map`, in the
  universe of `K`;
- `modelEquiv P : Model P ≃ₐ[K] A` is Mathlib's
  `Ideal.quotientKerAlgEquivOfSurjective`;
- `modelPresentation P` is its quotient presentation;
- `modelMap P Q f : Model P →ₐ[K] Model Q` is `f` conjugated by the two
  model isomorphisms, with `modelEquiv_modelMap` and `modelMap_conj`.

`surjective_iff_model` and `isOpenImmersion_iff_model` show that surjectivity
of `f` and the open-immersion property of its spectrum map agree with those of
`modelMap P Q f`.

## Analytic side

- `isIso_localizedHom_of_algEquiv`: by localized functoriality
  (`affineAnalytificationLocalizedFunctoriality`), a `K`-algebra isomorphism,
  possibly between algebras of different universes, induces an isomorphism of
  affine analytifications.
- `localizedHom_eq_conj`: analytification is contravariant, so
  `localizedHom K P Q f` runs from `localized K Q` to `localized K P`. By
  localized functoriality it is the composite of three maps: first the
  analytic isomorphism from `localized K Q` to
  `localized K (modelPresentation Q)` induced by `modelEquiv Q`, then the
  analytification of `modelMap P Q f`, from
  `localized K (modelPresentation Q)` to `localized K (modelPresentation P)`,
  and finally the analytic isomorphism from
  `localized K (modelPresentation P)` to `localized K P` induced by
  `(modelEquiv P).symm`.
- `closedImmersion_iff_model` and `openImmersion_iff_model`: since both
  morphism properties respect isomorphisms, `localizedHom K P Q f` is an
  analytic closed (respectively open) immersion exactly when the analytified
  map of models is.

## Provenance

This is internal bookkeeping derived from the Library's localized
functoriality of affine analytification and from Mathlib's ring theory. It
reduces the affine immersion comparison to algebras in the universe of the
field, where Mathlib's schemes and the Library's scheme analytification are
available.
