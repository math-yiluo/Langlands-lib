# Monomorphisms of affine analytifications and ring epimorphisms

Let `K` be a complete, ultrametric, nontrivially normed field and let
`f : A →ₐ[K] B` be a map of commutative `K`-algebras with finite polynomial
presentations `P` and `Q`. The field and the algebras may lie in independent
universes. The module proves that the analytified map
`localizedHom K P Q f : localized K Q ⟶ localized K P` is a monomorphism of the
localized category exactly when `CommRingCat.ofHom f.toRingHom` is an
epimorphism of commutative rings.

## Declarations

In `MonomorphismComparison`, `B` is an `A`-algebra with
`IsScalarTower K A B`, so that `IsScalarTower.toAlgHom K A B` plays the role
of `f`.

- `finiteType_tensor` and `tensorPresentation`: `B ⊗[A] B` is of finite type
  over `K` (base change of finite type and transitivity), with a chosen finite
  polynomial presentation.
- `inclLeft`, `inclRight` and `mult`: the two inclusions `b ↦ b ⊗ 1` and
  `b ↦ 1 ⊗ b` and the multiplication `B ⊗[A] B → B`, as `K`-algebra maps.
  `mult_comp_inclLeft` and `mult_comp_inclRight` say that multiplication is a
  retraction of both, and `mult_surjective` that it is surjective.
- `isPullback_square`: the analytified square of the two inclusions over the
  analytified structure map is a pullback. It is the published
  `affineAnalytificationFibreProduct` applied to `B ⊗[A] B`.
- `mult_comp_left` and `mult_comp_right`: by localized functoriality, the
  analytified multiplication map followed by either analytified inclusion is
  the identity.
- `isIso_mult_of_mono`: if the analytified map is monic, the two analytified
  inclusions agree. The analytified multiplication map is then an isomorphism,
  with inverse the analytified left inclusion; the second inverse identity is
  checked on the two projections of the pullback square.
- `isEpi_of_mono`: under the same hypothesis `Algebra.IsEpi A B`. An
  isomorphism is étale in the localized category (`etale_of_isIso`). The
  published étale reflection (`isEtale_of_localizedHom_etale` together with
  `affineAnalytificationEtale`) makes the multiplication map étale, hence flat.
  It is surjective, and its analytification is surjective on points. The
  maximal-center criterion `bijective_of_surjective_of_flat_of_baseMap_surjective`
  makes it bijective, so `1 ⊗ b = b ⊗ 1` for every `b`, which is Mathlib's
  `Algebra.isEpi_iff_forall_one_tmul_eq`.
- `mono_of_isEpi`: conversely, if `Algebra.IsEpi A B`, the two inclusions are
  equal. Two maps with equal composites to `localized K P` have a common lift
  to the pullback, and are both equal to the lift followed by the common
  inclusion.

Outside that namespace:
- `epi_of_mono_localizedHom` and `mono_localizedHom_of_epi` state the two
  directions for an arbitrary `f`, using the `A`-algebra structure
  `f.toRingHom.toAlgebra` and Mathlib's `CommRingCat.epi_iff_epi`.
- `mono_specMap_of_epi` and `epi_of_mono_specMap`: the spectrum of a ring map
  is a monomorphism of schemes exactly when the ring map is an epimorphism.
  `Scheme.Spec` is a right adjoint, so it preserves monomorphisms, and it is
  faithful, so it reflects them.

## Provenance

This is an internal derivation from the Library's affine fibre product,
étale reflection and maximal-center results and from Mathlib's
characterization of ring epimorphisms. It is the affine form of the
monomorphism step in Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), Proposition 3.4.6(10), printed p.65/PDF p.79,
registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`,
which states that analytification detects monomorphisms. The Lean argument
compares the diagonal through the self tensor product rather than following
Berkovich's proof.
