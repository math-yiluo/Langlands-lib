# Base scalars on module sheaves and transport of ideal multiples

This derived helper shows that ideal multiples and ideal layers of module
sheaves are preserved by every self-equivalence of `X.Modules` that
commutes with multiplication by base scalars. In particular, tensoring with a
locally free rank-one module carries the layers of the structure sheaf to the
layers of that module. Here `f : X ⟶ Spec R` is any morphism. No flatness,
properness, noetherianity, finiteness or coherence is assumed.

## Base scalars

For `a : R` and a presheaf of modules `P`, `smulPresheaf f a P : P ⟶ P`
multiplies the sections over `U` by the image `scalar f U a` of `a` in
`Γ(X, U)`. Naturality is `P.map_smul` together with the published
`scalar_naturality`. `smulEnd f a M` is the same map on a module sheaf `M`,
and `smulEnd_app_apply` records its value on sections. `smulEnd_naturality`
states that every morphism of module sheaves commutes with these maps, since
each component is linear over `Γ(X, U)`.

`smulEnd_projection`: for `a ∈ J`, the composite of `smulEnd f a M` with the
projection `M ⟶ M/JM` is zero. This is the published
`inclusion_comp_eq_zero_iff` applied to the cokernel condition of the
projection. Because `inclusion f J M : JM ⟶ M` is a monomorphism in an
abelian category with cokernel this projection, `smulToMultiple f J M ha`
is the resulting factorization `M ⟶ JM` (`Abelian.monoLift`).
`smulToMultiple_inclusion` states that composing it with the inclusion gives
`smulEnd f a M` again.

## Tensor products

With the monoidal structure on presheaves of modules over the commutative
structure presheaf, `smulPresheaf_whiskerRight` states that
`smulPresheaf f a P ⊗ 𝟙 Q = smulPresheaf f a (P ⊗ Q)`. The proof checks this
on pure tensors, where `(a • p) ⊗ q = a • (p ⊗ q)` holds by definition.
`sheafify_map_smulPresheaf` states that sheafification sends
`smulPresheaf f a P` to `smulEnd f a` of the sheafification. The two maps
agree after composing with the sheafification unit, because the unit is
linear on sections, and the adjunction bijection is injective.
`tensorBy_map_smulEnd`: since the published `tensorBy N` sends `M` to the
sheafification of `M.val ⊗ N.val`, it sends `smulEnd f a M` to
`smulEnd f a ((tensorBy N).obj M)`.

## Transport along equivalences

Fix an equivalence `E : X.Modules ≌ X.Modules`, a proof `hE` that
`E.functor.map (smulEnd f a A) = smulEnd f a (E.functor.obj A)` for all
`a` and `A`, an ideal `J`, and an isomorphism `e : E.functor.obj M ≅ M'`.
Write `ι` for the monomorphism `E.functor.map (inclusion f J M) ≫ e.hom`
into `M'`.

- `transport_inclusion_projection`: `ι ≫ projection f J M' = 0`. Apply the
  adjunction bijection of `E`. This turns the claim into
  `inclusion f J M ≫ g = 0` for the adjoint transpose `g` of
  `e.hom ≫ projection f J M'`. By `inclusion_comp_eq_zero_iff` it suffices
  that `g` kills `scalar f U a • m` for `a ∈ J`, that is,
  `smulEnd f a M ≫ g = 0`. Naturality of the bijection, `hE`,
  `smulEnd_naturality` and `smulEnd_projection` reduce this to the transpose
  of zero, which is zero.
- `inclusion_transport_cokernel`: `inclusion f J M' ≫ cokernel.π ι = 0`.
  By `inclusion_comp_eq_zero_iff` it suffices that
  `smulEnd f a M' ≫ cokernel.π ι = 0` for `a ∈ J`. By `hE` and naturality,
  `smulEnd f a M'` equals `e.inv ≫ E.functor.map (smulToMultiple f J M ha) ≫ ι`,
  and `ι ≫ cokernel.π ι = 0`.
- `multipleTransportIso f E hE J e : E.functor.obj (JM) ≅ JM'`. Each of
  the two monomorphisms `ι` and `inclusion f J M'` factors through the other
  by the two lemmas above (`Abelian.monoLift`). The factorizations are
  mutually inverse, as one sees by cancelling the monomorphisms.
  `multipleTransportIso_hom_inclusion` states that the forward map composed
  with `inclusion f J M'` is `ι`.
- `layerTransportIso f E hE e h : E.functor.obj (layer f h M) ≅ layer f h M'`
  for `h : I ≤ K`, where `layer f h M` is the cokernel `KM/IM` of
  `multipleMap f h M`. The equivalence preserves cokernels
  (`PreservesCokernel.iso`). The two transported multiple isomorphisms are
  compatible with `multipleMap`, which is checked after composing with the
  monomorphism `inclusion f K M'` using `multipleMap_inclusion`.
  `cokernel.mapIso` then identifies the cokernels.

## Twisting layers

`layerTwistIso N hN h : (tensorBy N).obj (layer f h (structureSheaf X)) ≅
layer f h N` holds for a locally free rank-one `N` and `h : I ≤ K`. It is
`layerTransportIso` for the equivalence `(tensorBy N).asEquivalence`
(published `tensorBy_isEquivalence`), with `tensorBy_map_smulEnd` and the
left unitor `tensorLeftUnitor N : O_X ⊗ N ≅ N`. With `I = J^(n+1)` and
`K = J^n` it identifies the twist of `J^n O_X / J^(n+1) O_X` by `N` with
`J^n N / J^(n+1) N`.

## Provenance

Stacks Project Lemma 30.21.3 (registered snapshot
`stacks-noetherian-fibre-section-lifting-2026-11-03`, `02OF.txt`) twists the
graded pieces `m^n O_X / m^(n+1) O_X` by powers of an invertible sheaf and uses
`m^n L / m^(n+1) L ≅ (m^n O_X / m^(n+1) O_X) ⊗ L`. This module proves that
identification for the published sheaves of local base-ideal multiples, any
ideals and any locally free rank-one `N`. It does not use finite generation of
the ideals.
