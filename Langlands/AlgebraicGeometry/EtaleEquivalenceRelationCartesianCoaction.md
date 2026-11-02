# The coaction of an affine first level on a cartesian étale equivalence relation

Author: Worker 266.

## Setting

`h : IsCartesianHom E E₀ f g` is a cartesian morphism of étale equivalence
relations (Library `EtaleEquivalenceRelation.IsCartesianHom`): `g ≫ E₀.t =
E.t ≫ f`, and the square of `g`, `E.s`, `E₀.s` and `f` is a pullback. The
schemes `E.U`, `E₀.U` and `E₀.R` are affine. Write `B₀ = Γ(E₀.U, ⊤)`,
`C₀ = Γ(E₀.R, ⊤)` and `B = Γ(E.U, ⊤)`. `C₀` is a `B₀`-algebra through
`E₀.s.appTop`, and `B` through `f.appTop`; these algebra structures are given by
`letI` in the statements. `t₀ = E₀.t.appTop`.

## Declarations

In the namespace `EtaleEquivalenceRelation.IsCartesianHom`:

* `isAffine_R`: `E.R` is affine, since the pullback square makes `E.R ⟶ E₀.R`
  a base change of the affine morphism `f` (`IsAffine.of_isPullback`).
* `relationIso`: the ring isomorphism `C₀ ⊗[B₀] B ≅ Γ(E.R, ⊤)`. Mathlib's
  `isPushout_appTop_of_isPullback` makes `Γ(E.R)` a pushout of `C₀ ← B₀ → B`.
  The iso compares this pushout with `CommRingCat.isPushout_tensorProduct`.
  `relationIso_hom_tmul_one` and `relationIso_hom_one_tmul` say that it sends
  `c ⊗ 1` to `g.appTop c` and `1 ⊗ b` to `E.s.appTop b`.
* `ringHom`: the target map of `E` as a ring map `B →+* C₀ ⊗[B₀] B`, namely
  `relationIso⁻¹ ∘ E.t.appTop` (`relationIso_hom_ringHom`). `ringHom_algebraMap`:
  it sends `b • 1` to `t₀ b ⊗ 1`, by `g ≫ E₀.t = E.t ≫ f`.
* `ringEtaleGroupoid`: `ringHom` is a ring étale groupoid (`RingEtaleGroupoid`)
  with relation ring `C₀ ⊗[B₀] B` and source `b ↦ 1 ⊗ b`. It is the transport
  along `relationIso` (`RingEtaleGroupoid.ofRingEquiv`) of the ring form
  `EtaleEquivalenceRelation.ringEtaleGroupoid E` of `E`.
* `isCartesianHom_toScheme`: the isomorphisms `E.U ≅ Spec B` and
  `E.R ≅ Spec Γ(E.R) ≅ Spec (C₀ ⊗[B₀] B)` form a cartesian morphism from `E` to
  `ringEtaleGroupoid.toScheme`. The square with the second projections is a
  pullback because its horizontal maps are isomorphisms.
* `coaction`: `ringHom` as a Library `GroupoidCoaction E₀.t.appTop.hom B`. It is
  built by `RingEtaleGroupoid.coactionOfLevel` from the ring form
  `E₀.ringEtaleGroupoid` of `E₀`, `ringHom_algebraMap` and `ringEtaleGroupoid`.
  It has coaction `ringHom` (`coaction_coaction`) and is multiplicative
  (`coaction_isMultiplicative`).
* `ringHom_comp_appTop`: let `h' : IsCartesianHom E' E f' g'` with `E'.U`
  affine. Then `f'.appTop` is equivariant for the coactions of `h` and of the
  composite `h'.comp h : E' ⟶ E₀` (Library
  `EtaleEquivalenceRelation.IsCartesianHom.comp`). Here `f'.appTop` is the
  `B₀`-algebra map `EtaleEquivalenceRelation.appTopAlgHom f' f`. The proof
  checks the identity after the injective map `relationIso` of the composite.
  There it follows from `g' ≫ E.t = E'.t ≫ f'` and `g' ≫ E.s = E'.s ≫ f'`.

## Provenance and scope

This is the ring form of the coaction described in the ring-level route of
`context.md`: `Γ(E.R) ≅ C₀ ⊗[B₀] B`, and `τ = E.t.appTop` is a coaction of the
groupoid `(B₀, C₀)` on `B`. The coaction axioms are not checked directly at
universal points. They come from the groupoid laws of `E` through
`coactionOfLevel`. The first level `E₀` is used only through its ring form
`E₀.ringEtaleGroupoid`, whose relation map is a monomorphism. No closed
immersion condition on `E₀` is assumed.
