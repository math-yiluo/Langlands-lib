# Lifting a pointed abelian-scheme structure across an elementary Artinian extension

`Langlands.AbelianScheme.PointedAbelianArtinianLiftingStatement` expresses
Proposition 6.15 of Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
3rd ed. (1994), in every universe `u`. This file states the proposition and does
not prove it.

## The statement

Let `q : R →+* B` be a surjective homomorphism of Artinian local rings whose
kernel is annihilated by the maximal ideal of `R`, and let
`t = Spec.map (CommRingCat.ofHom q) : Spec B ⟶ Spec R`. Let `p : X ⟶ Spec R`
be smooth and proper, with a section `s` (`s ≫ p = 𝟙`). Suppose that there are
an abelian scheme `A₀` over `Spec B` and an isomorphism
`e₀ : A₀.X.left ≅ pullback p t` over `Spec B`, so that
`e₀.hom ≫ pullback.snd p t = A₀.X.hom`, whose identity section, followed by
`e₀.hom` and the projection `pullback.fst p t` to `X`, equals `t ≫ s`. Then
there are an abelian scheme `A` over `Spec R` and an isomorphism
`e : A.X.left ≅ X` over `Spec R` (`e.hom ≫ p = A.X.hom`) that carries the
identity section `η[A.X].left` to `s`.

## Correspondence with the source

The source takes `S = Spec(A)` for an Artin local ring `A` with maximal ideal
`m`, an ideal `I` with `m·I = (0)`, a smooth proper morphism `π : X → S` with a
section `e`, `S₀ = Spec(A/I)` and `X₀ = X ×_S S₀`. It assumes that `X₀` is an
abelian scheme over `S₀` with identity `e|S₀` and concludes that `X` is an
abelian scheme over `S` with identity `e`.

- The ring `R` is the source's `A`, the ideal `RingHom.ker q` is `I`, and the
  surjection `q` presents `B` as `R ⧸ RingHom.ker q`, so `t` is the closed
  immersion `S₀ → S` and `pullback p t` is `X₀`. The assumptions that `B` is
  local and Artinian follow from surjectivity once `B` is nonzero. Locality of
  `B` makes `B` nonzero, so the kernel is a proper ideal. The source needs `I`
  proper: for `I = A` the scheme `S₀` is empty, the hypothesis is vacuous, and
  the conclusion fails for the projective line over a field.
- The source's Definition 6.1 calls a group scheme over a noetherian base an
  abelian scheme when it is smooth and proper with connected geometric fibres.
  The structure `Langlands.AbelianScheme` of `Langlands.AbelianScheme.Basic` is
  a commutative group scheme whose structure morphism is smooth, proper and
  geometrically connected. Commutativity is automatic for the source's abelian
  schemes by its Corollary 6.5, so the hypothesis and the conclusion agree with
  the source's.
- The source's chapter assumes all schemes locally noetherian. Here `Spec R` is
  noetherian and `X` is of finite type over it, so no hypothesis is lost.
- An `AbelianScheme` carries its own underlying scheme `A.X.left`, so "a
  structure of abelian scheme on `X`" is an abelian scheme with an isomorphism
  of its underlying scheme onto `X` over the base. In the hypothesis, the
  identity section of `A₀` is a morphism over `Spec B`, so its composite with
  `e₀.hom ≫ pullback.snd p t` is the identity. The equation after projection
  to `X` then identifies the transported identity with the section of the
  pullback induced by `s`, which is `e|S₀`, by the universal property of the
  pullback.

In the source, Proposition 6.15 is the first step of the proof of Theorem 6.14.
In the proof of Proposition 6.16 it is the infinitesimal lifting criterion that
makes the projection of the scheme of abelian-scheme structures onto `S`
smooth. The module `Langlands.AlgebraicGeometry.ArtinianLiftingSmooth` defines
the lifting property `LiftsArtinian` of a morphism along the same elementary
extensions of Artinian local rings, and its theorem `smooth_of_liftsArtinian`
shows that this property makes a locally finite-type morphism to a locally
noetherian scheme smooth. The statement
`Langlands.AbelianScheme.PointedProjectiveAbelianLocusStatement` concerns the
open locus of Proposition 6.16 for pointed projective families.

## Source

The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
§6.3, Proposition 6.15, printed pp. 124–126 (PDF pp. 137–139); Definition 6.1
and Corollary 6.5 are in §6.1 of the same chapter.
