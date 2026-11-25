# The polarization is determined by its cubic bundle up to a twist from the base

`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundlePolarizationDeterminationStatement`
is a proposition definition (universe `u`). It is a statement target only; this
module proves nothing.

## The statement

Fix `P : Prerequisites.{u}`, a locally noetherian scheme `S`, natural numbers
`g d n`, and two ordinary polarized finite-level data `a b : Datum P S g d n`
(module `Data`). Let `e : a.abelian ≅ b.abelian` be an isomorphism of abelian
schemes over `S` and `N` a line bundle on `S`. Assume there is an isomorphism of
line bundles on the total space of `a.abelian`

`(hom e.hom)^* (b.cubicBundle) ≅ a.cubicBundle ⊗ π_a^* N`,

where `π_a = a.abelian.X.hom` is the structure morphism, `hom e.hom` is the
underlying scheme morphism of `e`, and `⊗` is `LineBundle.tensor` with the
tensor comparison `P.preservation`. Then

`a.polarization = e.hom ≫ b.polarization ≫ a.dualWitness.map P b.dualWitness e.hom`.

The right side is the pullback of the polarization of `b` along `e`: first `e`,
then `λ_b`, then the dual of `e` from the dual of `b` to the dual of `a`
(`DualWitness.map`, computed with the two data's own dual witnesses). This is
exactly the `polarization_eq` field of `PolarizedIso`. Nothing is assumed about
the level structures, and the conclusion says nothing about them.

The cubic bundle `a.cubicBundle` is the tensor cube of `a.canonicalBundle`, the
pullback of the Poincaré bundle along `(1, λ_a)` (module `CanonicalBundle`).

## Mathematical content and source

This is the step "the polarization is determined by the embedding" in
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), §7.2,
printed p.131 (PDF p.144), registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`:
the relation `(*)` there identifies `L_Δ(ω)^3` up to a bundle from the base;
"therefore `L_Δ(ω)^3` is determined ... But the group of `S`-homomorphisms from
`X` to `X̂` has no torsion, hence `ω` is determined."

In the present notation: the Mumford map of `L_Δ(λ) = (1, λ)^* 𝒫` is `2λ`, so
that of the cubic bundle is `6λ` (compare the field statement
`CubicBundleMumfordStatement`). The Mumford map of a bundle pulled back from the
base is zero, and pulling back along `e` conjugates Mumford maps by `e` and its
dual. Hence the hypothesis gives `6λ_a = e^∨ ∘ 6λ_b ∘ e`. Over a field the group
of homomorphisms between abelian varieties is torsion free (Mumford, *Abelian
Varieties*, §19), so the two sides agree on every geometric fibre, and by
rigidity (GIT Corollary 6.2) a homomorphism of abelian schemes over a connected
locally noetherian base that vanishes on one fibre vanishes. The locally
noetherian hypothesis on `S` is the case needed for ordinary moduli (all level
bases are locally noetherian); it makes connected components open.

## Use

This is the polarization input for showing that a frame-normalized datum is
determined, up to `PolarizedIso`, by the image of its canonical projective
embedding and its torsion sections (frame-chart representability,
`FrameChartRepresentabilityStatement`; module `FrameChartRepresentabilityReduction`). There the two cubic bundles are both
the pullback of `𝒪(1)` twisted by line bundles from the base.
