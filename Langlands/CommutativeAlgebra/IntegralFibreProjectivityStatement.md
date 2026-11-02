# Projectivity for flat algebras with geometrically integral fibres

The proposition
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement.{u}`
states that a flat, finitely presented commutative algebra `S` over a
commutative ring `R` is projective as an `R`-module if its spectrum morphism
has geometrically integral fibres. Both rings range over the arbitrary
universe `u`; no Noetherian or valuation-ring assumption is imposed.
This file states the result and supplies no proof.

The original is the Stacks Project, More on Flatness, Lemma 38.9.3
([tag 05FT](https://stacks.math.columbia.edu/tag/05FT)). The retained original
is `05FT.html` in the registered source
`stacks-integral-fibre-projectivity-05ft-2026-11-02`, content fingerprint
`7c78bdc42ba48789408fa5888590d1b55551ed72ad6efa68d3ac63f43007f9ab`.
Its assumptions are finite presentation and flatness of `R → S`, and
geometric integrality of `S ⊗[R] κ(p)` over `κ(p)` at every prime `p` of
`R`; its conclusion is projectivity of `S` as an `R`-module.

The Lean statement uses `Algebra.FinitePresentation`, `Module.Flat`, and
`Module.Projective` for these three algebraic properties. Its fibre
condition is Mathlib's `GeometricallyIntegral` on the actual spectrum
morphism of `algebraMap R S`. By
`AlgebraicGeometry.GeometricallyIntegral.iff_geometricallyIntegral_fiber`,
this is equivalent to geometric integrality of every residue-field fibre
morphism. The affine fibre is the spectrum of the corresponding tensor
product, so this is precisely the fibre condition in 05FT.
Integrality includes nonemptiness: empty fibres are not permitted.
No claim is made that an arbitrary smooth algebra satisfies this condition.

The source proof descends to a flat finite type algebra over a finitely
generated integer algebra with geometrically integral fibres, applies the
Noetherian result in Lemma 38.9.2 (tag 05FS), and extends scalars.
That proof route is background for the statement, not implemented Lean.
The complete retained 05FT page, including its empty comment section, was
read; no source-specific project errata note was found in the project or
startup Library notes.
