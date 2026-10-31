# Algebraic cancellation along actual strong quasi-isomorphisms

This module proves that postcomposition by a strong quasi-isomorphism cancels
full strong maps whenever the intermediate and final original-chart atlases
are directed. It constructs the resulting categorical monomorphism proof
and an embedding of the actual strong-map hom sets. The argument uses the
unique bounded factorization property of affinoid domains, so it compares
the bounded algebra maps themselves.

The coefficient field `K : Type u` is a complete ultrametric normed field.
The ambient-space and chart-index universes `v` and `w` are independent of
`u`; the strong-map endpoints have the same triple `u, v, w`. The imported
chart algebras are actual finite positive-polyradius Tate quotients by closed
ideals. There is no strictness or reducedness assumption.

The original source is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definitions 1.2.7 and 1.2.9, printed pp.18–19
(PDF pp.15–16), and Proposition 1.2.10(d) and its proof, printed pp.19–20
(PDF pp.16–17), registered as `berkovich-1993-etale-cohomology`. The retained
original is `Berkovich--Etale cohomology for non-Archimedean analytic
spaces--1993.pdf`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These passages were reread for this construction; the project lookup found
no source-specific errata note. Proposition 1.2.10(d) asks for equality after
a further source quasi-isomorphism and proves the stronger equality of the
original strong maps. The proof first cancels the ambient homeomorphism,
then cancels the local affinoid-domain morphism. The implementation follows
these two steps in the already constructed directed-composition setting.
The directedness hypotheses restrict the scope relative to the original
general category, whose composition uses extended atlases and finite descent.

`PresentedAffinoidAlgebra.Represents.hom_ext` is the algebraic step, derived
directly from the imported full `Represents K i U` definition. For actual
presented algebras `D`, `E`, `R`, a representing bounded structural map
`i : D → E`, and bounded maps `ψ χ : E → R`, it proves
`ψ.comp i = χ.comp i → ψ = χ`. The spectrum map of `ψ.comp i` lands in `U`
because it factors through that of `i`. Both `ψ` and `χ` are then lifts of
the same bounded map from `D`, so uniqueness in the representation property
gives equality. The test algebra `R` is arbitrary among all finite
positive-polyradius presented affinoids. No faithfulness of the functor from
algebras to spectra is used.

In the namespace `AffinoidAtlasPresentation.StrongHom`,
`IsQuasiIso.cancel_compOfDirected` takes `s : StrongHom B C`, its actual
quasi-isomorphism proof, directedness of `B.atlas` and `C.atlas`, and full
strong maps `f g : StrongHom A B`. Equality of `f.compOfDirected s` and
`g.compOfDirected s` implies `f = g`. The source atlas of `A` need not be
directed. First, pointwise equality of the composite base maps and injectivity
of the homeomorphism underlying `s` give equality of `f.baseMap` and
`g.baseMap`. For every source chart `i`, target existence for `f` gives a
chart `j` of `B`; the base-map equality makes `j` admissible for `g` as well.
Target existence for `s` gives a containing chart `k` of `C`. Equality of the
composite full strong maps gives equality of their pullbacks at `(i, k)`.
The published exact `compOfDirected_pullback` formula identifies these
pullbacks with the composites of the original bounded maps at `(i, j)` and
`(j, k)`. The full representation property of `s` at `(j, k)` and
`Represents.hom_ext` cancel the latter structural map. The published
`ext_of_directed` theorem then extends the resulting equalities from these
witness pairs to equality of all strong-map data. The private helper
`pullback_eq_of_eq` transports admissibility proofs along equality of full
strong maps; its proof is substitution and reflexivity.

`IsQuasiIso.compOfDirected_eq_iff` packages cancellation and the immediate
converse as an equivalence of the two equalities.

For actual bundled `DirectedAtlasPresentation` objects,
`mono_of_isQuasiIso s hs` proves `CategoryTheory.Mono s` by the full
cancellation theorem. It assumes only the displayed quasi-isomorphism
property, which retains the actual ambient homeomorphism and bounded domain
representations at every admissible chart pair. The definition
`postcompQuasiIsoEmbedding s hs` constructs
`(A ⟶ B) ↪ (A ⟶ C)`, sending `f` to the actual category composite `f ≫ s`;
its injectivity proof is the same cancellation argument.
`postcompQuasiIsoEmbedding_apply` records this formula by reflexivity.
The embedding concerns full bounded strong maps, not just their underlying
continuous maps.

This is a derived progressive construction for the existing directed
original-chart category. It does not construct extended atlases, unrestricted
strong composition, closure under composition of quasi-isomorphisms, Ore
squares or a localization. It does not assert that arbitrary
quasi-isomorphisms have strong inverses. General analytic spaces, structure
sheaves, étale and equivariant sites, and the Harris tower remain separate
construction obligations.
