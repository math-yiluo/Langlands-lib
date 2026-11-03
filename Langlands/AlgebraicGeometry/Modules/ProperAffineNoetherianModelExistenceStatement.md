# Noetherian approximation for a proper scheme with two modules

`Modules.ProperAffineNoetherianModelExistenceStatement.{u}` asserts that,
for every commutative ring `R` and proper locally finitely presented
`p : Y → Spec R`, two finitely presented module sheaves `M, N` with `N`
flat over `Spec R` admit a model satisfying
`Modules.HasAffineNoetherianModel p M N`.

The conclusion contains a noetherian ring `R₀` and a ring map
`φ : R₀ → R`, a proper locally finitely presented morphism
`p₀ : Y₀ → Spec R₀`, and finitely presented actual module sheaves
`M₀, N₀` on `Y₀`, with `N₀` flat over `Spec R₀`. It also contains a
morphism `q : Y → Y₀` making the square with vertical maps `p, p₀` and
lower horizontal map `Spec.map φ` Cartesian, and actual isomorphisms
`q* M₀ ≅ M` and `q* N₀ ≅ N` for ordinary module pullback. All rings and
schemes are in the same universe `u`.

The input base is affine but its ring need not be noetherian. No source
module flatness, ambient flatness, smoothness or local freeness is
required. The conclusion is a model of the actual scheme and module
sheaves, preserving target relative flatness. The statement supplies
neither a global model over an arbitrary base nor a Hom representer.

The source is the Stacks Project, *Limits of Schemes*, retained
`limits.tex` at commit `a04446e5`, registered as
`stacks-limits-of-schemes-a04446e5`. The relevant passages are Lemma
01ZM (`lemma-descend-finite-presentation`, lines 2369–2545), Lemma 01ZR
(`lemma-descend-modules-finite-presentation`, lines 2547–2605), Lemma
05LY (`lemma-descend-module-flat-finite-presentation`, lines 2666–2719),
and Lemma 081F (`lemma-eventually-proper`, lines 3264–3306, with its
setup in `situation-descent-property`). The final paragraph of the
proof of Stacks Project Proposition 99.3.10, in the separately retained
`08JS.html` registered as `stacks-hom-functor-08js-2026-11-02`, explains
the noetherian approximation route for proper Hom.

The proposition packages the following application of these limit
results. Express `R` as the filtered colimit of its finitely generated
`ℤ`-subalgebras. Properness and local finite presentation give finite
presentation of `p`; descend that scheme and the two finitely
presented module sheaves to a finite stage. At a later common stage,
the target module is flat over the stage base by 05LY and the scheme
morphism is proper by 081F. The stage ring is noetherian because it is
a finitely generated `ℤ`-algebra. The ordinary pullback descriptions
give precisely the Cartesian square and module isomorphisms in the
conclusion. The chosen definition asks only for noetherian `R₀`, so it
does not retain the stronger finite generation over `ℤ`.

This file defines the proposition and supplies no proof of it.
