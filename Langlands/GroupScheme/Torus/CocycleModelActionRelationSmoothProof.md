# Smooth action relations on diagonalizable cocycle models: proof

`Langlands.GroupScheme.Diagonalizable.cocycleModelActionRelationSmooth` proves
`Langlands.GroupScheme.Diagonalizable.CocycleModelActionRelationSmoothStatement.{u}`
for every universe `u`. The data are a field `k` and a finitely generated
additive group `Λ`. `G` is a smooth group scheme over `Spec k` with affine
structure map, and `a` is an automorphic action of `D(Λ)` on `G`. `M` is a
cocycle model whose scheme has affine structure map, locally of finite type. The
conclusion is that `M.actionRelation`, `(g, x) ↦ (g • x, x)`, has smooth
underlying morphism.

This follows Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), proof of Proposition A.8.12, printed p.554 (PDF p.580), using
Proposition A.8.10(2), printed pp. 547–550 (PDF pp. 573–576). The source is
registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`. As there,
smoothness comes from the infinitesimal lifting criterion. The source lets the
acting group act on `G × X × X` by `h.(g,ρ,ρ′) = (ρ(h)gρ′(h)⁻¹,ρ,ρ′)`. It
applies A.8.10(2) to the equivariant projection to `X × X`, whose fixed source
consists of the triples with `g.ρ′ = ρ`. The Lean proof instead writes this
action on points of `G` with the two cocycles fixed. It lifts fixed points of
that action directly, through the published square-zero lifting of
diagonalizable fixed points after base change to the test ring.

## Finiteness and affineness

The structure maps of `G.X` and `M.scheme` are affine, so both schemes are
affine. Then `G.X ⊗ M.scheme` and `M.scheme ⊗ M.scheme` are affine, being
pullbacks over `Spec k`. The coordinate algebra of `G` is smooth over `k` by the
published `AffineCoordinates.smooth_algebra`, hence formally smooth.

`M.scheme` is locally of finite type over the Noetherian `Spec k`, hence locally
Noetherian by `LocallyOfFiniteType.isLocallyNoetherian`. So is
`M.scheme ⊗ M.scheme`. By `Over.w`, the composite of `M.actionRelation.left` with
the structure map of `M.scheme ⊗ M.scheme` is the structure map of
`G.X ⊗ M.scheme`. That structure map is locally of finite type, so
`locallyOfFiniteType_of_comp` makes `M.actionRelation.left` locally of finite
type. Mathlib's instance for locally finite-type morphisms into a locally
Noetherian scheme then makes it locally of finite presentation.

## The lifting problem

`AffineLifting.smooth_of_lifting` from `Langlands.AlgebraicGeometry.AffineLiftingSmooth`
reduces smoothness to square-zero lifting against test spectra. Let `C` be a
`k`-algebra and `I` an ideal with `I ^ 2 = ⊥`, and let `π : Spec (C ⧸ I) ⟶ Spec C`
be the reduction. Suppose `y : Spec C ⟶ M.scheme ⊗ M.scheme` and
`x₀ : Spec (C ⧸ I) ⟶ G.X ⊗ M.scheme` satisfy `x₀ ≫ M.actionRelation = π ≫ y`.

1. Write `x₀ = (g₀, m₀)` and `y = (yy, xx)`. Composing the
   action relation with a pair `(g, m)` gives `(g • m, m)`. Hence the square
   says `g₀ • m₀ = π ≫ yy` and `m₀ = π ≫ xx`.
2. Write `c(z)` for `M.cocycle z`. By `M.restrict_cocycle`, `M.cocycle_act`
   and the previous step, `g₀` conjugates the restriction of `c(xx)` along `π` to
   the restriction of `c(yy)`.
3. `I` is nilpotent, since `I ^ 2 = ⊥`. Apply
   `CharacterAction.exists_conjugate_lift` from
   `Langlands.GroupScheme.Torus.CocycleConjugacyLifting`, to `c(xx)`, `c(yy)` and
   `g₀`. It gives `g : Spec C ⟶ G.X` with `π ≫ g = g₀` and
   `conjugate g c(xx) = c(yy)`.
4. By `M.cocycle_act`, `c(g • xx) = conjugate g c(xx) = c(yy)`. Injectivity of
   `M.cocycle` (`M.cocycle_injective`) gives `g • xx = yy`.
5. The lift is `(g, xx)`. Its image under the action relation is
   `(g • xx, xx) = (yy, xx) = y`. Its restriction along `π` is
   `(π ≫ g, π ≫ xx) = (g₀, m₀) = x₀`.

## Scope

The proof uses only the hypotheses of the statement. It uses no finite
generation of `Λ`, torsion condition, characteristic assumption or reducedness
of `D(Λ)`. The field hypothesis enters only through the Noetherian property of
`Spec k`, which converts finite type into finite presentation. The model's
basepoint and orbit map are not used. The inspected axioms are `propext`,
`Classical.choice` and `Quot.sound`.
