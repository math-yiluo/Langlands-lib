# Smooth action relations on diagonalizable cocycle models

`Langlands.GroupScheme.Diagonalizable.CocycleModelActionRelationSmoothStatement.{u}`
is an unproved proposition definition over an arbitrary field `k`. The
character group `Λ : Type u` is any finitely generated abelian group,
including groups with torsion divisible by the characteristic. For an
actual automorphic action of `D(Λ)` on a smooth affine group scheme `G`,
it asserts that every affine finite-type `CocycleModel M` has smooth
action relation

`G × M.scheme → M.scheme × M.scheme`, `(g,x) ↦ (g • x,x)`.

Here the morphism is the published `M.actionRelation`, built from its
actual scheme action. Smoothness is the usual scheme-morphism property
of its underlying morphism. The model includes an injection into actual
cocycles on every test scheme and the compatible conjugation action.
No reducedness, smoothness of the model, connectedness of `G`, or
reductivity of `G` is assumed. Finite type means affine and locally of
finite type; affineness supplies quasi-compactness.

This is the diagonalizable specialization, in actual cocycle coordinates,
of the smooth-action-map argument in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), proof of Proposition
A.8.12, printed p.554 (PDF p.580), using Proposition A.8.10(2).
The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The source applies smoothness of fixed points of an equivariant smooth
morphism to the projection `G × X × X → X × X`.
In cocycle coordinates the acting group's action on its first factor is

`h • (g,x,y) = (c_x(h) a(h,g) c_y(h)⁻¹,x,y)`.

Its fixed equation is exactly the conjugacy equation. Thus the relative
fixed-point argument applies to any represented stable subfunctor with
the model's injectivity and equivariance, rather than requiring the
particular indexing system of Lemma A.8.13. Making this identification
and proving the infinitesimal lifting property are retained proof
obligations. The existing smooth-fixed-subgroup result concerns
automorphisms of groups; it does not by itself prove this relative
scheme-morphism assertion.

This statement supplies no model existence, affine orbit, or reductivity
theorem.
