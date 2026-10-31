# Two closed points lie in a common affine open

`Langlands.GroupScheme.algebraicallyClosedCommonAffine` proves exactly the
published proposition
`Langlands.GroupScheme.AlgebraicallyClosedCommonAffineStatement`. It imports
the target unchanged. For every universe `u`, every algebraically closed field
`K : Type u`, and every commutative group object
`G : Grp (Over (Spec (CommRingCat.of K)))` whose structure morphism is smooth,
proper and geometrically connected, it constructs an actual affine open of
`G.X.left` containing any two closed topological points `x` and `y`.

## Implemented argument

1. Smoothness supplies local finite type. The published theorem
   `SeparatingLineBundle.irreducibleSpace_of_smooth_of_isProper` supplies
   irreducibility of the underlying scheme with precisely the given
   geometric hypotheses. Mathlib's `pointOfClosedPoint` turns `x` and `y`
   into sections `x'` and `y'` of the structure morphism. Its section and
   evaluation lemmas show that these are actual rational points with
   underlying points exactly `x` and `y`.
2. Choose an affine open `U` containing `x`, using
   `exists_isAffineOpen_mem_and_subset` with the ambient open equal to the
   whole scheme.
3. The private `CommonAffine.translationIso` packages the existing
   `GroupScheme.translation G z` as an isomorphism in the slice category.
   Its inverse is translation by `z⁻¹`. The two inverse laws follow from
   `points_translation`, compatibility of precomposition with inversion,
   and the group cancellation laws on morphisms into `G.X`. Forgetting the
   slice gives a scheme isomorphism and hence a homeomorphism.
4. For each of the two sections `z = x', y'`, form the open subset
   `V_z = t_z⁻¹(U)`. Surjectivity of the translation homeomorphism and
   nonemptiness of `U` show that both opens are nonempty. Apply the published
   `SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen` to this
   two-element family. It supplies a rational section `s` whose underlying
   point belongs to both `V_x'` and `V_y'`. Thus `t_x'(s)` and `t_y'(s)`
   belong to `U`.
5. On rational sections, `z ≫ t_s = s * z`. The private lemma
   `CommonAffine.translation_apply_section` uses commutativity of the group
   of sections to identify `t_s(z)` with `t_z(s)`, then evaluates this
   equality at the unique point of `Spec K`. Consequently `t_s(x)` and
   `t_s(y)` belong to `U`.
6. The required open is `t_s⁻¹(U)`. It is affine by
   `IsAffineOpen.preimage_of_isIso`, and the preceding two membership
   calculations show that it contains `x` and `y`.

The Boolean index type only packages the two nonempty opens. It does not
impose distinctness on the points. No dimension, characteristic or
nontriviality assumption is used. In particular equal points and dimension
zero remain included.

## Source and derivation

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article, author corrected version of January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Theorem 7.1 is on p.10. Its proof on p.11 constructs a common affine
neighbourhood of the identity and a closed point by intersecting two
translates of an affine open and then translating again. Those two pages
were read directly.

The implementation uses the same translation argument in its equivalent
translation-parameter form: choose a rational parameter in the intersection
of the two preimages `t_x⁻¹(U)` and `t_y⁻¹(U)`, then take the affine open
`t_s⁻¹(U)`. This avoids an initial reduction to the identity point. The
extension to arbitrary, possibly equal, closed points and the use of
preimages are derived content. The closed-point/rational-point comparison,
affine-open basis and affine preservation are Mathlib results; the required
irreducibility and rational-point existence are imported from the published
`Langlands.AbelianScheme.SeparatingLineBundle.RationalPoints` module.

The complete registered author errata snapshot
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`, was
also read. It contains no correction to this part of Theorem 7.1.

## Scope

This proof adds no outer hypothesis, supplied affine neighbourhood,
certificate or axiom. It preserves the target and all imported Lean and
Markdown pairs. Its proof uses neither projectivity nor quasi-projectivity,
ampleness, a separating line bundle or a downstream consequence of those
results. The import of `GeometricPicardZero` provides the existing
translation construction; no Picard-zero assertion enters the proof.
