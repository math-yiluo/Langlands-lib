# Section evaluation for actual relative homomorphisms

Author: Worker 51.

For arbitrary commutative group schemes `G` and `H` over a scheme `S`, and an
arbitrary test scheme `T : Over S`, `RelativeHom G H T` is the actual categorical
Hom from the pullback of `G` to the pullback of `H`. The category
`Langlands.CommGroupScheme` writes this Hom group additively. No pointwise group
homomorphism is supplied as an independent input.

`sectionBaseIso T` is the canonical isomorphism from the identity map of `T`,
regarded over `S`, to `T` itself. `sectionPointsEquiv G T` combines that
isomorphism with the published multiplicative `baseChangePointsEquiv` to identify
sections of the actual pullback group scheme with `T`-points of `G`.
`sectionPointsEquiv_left` records that the forward map composes the underlying
scheme morphism with the first projection of the pullback.

`evaluation χ` sends a `T`-point to its corresponding section, postcomposes
with the actual relative group-scheme homomorphism `χ`, and returns to a
`T`-point of `H`. It is bundled as a multiplicative homomorphism in the point
argument. `evaluation_def` records this exact formula. The lemmas
`evaluation_one`, `evaluation_mul`, and `evaluation_inv` express the group laws
in the point argument. The lemmas `evaluation_zero`, `evaluation_add`, and
`evaluation_neg` express the pointwise additive group law in the relative-Hom
argument, whose values are multiplied in `H(T)`. `evaluationAddHom` bundles
this latter additivity after applying the `Additive` type synonym to `H(T)`.

`evaluation_id` and `evaluation_comp` prove that identity and composition of
relative homomorphisms act as identity and composition on points.
`sectionPointsEquiv_comp` proves compatibility of the section identification
with a global group-scheme homomorphism. Consequently,
`evaluation_baseChange` identifies evaluation of a base-changed global
homomorphism with ordinary postcomposition of the point.
`evaluation_precompose` and `evaluation_postcompose` give the resulting
compatibility in the source and target group schemes.

For any integer `n`, suppose the actual multiplication morphism
`multiplication G.toGrp n` equals `1` in the multiplicatively written Hom group
of group objects. Here `1` is the constant unit morphism; it corresponds to the
zero morphism in the additive category of commutative group schemes.
`points_zpow_eq_one` deduces that every point of `G` is killed by `n`, and
`evaluation_zpow_eq_one` transfers this fact through evaluation.
`torsionEvaluation` then uses the inverse of the published
`torsionPointsEquiv` to produce a point of the **actual torsion scheme** of `H`.
`torsionEvaluation_ι` proves that its inclusion is ordinary evaluation, and
`torsionEvaluation_unique` proves uniqueness using the monomorphism of the
kernel inclusion. The multiplication, addition, unit, zero, inverse and
negation lemmas for `torsionEvaluation` follow by canceling this same inclusion.
The integer formulation includes every positive natural integer; no
annihilation assumption is imposed on ordinary evaluation.

These are derived categorical constructions motivated by Edixhoven–van der
Geer–Moonen, *Abelian Varieties*, preliminary draft built 2012-02-08,
(3.21), printed p.41/PDF45, which defines characters as actual relative group
scheme homomorphisms into the multiplicative group. The section formula is the
intrinsic evaluation occurring in (11.11)(i), printed p.162/PDF166, and its
bilinearity convention is stated immediately below (11.11). That passage also
notes the factorization through roots of unity under annihilation. Our module
proves the more general elementary construction for an arbitrary commutative
target `H`, using the existing pullback and torsion-kernel infrastructure. It
does not use the separate representability theorem (3.22) or the geometric
kernel-duality isomorphism mentioned in (11.11).

The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`, retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
PDF45–47 and PDF166 were read and the fingerprint verified. No corresponding
source erratum was found in the project or published notes.

This module supplies the section-evaluation component of the Cartier task.
Restriction in the test scheme, the relative-Hom presheaf, specialization to the
constructed multiplicative group scheme, and affine roots-of-unity comparisons
are separate remaining components. It asserts no Cartier representability,
finite local freeness, biduality, or duality of isogeny kernels.
