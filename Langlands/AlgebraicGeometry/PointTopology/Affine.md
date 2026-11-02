# Evaluation topology on affine points

Author: Worker 105.

This construction implements the intrinsic topology in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 2.1, printed page 2, and the composition maps used in
Example 2.2 on page 3. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, retained at
`/home/taskhub/central-library/Conrad--Weil and Grothendieck approaches to adelic points--2011.pdf`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The module is `Langlands.AlgebraicGeometry.PointTopology.Affine`, in namespace
`Langlands.AlgebraicGeometry.PointTopology`.

## Actual points and topology

For commutative rings `R`, `A`, and `S`, with `R`-algebra structures on `A`
and `S`, `AlgPoint R A S` is a named copy of the actual algebra-map type
`A →ₐ[R] S`. The inverse conversions `toAlgHom`, `ofAlgHom`, and
`algHomEquiv` have no extra data or hypotheses. The named carrier allows
the module to install its topology without assigning a global topology to
every algebra-map type.

Given any topology on `S`, the topology on `AlgPoint R A S` is induced
by `AlgPoint.evaluation` into the product space `A → S`. The proved
`isEmbedding_evaluation` identifies it with the subspace of all functions
that are algebra maps. `continuous_eval` and `continuous_iff` give its
universal property: a map into the point space is continuous exactly when
every coordinate evaluation is continuous. If `S` is Hausdorff, the
point space is Hausdorff by this embedding.

No topology is required on `R` or `A`, and continuity of the ring operations
on `S` is unnecessary for this initial construction. Conrad's intrinsic
definition makes sense at this generality. Finite generation and
continuity of ring operations are needed for later comparisons with
finite coordinate presentations and their consequences.

## Functorial comparison constructions

`AlgPoint.precomp` is composition with a map of coordinate algebras,
with the contravariant direction appropriate to scheme points.
`continuous_precomp`, `precomp_id`, and `precomp_comp` verify continuity
and the two functorial identities directly on algebra maps.
`AlgPoint.congr e`, for `e : A ≃ₐ[R] B`, is a homeomorphism from
`AlgPoint R A S` to `AlgPoint R B S`. Its forward map sends `p` to
`p ∘ e.symm`; its inverse sends `q` to `q ∘ e`.

`AlgPoint.mapCoefficients` composes a point with an actual map `S →ₐ[R] T`.
It is continuous if that coefficient map is continuous, and
`precomp_mapCoefficients` proves the square with a change of coordinate
algebra commutes. These are actual composition maps, with no assumed
topology properties packaged as structure fields.

## Scheme comparison and scope

For rings in a common arbitrary universe, `SpecPoint R A S` is the
actual subtype of scheme morphisms `Spec S ⟶ Spec A` whose composite
with `Spec A ⟶ Spec R` is the prescribed `Spec S ⟶ Spec R`.
`specPointEquiv` reuses Mathlib's `Spec.homEquivAlgHom`, which proves this
actual scheme/algebra correspondence. The topology on these scheme
points is transported along that equivalence; `specPointHomeomorph`
proves the resulting comparison is a homeomorphism.

This is the affine point construction and its intrinsic comparison
lemmas. It does not assert the whole of Proposition 2.1: the comparison
with finite coordinate presentations, uniqueness from Conrad's functorial
axioms, products and fibre products, embeddings from closed immersions,
and local compactness remain separate statement and proof obligations.
The embedding, closed-embedding and open-embedding assertions for
coefficient changes in Example 2.2 also remain separate obligations.
This module does not impose local-ring, open-unit, inversion, field, or
separatedness assumptions, and makes no claim yet about nonaffine,
adelic, or algebraic-space topologies.
