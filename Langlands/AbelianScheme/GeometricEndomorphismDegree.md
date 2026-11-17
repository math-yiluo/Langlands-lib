# The geometric degree of an integral abelian endomorphism

`Langlands.AbelianScheme.geometricEndomorphismDegree` assigns a nonnegative
integer, represented in Lean by `ℕ`, to every actual integral endomorphism
`f : End A` of an actual abelian scheme `A` over `Spec k`. The construction
works for a field `k : Type u` in every universe `u`. In particular it applies
to the algebraically closed characteristic-zero fields used by the separate
polynomiality statement.

## The morphism, point and rank

`End A` abbreviates `CategoryTheory.End A`, whose elements are actual
homomorphisms `A ⟶ A`. These are homomorphisms of the underlying commutative
group schemes, written in additive notation. `groupHom f` removes that
additive notation and is a homomorphism `A.toGrp ⟶ A.toGrp` of group objects
over the base. Forgetting the group operations and then the structure map to
the base gives

```lean
hom f = (groupHom f).hom.hom.left : A.X.left ⟶ A.X.left.
```

Here `A.X` is the underlying object of `Over (Spec (CommRingCat.of k))`;
`A.X.left` is its total scheme. The field is bundled as the commutative ring
`CommRingCat.of k`, and `Spec` takes its scheme spectrum.

The unit `η[A.X]` is a morphism from the monoidal unit in the category of
schemes over the base to `A.X`. Its `.left` component is the actual section
`Spec k ⟶ A.X.left`. The expression
`Classical.arbitrary (Spec (CommRingCat.of k))` denotes a point of the
underlying topological space of `Spec k`, using the coercion from schemes
to their carrier types. A field spectrum has exactly one point, namely
the zero prime ideal. Thus this choice specifies that unique point.
Applying the unit section as a function on underlying points produces the
identity point of `A.X.left`.

The predicate `GroupScheme.IsIsogeny (groupHom f)` says that the very same
scheme morphism `hom f` is finite, flat and surjective. In this case the
definition is

```lean
(hom f).finrank (η[A.X].left (Classical.arbitrary (Spec (CommRingCat.of k)))).
```

This is Mathlib's native `AlgebraicGeometry.Scheme.Hom.finrank`, constructed
from ranks of the actual affine coordinate ring maps. For a finite flat
morphism it measures the finite locally free rank; in the present setting
local finite presentation follows from finite type geometry over a field.
The target abelian variety is connected, so this locally constant rank
has one value. Evaluating at the identity selects that value. If the
isogeny predicate is false, the definition is zero. The noncomputable
section supplies classical decidability of the predicate and the unique
base point.

## Source and scope

The source is J. S. Milne, *Abelian Varieties* (1986 article, author revision
January 2, 2022), source ID
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Section 12, top of printed/PDF p.21, defines the degree of an integral
endomorphism to be its isogeny degree when it is an isogeny and zero
otherwise. Section 8, Proposition 8.1 and the paragraph following it on
printed/PDF p.12, identify isogenies with finite flat surjective
homomorphisms and their degree with the order of the finite kernel,
equivalently the rank of the finite locally free direct image of the
structure sheaf. The native rank above represents this geometric degree.
The complete registered errata snapshot
`milne-abelian-varieties-1986-errata-2026-10-25` was read; it states that the
corrections are incorporated in the retained author revision.

This module constructs the integral degree from the actual morphism. The
rational extension and its properties belong to the separate existential
polynomiality statement. That statement deliberately restricts the
source's general field scope to algebraically closed fields of
characteristic zero.
