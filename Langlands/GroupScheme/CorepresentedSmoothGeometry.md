# Coordinate algebras of smooth corepresented groups over a field

Authors: Worker 254.

This module collects three small geometric facts about group schemes. Worker
266's separably closed case of CGP Proposition C.1.6 uses them. Each fact is
standard; the module only transfers known scheme-level facts to the
coordinate algebra of a group given by an explicit coordinate algebra.
Everything lives in the namespace `Langlands.GroupScheme`.

The corepresented groups come from `Langlands.GroupScheme.Corepresented`.
Take a field `k`, a group-valued functor `F` on `k`-algebras, and a
`k`-algebra `B` with a corepresentation `e` of `F` (as a functor to sets) by
`B`. Then `Corepresented.groupScheme F e` is the group scheme over
`Spec k` with underlying scheme `Spec B`, whose structure morphism is
`Spec.map` of the algebra map `k → B`.

## Main results

- `surjective_hom`: for every scheme `S` and every group scheme `P` over `S`,
  the structure morphism `P.X.hom` is surjective. The base `S` is arbitrary;
  the case needed for C.1.6 is `S = Spec k` for a field `k`.
- `isGeometricallyReduced_of_geometricallyReduced_spec`: let `A` be a
  `k`-algebra. If the morphism `Spec A → Spec k` given by the algebra map is
  geometrically reduced in the sense of Mathlib's `GeometricallyReduced`,
  then `A` is geometrically reduced over `k` in the sense of Mathlib's
  `Algebra.IsGeometricallyReduced`.
- `Corepresented.isGeometricallyReduced_of_smooth`: if the structure morphism
  of `Corepresented.groupScheme F e` is smooth, then `B` is geometrically
  reduced over `k`.
- `Corepresented.isDomain_of_smooth_connected`: if the structure morphism of
  `Corepresented.groupScheme F e` is smooth and affine, and its underlying
  scheme is connected, then `B` is an integral domain.

In `isDomain_of_smooth_connected` the affineness hypothesis always holds,
since the underlying scheme is `Spec B`. It is kept as an instance argument
because the Library's `smoothConnectedAffineGeometry` takes it.

## Proof

Surjectivity. The unit `η` of `P` is a morphism over `S` from the terminal
object, so `η.left ≫ P.X.hom = 𝟙 S`. Hence every point `s` of `S` is the
image under `P.X.hom` of the point `η.left s`.

Geometric reducedness from the scheme statement. Let `k̄` be the algebraic
closure of `k`. Mathlib's `Algebra.isGeometricallyReduced_field_iff` reduces
the claim to `k̄ ⊗[k] A` being reduced. The hypothesis, applied to the point
`Spec k̄ → Spec k`, says that the pullback of `Spec A → Spec k` along it is a
reduced scheme. Mathlib's `pullbackSpecIso` identifies this pullback with
`Spec (A ⊗[k] k̄)`, so `A ⊗[k] k̄` is reduced. The commutativity isomorphism
of the tensor product then gives that `k̄ ⊗[k] A` is reduced.

Smooth case. The Library theorem
`Langlands.AlgebraicGeometry.smoothGeometricallyReduced` says that smooth
morphisms are geometrically reduced. The structure morphism of
`Corepresented.groupScheme F e` is `Spec.map` of `k → B` by definition, so
the previous result gives that `B` is geometrically reduced.

Domain. The Library theorem `smoothConnectedAffineGeometry` (first part)
says that a smooth, affine, connected group scheme over a field is
geometrically integral. Since `Spec k` has one point, Mathlib's
`GeometricallyIntegral.isIntegral_of_subsingleton` gives that the underlying
scheme `Spec B` is integral. Mathlib's `affine_isIntegral_iff` then says
that `B` is a domain.

## Provenance

This is internal infrastructure for the formalization of CGP Proposition
C.1.6 (Conrad, Gabber and Prasad, *Pseudo-reductive groups*, 2nd ed.,
printed p.586). Worker 266 requested these facts for the separably closed
case of that proof, where the coordinate algebra of the smooth connected
group `G` must be a geometrically reduced domain and the structure maps of
the group schemes involved must be surjective. None of them is a numbered
statement in CGP; each is a standard consequence of results already in the
Library or in Mathlib, as described above.
