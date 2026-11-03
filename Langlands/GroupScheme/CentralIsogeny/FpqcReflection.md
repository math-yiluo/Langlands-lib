# fpqc reflection of central isogenies

Authors: Worker 712 and Worker 1347.

Module `Langlands.GroupScheme.CentralIsogeny.FpqcReflection` proves the
published statement `Langlands.GroupScheme.CentralIsogenyFpqcReflectionStatement.{u}`
from `Langlands.GroupScheme.CentralIsogeny.FpqcReflectionStatement`, for
arbitrary universe `u`:

```lean
theorem centralIsogenyFpqcReflection : CentralIsogenyFpqcReflectionStatement.{u}
```

So for every surjective, flat, quasi-compact `b : S' ⟶ S`, every pair of
group schemes `G H : GroupScheme S` and every homomorphism `f : G ⟶ H`, if
`(GroupScheme.baseChange b).map f` is a central isogeny then `f` is a central
isogeny, with the unchanged definition `IsCentralIsogeny` from
`CentralIsogeny.Basic`. No hypothesis is added to the statement.

## Pullback square

`baseChange_map_isPullback b f` states that the square

```text
(G ×_S S') --(baseChange b).map f--> (H ×_S S')
     |                                    |
pullback.fst G.X.hom b           pullback.fst H.X.hom b
     v                                    v
    G.X  ------------- f -------------->  H.X
```

of underlying scheme morphisms is a pullback square. The underlying map of
`(GroupScheme.baseChange b).map f` is `((Over.pullback b).map f.hom.hom).left`.
Composed with the projection to `S'`, the square with `G.X ⟶ S` along `b` is
the defining pullback of `G.X.hom` and `b`. The right-hand square is the
defining pullback of `H.X.hom` and `b`, so the pasting lemma
`IsPullback.of_right` gives the left-hand square.

## Proof

The right vertical map `pullback.fst H.X.hom b` is a base change of `b`, so it
is again surjective, flat and quasi-compact. Mathlib's
`MorphismProperty.of_isPullback_of_descendsAlong` applied to the pullback
square then transfers each of the four geometric conditions from the
base-changed homomorphism to `f.hom.hom.left`:

- finiteness, by `descendsAlong_isFinite_surjective_inf_flat_inf_quasicompact`;
- flatness, by `descendsAlong_flat_surjective_inf_flat_inf_quasicompact`;
- surjectivity, by Mathlib's fpqc descent of `Surjective`;
- local finite presentation, by Mathlib's fpqc descent of
  `LocallyOfFinitePresentation` in `Morphisms.LocalFlatDescent`.

The first two instances are in
`Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent`. Finiteness descent
there uses Zariski's main theorem (finite = proper and locally quasi-finite)
and requires no affineness descent.

Centrality of the full scheme-theoretic kernel inclusion is
`isCentral_kernelι_of_baseChange b f hf.isCentral_kernelι` from
`Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers` (Worker 1347).
It tests every point of every test scheme over `S` and needs only that `b` is
flat and surjective; no representable centre is used.

## Provenance

The statement's provenance is documented in `FpqcReflectionStatement.md`. The
proof follows the route described there: fpqc descent of the four
scheme-morphism properties of the underlying map, and reflection of the
commutation identities defining kernel centrality along the flat surjective
projection of each test scheme.
