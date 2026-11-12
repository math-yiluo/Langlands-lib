# Quasi-separatedness and finite presentation of action quotients over a field

Author: Worker 79.

`ActionQuotientFinitenessStatement` states that an fppf quotient of a scheme of finite
type over a field by a quasi-compact group, with a smooth surjective quotient map and a
quotient locally of finite type, is quasi-separated and of finite presentation. It supplies
the finiteness assertions in clause 2 of `UnipotentOrbitQuotientStatement` and the
quasi-separatedness used in clause 3. The module states the claim and contains no proof.

## The statement

Notation is that of `UnipotentOrbitQuotientStatement.lean`. Let `k : Type u` be a field,
`G : GroupScheme (Spec k)` a group scheme with `G → Spec k` quasi-compact
(`QuasiCompact G.X.hom`), and `b : SchemeAction G Z` an action on a scheme
`Z : Over (Spec k)` that is locally of finite type and quasi-compact over `k`, i.e. of
finite type. Let `X : AlgebraicSpace (Spec k)` and let `π : h_Z ⟶ X` be a map of fppf
sheaves such that:

- `IsFppfActionQuotient b π`: `π` is the fppf sheaf quotient of `Z` by `b`;
- `IsSmooth π.hom` and `IsSurjective π.hom`: `π` is representable by schemes, and every
  base change of `π` along a map from a scheme is a smooth surjective morphism of schemes
  (`SmoothRelationQuotientStatement.lean`, `Basic.lean`);
- `LocallyOfFiniteTypeOverBase X`: `X` has a surjective étale atlas by a scheme locally of
  finite type over `k` (`StructuralAtlasGeometry.lean`).

The conclusion is `IsQuasiSeparated X ∧ FinitePresentationOverRing k X`: the diagonal of
`X` is representable by quasi-compact morphisms of schemes (`RingPoints.lean`), and `X`
has a surjective étale atlas by a scheme locally of finite presentation and quasi-compact
over `k` (`SpaceWeilRestriction.lean`).

## Sources

- Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
  registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Example 5.5,
  printed p.16: "there is a finitely presented algebraic space `X` over `k` and a
  faithfully flat map `V_d → X` that identifies `X` with the fppf sheaf quotient of `V_d`
  by its `G`-action". Section 5 works with quasi-separated algebraic spaces (printed
  p.13), which is how `UnipotentOrbitQuotientStatement.md` reads "finitely presented".
- The Stacks Project, Algebraic Spaces, full chapter PDF (registered source
  `stacks-algebraic-spaces-chapter-ed88ff78-2026-11-05`, SHA-256
  `49a75fa582cbeafadb9e1fbbdce130e5b8971322a2c0048d777e8a97f0d0fcf5`), Definition 65.13.2
  (Tag 02X5), part (3): "We say `F` is quasi-separated over `S` if `∆` is quasi-compact."

## Derivation (provenance: derived)

The statement isolates the finiteness part of Example 5.5. Conrad obtains it from
[Del2, Prop. 3.11]; here it is deduced from the existence of a smooth surjective quotient
map, which `SmoothStabilizerActionQuotientStatement` provides. The reason it holds:

- *Quasi-separated.* The base change of the diagonal of `X` along the smooth surjective
  map `Z × Z → X × X` is the monomorphism `Z ×_X Z → Z × Z`. The map
  `G × Z → Z ×_X Z`, `(g, z) ↦ (g.z, z)`, is surjective as a map of fppf sheaves (the
  quotient presheaf is `T ↦ Z(T)/G(T)`), hence surjective on points. As `G × Z` is
  quasi-compact, so is the scheme `Z ×_X Z`; it is locally of finite type over `k`
  (smooth over `Z`), hence Noetherian, so every morphism from it is quasi-compact.
  Quasi-compactness descends along fppf coverings, so the diagonal of `X` is
  quasi-compact.
- *Finite presentation.* Take an étale atlas `U → X` with `U` locally of finite type over
  `k`, and write `U` as a disjoint union of affine opens `U_j`. The images of the étale
  maps `Z ×_X U_j → Z` are open and cover `Z`; as `Z` is quasi-compact, finitely many
  suffice. Since `π` is surjective, the disjoint union of those finitely many `U_j` is
  still a surjective étale atlas. It is quasi-compact and of finite type over the
  Noetherian ring `k`, hence of finite presentation.

The hypothesis that `X` is locally of finite type is part of the conclusion of
`SmoothStabilizerActionQuotientStatement`. The names of the declarations are derived
here.
