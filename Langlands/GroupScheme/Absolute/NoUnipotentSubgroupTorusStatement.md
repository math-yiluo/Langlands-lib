# Statement: a group variety without unipotent subgroups is a torus

Worker 75.

`Langlands.GroupScheme.NoUnipotentSubgroupTorusStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Absolute.Borel`](Borel.md), which supplies, directly or
through its imports, the group-scheme vocabulary over a field, `IsClosedSubgroup` and
`IsUnipotent` ([`Reductive.Basic`](../Reductive/Basic.md)) and `IsTorus`
([`Torus.Lattice`](../Torus/Lattice.md)).

## Lean statement

```lean
def NoUnipotentSubgroupTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∀ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G), IsClosedSubgroup u →
        Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
          SubgroupFunctor.range u = ⊥) →
      IsTorus G
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`; `G.X.left` is the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsClosedSubgroup u` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism
  of schemes of `u` is a closed immersion.
- `IsUnipotent U` ([`Reductive.Basic`](../Reductive/Basic.md)): every nonzero
  finite-dimensional representation of `U` has a nonzero fixed vector.
- `SubgroupFunctor.range u = ⊥`: the only point of `G`, over any scheme over `Spec k`, that
  factors through `u` is the identity. As `u` is a monomorphism, this says that `U` is the
  trivial group.
- `IsTorus G` ([`Torus.Lattice`](../Torus/Lattice.md)): `G` becomes a split torus after base
  change to some field extension of `k`.

## Statement and quantifiers

For every algebraically closed field `k : Type u` and every smooth, affine, connected group
scheme `G` over `Spec k`: if every closed subgroup `u : U ⟶ G` with `U` smooth, connected and
unipotent is trivial, then `G` is a torus.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 17.25, p.359: "If G contains no nontrivial connected unipotent subgroup variety,
  then it is a torus. This is true, for example, if all elements of G(k) are semisimple."
- Section 17b, opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k."
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; p.13:
  "group variety" = "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. None concerns Corollary 17.25.

Milne's proof: for a Borel pair `(B, T)`, `B = B_u ⋊ T` (16.33); the hypothesis forces
`B_u = e`, so `B` is nilpotent, and Proposition 17.23 gives `G = B = T`. This is explanation
only.

## Derivation from the source

- **Connected group variety.** As in Section 17b: `[IsAlgClosed k]`, `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **Connected unipotent subgroup varieties.** A subgroup variety is a smooth algebraic
  subgroup, so a closed subgroup `u : U ⟶ G` with `U` smooth; "connected" and "unipotent" are
  `ConnectedSpace U.X.left` and `IsUnipotent U`. "Nontrivial" is negated by
  `SubgroupFunctor.range u = ⊥`, the form the Library uses for trivial subgroups.
- **Torus.** Over an algebraically closed field a torus is a split torus; the Library predicate
  `IsTorus` (split after some field extension) agrees with it there.

## Scope

- The second sentence of the corollary (the case where every element of `G(k)` is semisimple)
  is not stated: the Library has no predicate for semisimple elements of a group scheme over a
  field.
- Only algebraically closed fields are covered, as in Milne's Section 17b.

## Related Library results

- [`Torus.NoTorusBasicReductionStatement`](../Torus/NoTorusBasicReductionStatement.md) treats
  the opposite situation (no nontrivial torus implies unipotent) in the nilpotent and
  finite-field cases.
