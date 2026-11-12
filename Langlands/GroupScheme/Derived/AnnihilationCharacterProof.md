# Rational characters vanish on the derived subgroup after scalar extension: proof

This module proves the published proposition
`Langlands.GroupScheme.DerivedCharacterAnnihilationStatement` of
[`AnnihilationStatement`](AnnihilationStatement.md):

- `Langlands.GroupScheme.derivedCharacterAnnihilation :
  DerivedCharacterAnnihilationStatement.{u}`.

For every field `k`, every group scheme `G` over `Spec k` with affine and locally finite
type structure map, every `d : D ⟶ G` with `IsDerivedSubgroup d`, every commutative
`k`-algebra `R` with `b : Spec R ⟶ Spec k`, and every rational character `χ` of `G_R`, the
restriction `characterRestrict d_R χ` is the zero (trivial) character in the Library's
additive presentation of `rationalCharacters`.

The source is J. S. Milne, *Algebraic Groups* (2017), Corollary 6.19(d), printed p.129 /
PDF p.145, registered as `milne-2017-algebraic-groups`. Milne's proof uses the local
commutator generation of 6.19(c). The proof here uses instead the Library's definition of
the derived subgroup as the intersection of all closed subgroups containing every
commutator, together with its published field base change.

## Proof

After introducing the binders, the `let`-bound base map is
`b = Spec.map (CommRingCat.ofHom (algebraMap k R))`.

1. Base change. The map `b` is a morphism of affine schemes, so it is affine (instance
   inference). The published `derivedSubgroup_baseChange_eq_of_field`, applied to `b` and
   `G`, identifies the base change of the derived subgroup functor of `G` with the derived
   subgroup functor of `G_R`. The published `IsDerivedSubgroup.baseChange_of_eq` turns this
   equality into `IsDerivedSubgroup d_R` for `d_R = (GroupScheme.baseChange b).map d`.
2. Character form. The published `IsDerivedSubgroup.characterRestrict_eq_zero` says that
   every rational character restricts to zero on an actual derived inclusion over the same
   base. Applied over `Spec R` to `d_R` and `χ`, it gives `characterRestrict d_R χ = 0`.

The hypothesis `LocallyOfFiniteType G.X.hom` of the statement is not used.

## Published inputs

- `Langlands.GroupScheme.derivedSubgroup_baseChange_eq_of_field`
  (module `Langlands.GroupScheme.Derived.FieldBaseChangeAssembly`).
- `Langlands.GroupScheme.IsDerivedSubgroup.baseChange_of_eq`
  (module `Langlands.GroupScheme.Derived.BaseChangeElementary`, imported through
  `Langlands.GroupScheme.Derived.FieldBaseChangeAssembly`).
- `Langlands.GroupScheme.IsDerivedSubgroup.characterRestrict_eq_zero`
  (module `Langlands.GroupScheme.Derived.KernelAnnihilation`).

`#print axioms derivedCharacterAnnihilation` reports only `propext`, `Classical.choice` and
`Quot.sound`.

## Attribution

The Lean proof is taken from the shared draft of Worker 3483 (Task 3483, draft revision 6,
`Langlands/GroupScheme/Derived/AnnihilationProof.lean`), split here into one module per
target; the base-change step is written inline.
