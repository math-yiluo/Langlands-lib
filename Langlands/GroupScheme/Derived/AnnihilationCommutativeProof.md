# Commutative targets annihilate the derived subgroup after scalar extension: proof

This module proves the published proposition
`Langlands.GroupScheme.DerivedCommutativeAnnihilationStatement` of
[`AnnihilationStatement`](AnnihilationStatement.md):

- `Langlands.GroupScheme.derivedCommutativeAnnihilation :
  DerivedCommutativeAnnihilationStatement.{u}`.

For every field `k`, every group scheme `G` over `Spec k` with affine and locally finite
type structure map, every `d : D ⟶ G` with `IsDerivedSubgroup d`, every commutative group
scheme `H` over `Spec k` with affine and locally finite type structure map, every
commutative `k`-algebra `R` with `b : Spec R ⟶ Spec k`, and every homomorphism
`f : G_R ⟶ H_R` of group schemes over `Spec R`, the composite `d_R ≫ f` is the trivial
group-scheme homomorphism `1`.

The source is J. S. Milne, *Algebraic Groups* (2017), Corollary 6.19(d), printed p.129 /
PDF p.145, registered as `milne-2017-algebraic-groups`. Milne's proof uses the local
commutator generation of 6.19(c). The proof here uses instead the Library's definition of
the derived subgroup as the intersection of all closed subgroups containing every
commutator, together with its published field base change.

## Internal lemma

`Langlands.GroupScheme.IsDerivedSubgroup.baseChange_algebra`. Let `k` be a field, `G` a
group scheme over `Spec k` with affine structure map, `d : D ⟶ G` with
`IsDerivedSubgroup d`, and `R` any commutative `k`-algebra. Then the base change of `d`
along `Spec.map (CommRingCat.ofHom (algebraMap k R))` again satisfies `IsDerivedSubgroup`.

Proof. The map `Spec R ⟶ Spec k` is a morphism of affine schemes, so it is affine
(instance inference). The published `derivedSubgroup_baseChange_eq_of_field` identifies the
base change of the derived subgroup functor of `G` with the derived subgroup functor of
`G_R`. The published `IsDerivedSubgroup.baseChange_of_eq` turns this equality into
`IsDerivedSubgroup` for the base-changed inclusion. No finite type hypothesis is used.

## Proof of the target

After introducing the binders, the `let`-bound base map is `b`. The structure map of
`H_R = (CommGroupScheme.baseChange b).obj H` is definitionally the second projection
`pullback.snd H.X.hom b`; it is affine because `H.X.hom` is affine and affineness is
stable under base change (instance inference after `change`). An affine morphism is
separated, so `H_R` is separated over `Spec R`; it is commutative as an actual
commutative group object. The published `IsDerivedSubgroup.comp_eq_one` says that every
homomorphism to a separated commutative group scheme is trivial on an actual derived
inclusion over the same base. Applied over `Spec R` to the inclusion `d_R` of the internal
lemma, it gives `d_R ≫ f = 1`.

The hypotheses `LocallyOfFiniteType G.X.hom` and `LocallyOfFiniteType H.X.hom` of the
statement are not used.

## Published inputs

- `Langlands.GroupScheme.derivedSubgroup_baseChange_eq_of_field`
  (module `Langlands.GroupScheme.Derived.FieldBaseChangeAssembly`).
- `Langlands.GroupScheme.IsDerivedSubgroup.baseChange_of_eq`
  (module `Langlands.GroupScheme.Derived.BaseChangeElementary`, imported through
  `Langlands.GroupScheme.Derived.FieldBaseChangeAssembly`).
- `Langlands.GroupScheme.IsDerivedSubgroup.comp_eq_one`
  (module `Langlands.GroupScheme.Derived.KernelAnnihilation`).

`#print axioms derivedCommutativeAnnihilation` reports only `propext`, `Classical.choice`
and `Quot.sound`.

## Attribution

The Lean proof is taken from the shared draft of Worker 3483 (Task 3483, draft revision 6,
`Langlands/GroupScheme/Derived/AnnihilationProof.lean`), split here into one module per
target.
