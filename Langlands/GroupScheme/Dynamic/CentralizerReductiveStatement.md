# Connected reductivity of actual dynamic centralizers

`Langlands.GroupScheme.DynamicCentralizerReductiveStatement.{u}` is a
`Prop`-valued definition with the following complete scope. For every field
`k : Type u`, every group scheme `G` over `Spec (CommRingCat.of k)` satisfying
the existing `IsConnectedReductive G`, every cocharacter
`χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G`, every group scheme `M` over
the same base, and every group-scheme homomorphism `j : M ⟶ G`, it asks that

```text
IsClosedSubgroup j →
(Dynamic.centralizer χ).IsRepresentedBy j →
IsConnectedReductive M.
```

Here `IsClosedSubgroup j` says that the underlying scheme morphism is a
closed immersion. The existing `SubgroupFunctor.IsRepresentedBy` says that
the underlying relative morphism is a monomorphism and that
`SubgroupFunctor.range j = Dynamic.centralizer χ`. This equality is on all
test schemes over `Spec k`, including non-affine and nonreduced schemes.
Membership in `Dynamic.centralizer χ` means that the conjugation orbit map
is the constant map with value the given point. It therefore expresses
commutation with the cocharacter after every change of test scheme.

The conclusion uses `IsConnectedReductive` from
`Langlands.GroupScheme.Reductive.Basic`: `M` is smooth, affine and connected,
and its base change to `AlgebraicClosure k` has trivial unipotent radical in
the existing all-test closed-subgroup sense. The definition quantifies over
every actual closed representative `j`, without choosing a preferred one.
It assumes no splitness, perfectness, restriction on characteristic, maximal
torus, local-field structure, reductivity of `M`, or structural theorem.
Every cocharacter is included, in particular the trivial cocharacter, whose
centralizer is the whole group.

The provenance is a derived consequence of B. Conrad, O. Gabber and
G. Prasad, *Pseudo-reductive groups*, second edition (2015), rather than a
verbatim formulation of a single proposition:

- Proposition 2.1.8(3),(4), printed pp. 53–54 (PDF pp. 79–80; the preceding
  discussion starts on printed p. 52), gives smoothness of the dynamic
  centralizer for a smooth affine group of finite presentation, and
  connectedness of that centralizer when the group has connected fibers.
- Proposition 1.2.4 and its proof, printed pp. 13–14 (PDF pp. 39–40), states
  the pseudo-reductivity of torus centralizers in pseudo-reductive groups
  and recalls that a torus centralizer in a connected reductive group is
  connected reductive.

The intended deduction applies the torus-centralizer result after extending
to an algebraic closure: the image of a cocharacter is a split torus
(possibly trivial), and its centralizer is the cocharacter centralizer.
The all-test centralizer commutes with base change, as proved in the
existing `Dynamic.centralizer_baseChange` in
`Langlands.GroupScheme.Dynamic.BaseChange`. Together with the dynamic
smoothness and connectedness results and closedness in the affine group,
this gives the geometric-radical condition required by the Library
definition over an arbitrary field. This paragraph records the provenance
route; this module does not implement that deduction.

The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The Lean module imports only the existing dynamic and reductive definitions.
It defines a proposition, supplies no proof of it, and constructs no
centralizer representative. Proving the proposition and establishing
representability or existence remain separate obligations.
