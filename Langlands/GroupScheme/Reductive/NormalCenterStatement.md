# Full centres of normal connected reductive subgroups

`Langlands.GroupScheme.NormalReductiveCenterStatement` is a proposition
target at every universe `u`. For every field `k : Type u`, connected
reductive group schemes `G` and `H` over `k`, and a homomorphism `i : H ⟶ G`
that is a closed immersion and whose all-test range is normal, it asserts

```text
center H ≤ (center G).comap i.
```

Here `center` is the full scheme-theoretic centre functor: its points
commute with all points after every refinement of every test scheme.
`comap` is the inverse image under the actual homomorphism. In particular,
the target retains nonreduced test schemes and possibly nonsmooth centres.
It imposes no algebraic-closedness, perfectness or characteristic
restriction on the field, and contains no torus action or semigroup premise.

The target specializes Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), Proposition A.1.13, printed p.471 (PDF page 497,
zero-based index 496). The source proves, more generally, that the full
centre of a smooth normal closed subgroup of a smooth connected group is
central if that centre is of multiplicative type, and that this condition
holds when the ambient group is reductive. Our target additionally assumes
the subgroup connected reductive and asserts only this last consequence.
The source's argument uses the normality of the centre and the étaleness
of its automorphism functor to make conjugation by the connected ambient
group trivial. These structural steps are not proved in this module.

The source uses this precise containment in the normal-subgroup case of
Proposition 3.3.10(c), printed p.114 (PDF page 140, zero-based index 139),
when passing to full-centre adjoint quotients. This explains the target's
role in semigroup intersection comparison. Source identifier:
`conrad-gabber-prasad-2015-pseudo-reductive`.

The grouped theorem
`center_eq_comap_of_normalReductiveCenterStatement` assumes the global
target and proves the stronger equality for the same data. Its forward
inclusion is the supplied target. For the reverse inclusion, closedness
makes `i` a monomorphism and the published `center_comap_le_of_mono`
pulls ambient centrality back to the source. This proof uses no
algebraic-group structure theorem.

This module does not prove `NormalReductiveCenterStatement`, construct
adjoint quotients, or prove semigroup intersection comparison. The
equality theorem is conditional on the displayed structural target.
