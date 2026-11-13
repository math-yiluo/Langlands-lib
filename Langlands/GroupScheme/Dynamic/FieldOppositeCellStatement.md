# Statement: the opposite dynamic open cell over a field without smoothness

Worker 3483.

`Langlands.GroupScheme.DynamicFieldOppositeCellStatement.{u} : Prop` is a
statement-only proposition definition. This module supplies no proof and
introduces no axiom.

## Quantifiers and conclusion

For every field `k : Type u`, put `S = Spec (CommRingCat.of k)`. The
proposition quantifies over an actual group scheme `G : GroupScheme S` with
affine and locally finite-type structure morphism, a cocharacter
`χ : (Gm S).toGrp ⟶ G`, group schemes `U` and `P` over `S`, and homomorphisms
`iU : U ⟶ G` and `iP : P ⟶ G`.

If `iU` represents `Dynamic.unipotent (-χ)` and `iP` represents
`Dynamic.parabolic χ`, then the scheme morphism underlying
`SubgroupFunctor.cellMultiplication iU iP : U.X ⊗ P.X ⟶ G.X` is an open
immersion. The product is the fibre product over `S`, and multiplication is
ordered `(u, p) ↦ iU(u) iP(p)`. Inversion of the cocharacter means
precomposition with `Gm.powerHom S (-1)`, rather than inversion in the
possibly noncommutative target.

`SubgroupFunctor.IsRepresentedBy` requires a monomorphism together with
equality of its range and the specified subgroup functor on every test
scheme over `S`, including nonreduced tests. The dynamic subgroups use the
actual conjugation orbit on `G_m`: `P` means extension to the affine line,
and `U` further requires identity value at zero. Representative existence
is not asserted.

No smoothness, geometric reducedness, connectedness, reductivity,
perfectness or algebraic closedness is assumed. The trivial cocharacter is
included. Affineness makes the structure morphism quasi-compact, so local
finite type gives finite type.

## Original source and derivation

Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*,
second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, file
`Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Proposition 2.1.8(3), printed p.53, PDF p.79, states the open immersion
over a field under the proposition's affine finite-presentation hypothesis.
Its separate extension to rings assumes smoothness. The field assertion
does not.

Over a field, finite type implies finite presentation. Thus affine local
finite type supplies the source's finiteness hypothesis. The source uses
the actual dynamic subgroup schemes. The present proposition permits
arbitrary supplied representatives: monomorphism and equality of ranges
on all tests identify them uniquely over `G` with those subgroup schemes
by Yoneda. Their ordered multiplication therefore differs from the source
map only by a source isomorphism, preserving the open-immersion property.
This is the reason for the derived provenance.

This target isolates the first open-immersion assertion of part (3). It
does not assert the subsequent intersection identity with an ambient
group.

## Relation to existing targets

The published field target `Langlands.GroupScheme.OppositeCellStatement`
in [`Absolute.OppositeCellStatement`](../Absolute/OppositeCellStatement.md)
assumes smoothness. Its published proof uses that hypothesis only to obtain
local finite type for a closed linear embedding. The present target
retains finite type directly and permits groups without smoothness.
The original statement and proof remain useful and are retained.

[`DynamicBaseOppositeCellStatement`](BaseOppositeCellStatement.md) permits
an arbitrary base scheme and assumes smoothness. The present field target
does not remove smoothness from that arbitrary-base assertion. In
particular, it makes no claim about an open cell for a group without
smoothness over a general ring.
