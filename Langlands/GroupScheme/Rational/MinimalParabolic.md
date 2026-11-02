# Minimal rational parabolic subgroups and their functors of points

Author: Worker 1262.

This module defines minimality among parabolic subgroups over the ground field.
It uses the existing geometric `IsParabolicSubgroup`; it makes no identification
with dynamic subgroups and proves no structural existence or conjugacy theorem.

The source is Borel and Tits, *Groupes réductifs* (1965), source ID
`borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`,
4.13(b), printed p.90 (PDF p.37), and 4.16, printed pp.91–92 (PDF pp.38–39).
In 4.13(b), minimal means minimal among the parabolic subgroups defined over
the ground field. In 4.16 the same minimality is characterized by the maximal
split tori in the radical.

For a field `k : Type u`, write `S = Spec (CommRingCat.of k)` and let
`G : GroupScheme S`. A subgroup functor has a subgroup of `G(U)` for every
scheme `U` over `S`. The existing order on subgroup functors tests inclusion
on every such `U`. The existing `SubgroupFunctor.range j` consists of points
that factor through `j`, on every test scheme.

`IsParabolicFunctor F` says that some actual parabolic subgroup `j : P ⟶ G`
has all-test range `F`. `IsMinimalParabolicFunctor F` says that `F` is
parabolic and that every parabolic functor contained in `F` equals `F`.

`IsMinimalParabolicSubgroup j` requires that `j` itself is parabolic, and that
any actual parabolic subgroup whose all-test range is contained in the range
of `j` has that same range. Requiring `j` itself to be parabolic retains the
published closed-immersion and smoothness conditions. This is a derived
functor-of-points formulation of the source's subgroup minimality: all-test
inclusion records scheme-theoretic subgroup inclusion, including over finite
fields. It does not define minimality using only `G(k)`.

The lemmas unpack these definitions. A minimal actual subgroup gives a
minimal functor; conversely a minimal functor has a representative that is a
minimal actual subgroup. The latter assertion extracts the representative
already required by `IsParabolicFunctor`; it does not assert that a
parabolic or a minimal parabolic exists in an arbitrary group. Two minimal
parabolic functors related by inclusion are equal.
