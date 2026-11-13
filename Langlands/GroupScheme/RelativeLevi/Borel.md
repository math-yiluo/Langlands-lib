# Borel subgroups and quasi-split reductive group schemes over a base scheme

Author: Worker 75.

This module supplies two predicates for group schemes over an arbitrary base scheme
`S`. They are the relative counterparts of the existing ground-field predicates
`IsGeometricBorelSubgroup` and `IsQuasiSplit`
([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)). The module only defines these
predicates. It does not construct a Borel subgroup, and it asserts no existence,
conjugacy, openness or representability theorem.

## Borel subgroups

`IsRelativeBorelSubgroup i`, for a homomorphism `i : B ⟶ G` of group schemes over `S`,
has two fields:

- `isRelativeParabolicSubgroup : IsRelativeParabolicSubgroup i`
  ([`RelativeLevi.Basic`](Basic.md)): `B` is smooth and affine over `S`, `i` is a
  monomorphism of `S`-schemes, and every residue fibre of `i` is a parabolic subgroup;
- `residueFiber`: for every point `s` of `S`, the residue fibre
  `RelativeLevi.residueFiberHom i s : B_s ⟶ G_s`, the base change of `i` along
  `Spec κ(s) ⟶ S`, satisfies `IsGeometricBorelSubgroup`.

Over a field `k`, `IsGeometricBorelSubgroup j` says two things. First, `j` satisfies
the field predicate `IsBorelSubgroup`: it is a closed subgroup with smooth, connected
and solvable source that is maximal among such subgroups over `k`. Second, the base
change of `j` to the algebraic closure of `k` also satisfies `IsBorelSubgroup`.

The second field implies the residue-fibre condition contained in the first field,
because the existing theorem `IsGeometricBorelSubgroup.isParabolicSubgroup` shows that
a geometric Borel subgroup is parabolic. The predicate repeats that condition so that
it reads exactly as the source: a parabolic subgroup whose fibres are Borel subgroups.

## Quasi-split reductive group schemes

`IsRelativeQuasiSplit G`, for a group scheme `G` over `S`, has two fields:

- `isReductive : IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md));
- `exists_isRelativeBorelSubgroup`: there are a group scheme `B` over `S` and a
  homomorphism `i : B ⟶ G` with `IsRelativeBorelSubgroup i`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers
are the one-based PDF pages, which agree with the printed page numbers.

Definition 5.2.10, p.157: "A Borel subgroup of a reductive group scheme G → S is a
parabolic subgroup P ⊂ G such that P_s is a Borel subgroup of G_s for all s ∈ S. A
reductive group G → S is quasi-split over S if it admits a Borel subgroup scheme over
S." The parenthetical remark after it notes that SGA3 (XXIV, 3.9) uses a stronger
relative notion of quasi-split, and that the two agree over semi-local bases. This
module transcribes Conrad's definition, not the SGA3 one.

## Formalization choices

1. **Borel subgroups of fibres.** The residue field `κ(s)` need not be algebraically
   closed. In this setting Conrad uses "Borel subgroup" (also "Borel `k`-subgroup")
   for a `k`-subgroup whose base change to an algebraic closure `k̄` is a Borel
   subgroup in the classical sense. Two places in the source show this. Exercise
   5.5.1(iii), pp.181–182, speaks of Borel `k`-subgroups of a group over a field and
   checks parabolicity of `k`-subgroups after base change to `k̄`. The proof of
   Corollary 5.2.14, p.159, obtains a Borel subgroup of the special fibre from
   [Bo91, 16.6] and lifts it as a point of `Bor_{G/R}`, whose geometric fibres
   parametrize the classical Borel subgroups (Theorem 5.2.11(3), p.158). The field
   predicate `IsBorelSubgroup` alone only asks for maximality among subgroups defined
   over `κ(s)`. For example, in the anisotropic real group `SO(3)` a maximal torus is
   maximal among smooth connected solvable `ℝ`-subgroups, but it is not a Borel
   subgroup over `ℂ`. The predicate therefore uses
   `IsGeometricBorelSubgroup`, the condition the Library already uses for field-level
   quasi-splitness in `IsQuasiSplit`. Its first conjunct, maximality over `κ(s)`,
   follows from the second, because closed subgroups of `G_s` that agree over `k̄`
   are equal.
2. **Fibres over residue fields.** "For all s ∈ S" is read with `P_s` the fibre over
   `Spec κ(s)`, as in `IsRelativeParabolicSubgroup`. Because Borelness of a fibre is
   detected after base change to an algebraic closure, using residue fibres instead
   of geometric fibres changes nothing.
3. **Reductivity.** The source defines Borel subgroups only for reductive `G`.
   `IsRelativeBorelSubgroup` places no condition on `G`, as with
   `IsRelativeParabolicSubgroup`, and statements should assume `IsReductive G`
   separately. `IsRelativeQuasiSplit` includes `IsReductive G` because the source
   defines quasi-splitness only for reductive group schemes. The field-level
   `IsQuasiSplit` likewise includes `IsConnectedReductive`.

## Relation to the Library

- Over a field, Conrad's definition makes quasi-splitness agree with the classical
  notion that the Library records as `IsQuasiSplit`. This module does not prove that
  `IsRelativeQuasiSplit` over `Spec k` agrees with `IsQuasiSplit`.
- The field-level predicates `IsBorelSubgroup` and `IsParabolicSubgroup`
  ([`Absolute.Borel`](../Absolute/Borel.md)) and `IsGeometricBorelSubgroup` are used
  unchanged on residue fibres.
