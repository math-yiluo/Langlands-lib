# Geometric solvable-radical existence for rational parabolics

Author: Worker 1355.

`ParabolicGeometricSolvableRadicalExistsStatement.{u}` is a proposition
target over every field `k : Type u`. Given an actual connected reductive
group scheme `G`, an actual group scheme `P`, and a morphism `j : P → G`
satisfying `IsParabolicSubgroup j`, it asserts the existence of an actual
group scheme `R` and morphism `r : R → P` satisfying the published predicate
`IsGeometricSolvableRadical r`.

The parabolic predicate includes closedness of `j`, smoothness of `P`, and
containment of a Borel after base change to the algebraic closure. The target
has no assumption that `k` is perfect, that `G` or `P` is split, or that a
maximal torus has been supplied. It asserts existence and makes no choice of
a representative.

## Meaning of the radical predicate

The imported definition in `Rational.LeviSubgroup` requires both
`IsSolvableRadical r` over `k` and `IsSolvableRadical` for the actual
base-changed morphism over `AlgebraicClosure k`. Each radical predicate
requires a closed embedding, a smooth connected source, solvability,
normality, and greatestness among all actual smooth connected solvable
normal closed subgroup morphisms into the same ambient group.

Solvability uses the existing `IsSolvableGroupScheme`: solvability of the
group of algebraic-closure points of the group after base change.
Normality and greatestness concern represented subgroup functors on
every relative test scheme. In particular, greatestness is an inclusion
of these subgroup functors, rather than just an inclusion of rational
points. For the algebraic-closure radical the same definitions are used
over that field, including its own algebraic-closure point convention.

## Source and derivation

The source is Armand Borel and Jacques Tits, *Groupes réductifs*,
Publications Mathématiques de l'IHÉS **27** (1965), pp. 55–150,
registered as `borel-tits-1965-groupes-reductifs`, content SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
The relevant passages are §0.3, printed pp. 57–58 (PDF pp. 4–5);
§0.7, printed p. 59 (PDF p. 6); Corollary 3.14 and its proof,
printed p. 80 (PDF p. 27); and §§4.1–4.3, printed pp. 85–86
(PDF pp. 32–33).

Section 0.3 permits the interpretation of linear algebraic groups as
affine geometrically reduced group schemes, and §0.7 defines the
geometric radical by its greatest connected solvable normal closed
subgroup property. The proof of Corollary 3.14 states that the radical
of a connected subgroup of maximum rank is defined over the ground
field, and identifies it as the product of the connected central torus
of a rational Levi with the unipotent radical. Sections 4.1–4.3 put
parabolics within this setting: a parabolic contains a Borel, the
standard parabolics contain the fixed maximal torus, and every
parabolic is connected and conjugate to a standard parabolic.

This target is the parabolic specialization of that descent assertion,
expressed through the existing scheme predicates. It is derived from
those passages, rather than a verbatim statement of Corollary 3.14.
Its eventual proof must implement the descent and identify the actual
represented subgroup, including smoothness and the full normality and
greatestness assertions over both fields. The literature does not
supply a Lean proof of these obligations.

## Relation to the consuming theorem

This is a proper prerequisite of
`ParabolicRadicalTorusLeviStatement`: it provides the geometric solvable
radical needed there. It does not assert the existence or maximality
of a torus in that radical, a radical intersection formula, or an
adapted rational Levi and its centralizer description. The consuming
statement and its imports are unchanged.

The file defines only a proposition target. It proves no existence
theorem, and it makes no assertion that the geometric radical of an
arbitrary smooth connected affine group descends over an imperfect
field.
