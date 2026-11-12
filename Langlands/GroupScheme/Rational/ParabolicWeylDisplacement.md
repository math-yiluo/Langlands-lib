# Dominant Weyl displacements in the actual parabolic root cone

Author: Worker 135. This module constructs the full real character displacement
`relativeWeylDisplacement w`, the linear map `x -> x - w x` for the actual
relative Weyl quotient `N(k)/Z(k)`. It proves that the restriction of every
such displacement of a dominant character belongs to the nonnegative cone of
an actual compatible parabolic root presentation. It also proves that the
defining functional is strictly positive on every nonzero vector in that cone.
These are intermediate inputs to Task 5282; opposite regularity is not proved.

## Objects and hypotheses

The field `k : Type u` is arbitrary. `relativeWeylDisplacement` acts on the
full published real character space `RealTorusSpace.Vstar T`, with its central
directions retained. No choice of a complementary root subspace is made.
`RelativeRootReflectionData.fullRealAction_representative` extends the supplied
integral formula of `D` to this entire real space. The corresponding actual
quotient element is a relative reflection, as proved by
`isRelativeReflection_representative` using finiteness of the actual roots and
a supplied split torus.

For a compatible presentation `r` of specified maps `P -> G`, `M -> P`, and
`A -> M`, the theorem
`ParabolicRootPresentation.restrict_displacement_mem_nonnegCone` assumes that
`G` is connected reductive and that `x : Vstar r.data.T` pairs nonnegatively
with `D`'s coroot of every simple relative root. For every actual quotient
class `w`, it proves

```
rationalCharacterRestrictReal (groupHom r.data.f) (x - w x) in r.nonnegCone.
```

The representation-theoretic hypotheses of a Langlands triplet are unnecessary
for this bound. Local finite type is an explicit ambient instance in the
parabolic section. The variant ending in `_of_coxeter` retains a supplied
finite quotient and Coxeter realization. The connected reductive version
discharges those inputs with the published proof `relativeWeylCoxeter`.
Neither theorem assumes a supplied displacement bound, root-sign law or
reflection formula beyond the published `D` data in the Langlands target.

## Implemented proof

The full real reflection formula is an equality of linear maps, checked on
pure tensors. The representative's reflection on the rational root span is
then identified with the actual simple generator by the published uniqueness
argument for finite Coxeter realizations. Thus its full real action uses the
same integral coroot that appears in the dominance assumption.

Strong induction on Coxeter length writes a nonidentity `w` as `v s_a` with
`length v < length w`. The displacement decomposes as

```
x - v s_a x = (x - v x) + <x, a^vee> * v a.
```

The actual root-sign length law makes `v a` a positive relative root. The
published `one_tmul_restrict_mem_nonnegCone` places its restriction in the
actual parabolic cone. Its coefficient is nonnegative by dominance; cone
closure under nonnegative scaling and addition completes the induction.

For `splitComponentEvaluation_eq_zero_iff_of_mem_nonnegCone`, write a vector
as the published finite nonnegative combination of restricted simple roots.
Every restricted root has strictly positive defining evaluation. A zero sum
of the nonnegative evaluated terms forces every coefficient to vanish.
`splitComponentEvaluation_pos_of_mem_nonnegCone` follows, including when the
root set is empty (then there is no nonzero vector in the cone).
`add_ne_zero_of_mem_nonnegCone` uses this functional to show that a cone
vector cannot cancel a nonzero cone vector.

## Source and scope

David Renard, *Representations des groupes reductifs p-adiques*, French version
of 9 July 2026, literature ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 135 read the Lemma and proof of VII.4.1, printed pp.241--242 / PDF
pp.247--248. Equation (VII.4.1.3) is the dominant Weyl displacement bound;
the paragraph following it restricts the bound to the Levi split component.
The final cone addition motivates the noncancellation lemma. This module is
a derived formulation of those steps. Its length induction uses the displayed
reflection decomposition above and does not use the book's dual-basis
coordinate calculation.

Strict displacement for a Weyl double coset outside the Levi, the comparison
with actual twisted Jacquet exponents and the geometric-lemma pieces, and the
opposite identity-support equivalence are still required for the main task.
No strictness assertion for a nonidentity quotient class is made here:
a nonidentity element of the Levi Weyl subgroup can have zero restriction.
