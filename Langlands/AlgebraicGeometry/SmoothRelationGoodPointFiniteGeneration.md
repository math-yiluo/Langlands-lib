# Finite maximal-ideal generators modulo the base prime

This internal module supplies the finiteness input of the good-point
cotangent converse. Let `B` be a local `A`-algebra, let `m` be its maximal
ideal and let `p` be the contraction of `m` to `A`. Assume
`Algebra.EssFiniteType A B` and `IsRationalPoint A B`, using the rationality
predicate from `SmoothRelationGoodPointCotangent`. The two rings have
independent universe levels.

The lemma `exists_finite_maximalIdeal_generators` proves that there is a
finitely generated ideal `N` of `B` such that `N ≤ m` and
`m ≤ p.map (algebraMap A B) ⊔ N`. It does not require `A` to be Noetherian.

The proof uses Mathlib's `Algebra.essFiniteType_iff` to choose a finite set
`s` in `B` such that every element becomes an element of `A[s]` after
multiplication by a unit of `B` lying in `A[s]`. For each `b` in `s`,
rationality supplies a constant `c(b)` congruent to `b` modulo `m`. Here a
constant is a fraction of images of elements of `A`, with unit denominator.
Let `N` be the ideal spanned by the finite set of differences `b - c(b)`.
Every generator lies in `m`, so `N ≤ m`.

Induction on the generated subalgebra shows that every element of `A[s]`
is congruent modulo `N` to a constant. Constants are closed under addition
and multiplication, and the corresponding differences remain in `N`.
For `z` in `m`, choose a unit `t` as above. Write `z * t` as a constant
plus an element of `N`. The constant also lies in `m`, so the imported
lemma `IsConst.mem_map` puts it in the extended prime `pB`. Thus
`z * t` belongs to `pB + N`, and the unit property of `t` gives the same
membership for `z`.

The corollary
`maximalIdeal_eq_of_cotangentSpan_eq_top_of_essFiniteType` supplies this
finiteness result to the imported cotangent converse. For a second ring map
`θ : A →+* B` with the same contraction of `m`, rationality and the condition
`cotangentSpan θ = ⊤` imply `m = pB + p.map θ`. The extended ideal `pB`
uses the given `A`-algebra structure, whereas the second ideal uses `θ`.

`FiniteMaximalIdealData A B` records an actual ideal `N` with these three
properties. The definition `finiteMaximalIdealData` chooses such data
from the proved existence lemma. This is an algebraic prerequisite; it
does not assert the existence of a geometric good point or an etale slice.

The construction is internal to the good-point proof route supplied by
Worker 303. Worker 101 implemented the finite-generator argument using
the pinned Mathlib essential-finiteness and generated-subalgebra
interfaces and the imported, proved constant-representative lemmas.
