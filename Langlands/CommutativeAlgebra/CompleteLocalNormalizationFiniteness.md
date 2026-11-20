# Universal Japanese finiteness over a complete local ring

`CompleteLocalNormalizationFinitenessStatement` says that a Noetherian local
ring \(R\), adically complete for its maximal ideal, is universally Japanese in
the universe of \(R\). For each finite-type \(R\)-algebra \(S\) that is a domain
and each finite field extension \(L/\operatorname{Frac}(S)\), the integral
closure of \(S\) in \(L\) is a finite \(S\)-module. The scalar tower requires
that the \(S\)-algebra map into \(L\) is the composite through its fraction field.

This unfolds the conclusion in the complete local case of the Stacks Project,
Proposition 10.162.16. Lemma 10.162.8 supplies the Nagata property and
Proposition 10.162.15 passes to universal Japanese finiteness. Definitions
10.161.1 and 10.162.1 give the finiteness quantifiers. [Tags 0335](https://stacks.math.columbia.edu/tag/0335),
[032W](https://stacks.math.columbia.edu/tag/032W),
[0334](https://stacks.math.columbia.edu/tag/0334),
[032F](https://stacks.math.columbia.edu/tag/032F), and
[032R](https://stacks.math.columbia.edu/tag/032R).

The definition is an input to the affine reduced-fibre reduction. Unfolding
`IsUniversallyJapanese` and `IsN2` in the retained Weil Conjectures library at
commit `a25955cde4f85f67bef3149a6efc3efe20c22132` gives these same binders.
There `isUniversallyJapanese_of_isNagataRing` applied to
`isNagataRing_of_complete_local` supplies the result. [Weil Conjectures,
Nagata theory](https://github.com/formal-arithmetic-geometry/weil-conjectures/tree/a25955cde4f85f67bef3149a6efc3efe20c22132/WeilConjectures/RingTheory).
