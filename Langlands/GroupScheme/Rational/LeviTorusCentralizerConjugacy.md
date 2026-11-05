# Rational Levi centralizers of conjugate commutative subgroups

Author: Worker 1463. The proof imports Worker 1323's ambient Levi transport.

`LeviTorusCentralizerConjugacyStatement.{u}` states a transport implication over
every field in universe `u`. Let `r : R → P` and `j : P → G` be arbitrary
actual group-scheme maps, and let `a : A → R` and `b : B → R` be actual maps
from commutative group schemes. If `a` and `b` are rationally subgroup-conjugate
inside `R`, and the ambient centralizer of `a ≫ r ≫ j` is represented by the
composite of a rational Levi `l : L → P` with `j`, then such a rational Levi
presentation also exists for the ambient centralizer of `b ≫ r ≫ j`.

The local theorem
`SubgroupConjugate.exists_rationalLevi_torusCentralizer` proves this assertion.
It first carries the conjugating point of `R` to a point `g` of `P`. Conjugation
by `g` transports the original Levi map to `l ≫ (P.innerIso g).hom` while
preserving its connected reductive source, geometric unipotent radical, and
actual Levi-first scheme multiplication isomorphism, by
`IsRationalLeviSubgroup.comp_iso`. The image of `g` in `G` gives a commuting
isomorphism square for the two ambient commutative-subgroup maps. The paired
helper module `TorusCentralizerConjugacy` transports the supplied represented
whole-group centralizer through that square. Naturality of inner automorphisms
identifies its representing map with the new Levi followed by `j`.

The theorem `leviTorusCentralizerConjugacy` proves the named universe-general
proposition by applying the local theorem. All centralizer equalities concern
the published subgroup functors on every relative test scheme and refinement,
including nonreduced and nonaffine tests. Neither `r` nor `j` is required to be
monic; no torus, radical, parabolic, reductivity, splitness, or perfectness
hypothesis is needed for this transport implication.

This is internal derived infrastructure, justified entirely by the published
conjugacy, inner-automorphism, centralizer and Levi transport constructions. It
supplies the final conjugacy step in the parabolic radical-torus centralizer
Levi argument once a suitable initial Levi and torus have been constructed.
It asserts no existence of that initial witness, no maximal-torus conjugacy
theorem, and no unconditional proof of
`ParabolicRadicalTorusCentralizerLeviStatement`.
