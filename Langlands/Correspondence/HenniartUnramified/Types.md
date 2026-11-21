# Inertia types and their Frobenius conjugates

For a split group `(G, D)`:

- `IsType A` says that a finite-dimensional complex representation `A` of `D.inertia`
  is continuous and irreducible.
- `TypeClass D` is the type of isomorphism classes of such representations, using the
  Library's `IsomorphismClassesWith`. `toClass` is the quotient map.
- `conjObj k A` is the type `A ∘ cj k` on the same carrier. It is again continuous
  (`cj k` is continuous) and irreducible (`cj k` is surjective).
- `conjType k` is the induced map on classes. It satisfies `conjType_zero`,
  `conjType_conjType` and `iterate_conjType`: the `d`th iterate of `conjType 1` is
  `conjType d`.

For local Weil groups these classes are the inertia types, with the action of
geometric Frobenius.

Let `A` be a type whose class has minimal period `m + 1` under `conjType 1`.

- `conj_dist_of_minimalPeriod`: for distinct `j, k < m + 1`, every intertwiner from
  `A ∘ cj j` to `A ∘ cj k` is zero. A nonzero one would be an equivalence, so the two
  iterates would agree below the minimal period.
- `conj_equiv_of_minimalPeriod`: `A ∘ cj (m + 1)` is equivalent to `A`.

These are the hypotheses needed to coinduce a type of exact period `m + 1` from the
stage of degree `m + 1`. This module is internal infrastructure for the proof of
Henniart (1988), Proposition 2.2.
