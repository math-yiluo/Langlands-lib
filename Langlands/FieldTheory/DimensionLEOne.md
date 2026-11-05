# The norm criterion for fields of dimension at most one

Author: Worker 1673.

`Langlands.FieldTheory.HasDimensionLEOne K` is the finite-separable norm
criterion for field-theoretic dimension at most one. It is a proposition
definition; this module proves no dimension bound.

For every finite separable extension `E/K` and every finite Galois extension
`L/E`, it requires surjectivity of the actual multiplicative norm
`Lˣ → Eˣ`. The map is `Units.map (Algebra.norm E : L →* E)`.
Mathlib defines `Algebra.norm` as the determinant of multiplication. The
finite-dimensional hypotheses ensure that the norms here are the ordinary
finite-extension norms. The two algebras specify the two extensions;
the predicate does not need a separate `K`-algebra structure on `L`.
All three fields lie in the arbitrary universe `u`, with no restriction on
their characteristic or perfectness.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Section 2.3, printed pp.78–79 (PDF pp.109–110), source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Condition (3) is surjectivity of norms for finite Galois extensions of
algebraic extensions of the base. The following sentence says it suffices
to test finite separable extensions of the base; this definition uses that
criterion directly. It does not formalize the equivalence with Brauer-group
vanishing or with the characteristic-sensitive cohomological criterion.
In particular, it is not defined to be the bare cohomological dimension
bound, which would omit the source's extra condition in positive
characteristic. It is also unrelated to the Krull dimension of the ring `K`.

The authors' official corrections, version of 1 November 2024, Chapter 2,
PDF pp.24–25, source `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
do not change Section 2.3. The later Section 2.6 additions of Henselian and
perfect-residue hypotheses do not alter this arbitrary-field definition.

This predicate is intended to connect the Henselian discrete-field
dimension bound of Corollary 2.3.7 to the connected reductive quasi-splitness
conclusion of Theorem 2.3.3(2). Neither implication is proved here.
