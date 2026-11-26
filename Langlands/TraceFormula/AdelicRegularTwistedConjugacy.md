# Regular cyclic norm fibres on adelic matrix groups

`adelic_twistedConjugate_iff_cyclicNorm_charpoly` identifies the twisted conjugacy class of a
rational matrix with regular cyclic norm with the fibre of the characteristic polynomial of
its norm in `AdelicGL L n`. The forward implication uses telescoping of the ordered norm and
invariance of the characteristic polynomial under conjugation.

For the reverse implication, use `numberFieldAdeleTensorEquiv` to identify the matrix
coefficients with `Adeles K ⊗[K] L`. This comparison intertwines the entrywise twist with the
action on the second tensor factor. Modulo any maximal ideal of `Adeles K`, the coefficient
algebra over the residue field is cyclic of degree `l` by `cyclicAlgebraBaseChange`. It is
finite and reduced. In its field factors the two cyclic norms are conjugate, since their
characteristic polynomials agree and are separable. `cyclicNormLemma` gives a twisted
conjugator over the whole reduced algebra.

A cyclic basis for the rational norm extends to the tensor algebra. The lifting lemma
`exists_cyclicIntertwiner_lift` gives an exact intertwining matrix whose reduction is the
invertible conjugator multiplied by `l`. The degree is a unit in each specialization because
it comes from the characteristic-zero base field. The determinant's tensor norm for this
lift therefore avoids the chosen maximal ideal. All such norms generate the unit ideal,
and a finite subfamily already generates it. `exists_adele_idempotent_patch` gives a partition
of unity to patch the corresponding matrix intertwiners. In each maximal-ideal residue field
exactly one idempotent is one, so the determinant norm of the patched matrix agrees there
with the norm selected by the partition. The patched determinant norm is a unit, which
makes the matrix invertible by the multiplication-matrix definition of the tensor norm.

Continuity of the cyclic norm and the characteristic coefficients makes the fibre closed.
`isClosed_range_adelic_normOne_twistedConj` uses the same orbit for conjugators of determinant
norm one when `n > 0`. Right multiplication of any conjugator by a twist-fixed positive
scalar preserves twisted conjugation and can correct the determinant norm.

The residue-field step uses the algebraic norm and conjugacy argument of
Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), Chapter 1, §1, Lemma 1.1, pp. 3–4, in its cyclic-algebra form. Its adelic extension is
the idempotent argument above. The positive scalar normalization is the matrix case of Getz
and Hahn (2024), §2.6, equations (2.19)–(2.22) and Lemma 2.6.2, pp. 68–69.
