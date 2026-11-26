# Finiteness of rational σ-elliptic classes meeting a compact adelic set

`Langlands.TraceFormula.twistedEllipticClassFiniteness` proves
`TwistedEllipticClassFinitenessStatement.{u,v}` for number fields in
independent universes. Its finite set consists of rational σ-elliptic
elements with adelic twisted classes meeting the given compact set.
[Statement](TwistedEllipticClassFinitenessStatement.md)

## Lean proof

1. Arithmetic transport acts on the adele ring by \(\mathbb Z\)-algebra
   automorphisms, so the ordered product `cyclicNorm` applies to adelic
   matrix units. Its factors are continuous by `adelicEquiv` and commute
   with the rational diagonal map by `adelicEquiv_rational`. Since
   \(\sigma^l=1\), `cyclicNorm_twistedConj` identifies the norm of an
   adelic twisted conjugate with an ordinary adelic conjugate of the
   rational norm.
2. The characteristic coefficients below the leading term of the
   adelic norm form a continuous map into \(\mathbb A_L^n\). For each
   qualifying rational element, these coefficients belong to the image
   of the compact set and to the diagonal \(L^n\). The product of \(n\)
   copies of the principal adeles embeds as a closed discrete subspace,
   so only finitely many coefficient vectors occur.
3. `Set.exists_subset_image_finite_and` chooses a finite subset of the
   qualifying rational elements whose coefficient image contains
   every occurring vector. Injectivity of the rational diagonal map
   and monicity in degree \(n\) turn equality of adelic coefficient
   vectors into equality of rational norm characteristic polynomials.
4. σ-ellipticity gives a norm associate over \(K\) with separable
   characteristic polynomial. Separability persists upon base change
   to \(L\) and conjugation. `matrixConj_of_squarefree_charpoly_eq` thus
   gives a rational conjugation between the norms of each qualifying
   element and its chosen representative. The third clause of
   `cyclicNormLemma` gives the required rational σ-conjugation.

## Relation to the sources

Getz–Hahn use a compact image in an adelic quotient and closed
discreteness of the rational points in Lemma 17.7.11, printed pp. 461–462.
Lemma 18.2.6, printed pp. 479–480, treats geometric finiteness modulo the
split centre, and §18.5, printed pp. 486–488, applies the simple trace
formula to the twisted action. The Lean proof implements the compact
invariant argument on \(GL_n(\mathbb A_L)\) using the coefficients
of the norm. The registered source is
`getz-hahn-2024-automorphic-representations`.
[Getz–Hahn, *An Introduction to Automorphic Representations* (2024)](https://doi.org/10.1007/978-3-031-41153-3)

The final implication from rational conjugate norms to rational twisted
conjugacy is Henniart–Lemaire, I.2.2, Lemma (2), printed p. 12
(PDF p. 20). Section I.2.3, printed pp. 13–14, gives the
regular-semisimple and elliptic conventions for the norm associate. The
registered source is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
[Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non nulle* (2011)](https://numdam.org/item/MSMF_2011_2_124__1_0/)
