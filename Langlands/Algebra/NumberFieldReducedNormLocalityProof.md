# Locality of reduced norms over number fields

`Langlands.CentralSimple.numberFieldReducedNormLocality` proves
`NumberFieldReducedNormLocalityStatement` in every universe. The
hypothesis is membership in the image of the reduced norm on units
after scalar extension to each completion of the number field. The
conclusion is membership in the corresponding image over the number
field itself.

At each nonsplit finite completion and each infinite completion,
`exists_norm_eq_with_separable_reducedCharpoly` gives a representative
of the prescribed norm with separable reduced characteristic
polynomial. All these polynomials are monic of the reduced degree
\(d\) and have constant coefficient given by the image of
\((-1)^d a\), where \(a\) is the prescribed norm. The polynomial
weak approximation theorem gives a monic global polynomial \(g\)
of degree \(d\) with this constant coefficient and coefficients in
the chosen local neighborhoods. Separability of its image at an
infinite completion gives separability of \(g\).

For each monic irreducible factor of \(g\), adjoin a root to obtain
a number field \(L\). If \(w\) is a place of \(L\) over \(v\), the
image of the adjoined root in \(L_w\) is a root of \(g\) over \(F_v\).
The neighborhood theorems give splitting over \(L_w\) at the specified
places. At the other finite places the splitting over \(F_v\) extends
to \(L_w\). The scalar extension tower equivalences identify both
of these local algebras with \(L_w \otimes_L (L \otimes_F A)\).
Brauer–Hasse–Noether gives splitting over \(L\).

The splitting over each factor field lets
`exists_reducedCharpoly_eq_of_split_factors` realize \(g\) as the
reduced characteristic polynomial of an element \(z\) of \(A\).
Comparing constant coefficients gives reduced norm \(a\) for
\(1 \otimes z\) in \(F \otimes_F A\). Since \(a\) is nonzero,
\(1 \otimes z\) gives a unit whose reduced norm is the prescribed
field unit.

## Sources

- Martin Kneser, *Lectures on Galois Cohomology of Classical Groups*,
  TIFR Lectures on Mathematics 47 (1969), §5.4, printed pp. 67–69
  (PDF pp. 73–75). Eichler's argument there uses coefficient
  approximation and splitting over the factor fields.
  Source `kneser-1969-galois-cohomology-classical-groups`, SHA-256
  `55309defa8ea7b311d5d6959832029ee6a0245330b7d0e45b2524e62283809a0`.
  [TIFR publication](https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr47.pdf)
- V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*
  (1994), §6.7, equation (6.39), printed p. 357 (PDF p. 367), and
  Theorem 1.13, printed p. 38 (PDF p. 48). The Lean statement is
  the local-to-global direction of (6.39).
  Source `platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256
  `c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`.
