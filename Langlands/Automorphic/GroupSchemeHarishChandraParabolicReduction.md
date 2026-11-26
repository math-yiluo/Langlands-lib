# Parabolic Harish-Chandra finiteness from arithmetic finiteness and a center map

`parabolicHarishChandraFiniteness_of_arithmetic_and_center` proves
`ParabolicHarishChandraFinitenessReductionStatement`. Given
`ArithmeticHarishChandraFinitenessStatement` and
`ParabolicLeviCenterRestrictionStatement`, its conclusion is the published
`ParabolicHarishChandraFinitenessStatement` at universe `u`.

The theorem first uses `rationalHarishChandraFiniteness_of_arithmetic` to
obtain the finiteness bound on the full adelic rational quotient of each
connected reductive Levi. It then applies the finite sampling theorem
`finiteDimensional_span_of_leviRestrictions`. For a finite translate \(b\)
and an infinite compact translate \(a\), it places the Levi restrictions in
one fixed space of rational automorphic functions on the Levi.

- Rational Levi invariance comes from the definition of the ambient
  parabolic quotient subgroup. The finite level is the inverse image of
  \(L\) under the Levi inclusion followed by conjugation by \(b^{-1}\).
  Continuity of this map proves openness.
- The restriction is continuous. Its archimedean slice at \(c\) is the
  translated smooth pullback of the ambient slice at \(l(c)b\). Moderate
  growth follows from the ambient estimate at the fixed right translate and
  the equality of the matrix heights for the restricted representation.
- The Levi maximal compact \(H\) and radical point \(v\) come from
  `exists_leviCompact_conj_by_radical`. For \(h\in H\), replace the embedded
  \(h\) by \(v h v^{-1}\) inside the original compact. The difference in
  the two evaluation points is a left radical factor, since the Levi
  normalizes the radical. The Levi profiles thus lie in the linear image
  of the original space \(E\) by pullback along
  \(h\mapsto a^{-1} v h v^{-1} a\).
- The finite center comparison at \(a\) extends the ideal to a cofinite
  Levi ideal by `exists_cofinite_center_ideal_of_leviRestriction`. The
  ambient slices are left invariant under the archimedean radical, so the
  extended ideal annihilates the actual Levi slices. It is the same ideal
  for every ambient function and Levi finite point at these translates.

The rational finiteness bound applies with this Levi level, compact profile
space and ideal. The sampling theorem recovers the original functions from
finitely many such restriction spaces and proves the required dimension
bound. The two finiteness and center comparison propositions are premises of
this implication.

This is the reduction by Levi restriction of Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.2.17, printed
pp. 37–38, PDF pp. 20–21. It uses the unnormalized convention and the finite
arithmetic slice reduction of Borel–Jacquet §4.3. The retained originals are
`moeglin-waldspurger-1995-growth-and-constant-terms`, SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`, and
`borel-jacquet-1979-automorphic`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`, printed
p. 195, PDF p. 190.
