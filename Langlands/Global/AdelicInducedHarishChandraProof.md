# Uniform Harish-Chandra equations on the parabolic quotient

`Langlands.Global.inducedHarishChandraEquations` proves
`InducedHarishChandraEquationsStatement.{u}` on the given quotient
\(U(\mathbb A)M(F)\backslash G(\mathbb A)\) with the supplied maximal
Iwasawa compact. For each base parameter \(s_0\), the equation uses
finitely many smooth compactly supported kernels with finite left and
right \(K_\infty\)-translate spans. Its coefficients are entire in the
given coordinates, the scalar multiplying the twisted form is nonzero
at \(s_0\), and the identity holds at every parameter and adelic point.

The theorem `parabolicLeviCenterRestriction` gives the finite restriction
of enveloping centers and its differential identity on radical-invariant
functions. It uses the algebraic finiteness of the parabolic projection
and the grading of the actual archimedean tangent Lie algebras. The finite
restriction supplies arithmetic finiteness by
`arithmeticHarishChandraFiniteness_of_leviCenterRestriction`.
The reduction `parabolicHarishChandraFiniteness_of_arithmetic_and_center`
then gives finiteness on the parabolic quotient.

The proof uses `adelicSmoothIwasawaHeight` with the supplied compact to
obtain smooth height pairings on every infinite slice. At the identity
translate, the pullback in the center comparison is restriction along
the inclusion of the Levi points into the ambient infinite adelic group.
`adelicEnvelopingCenterConjugation` fixes the ambient center under the
adjoint action, so central differentiation commutes with right translation.
`hasUniformLeviCenterTransfer_of_identity` gives one Levi operator for
each ambient central element on every infinite Levi fibre.

The reduction `inducedHarishChandraEquations_of_parabolicCenter` fixes the
input's cofinite ambient center ideal, a finite adelic right level in the
supplied compact, and a finite space of archimedean compact coefficients. Parabolic
Harish-Chandra finiteness bounds the span of continuous automorphic
functions with those conditions. In the convolution transported through
the twist, the height ratio is constant in the Levi variable. Compact
integration commutes with the Levi derivatives, so the fibre identity
preserves annihilation by the original ambient ideal. Localization
preserves the right level, and averaging at infinity restores the compact
coefficients. This yields endomorphisms of one fixed finite-dimensional
space for all parameters.

A smooth approximate identity localized at the finite level, with the
two compact reproducing weights, supplies a kernel whose transported
operator is invertible at \(s_0\). Evaluation at fixed points shows that
the matrix entries are entire, so the characteristic polynomial has
entire coefficients. Its constant coefficient is nonzero at \(s_0\).
Cayley–Hamilton yields the pointwise equation with the positive
convolution powers as kernels and the negative constant coefficient as
the scalar. When the embedding has matrix size zero, the adelic group is
subsingleton and a normalized kernel acts as the identity.

The fixed finite space on the parabolic quotient uses the finiteness
argument of Mœglin–Waldspurger I.2.17, printed pp. 37–38. Their I.4.5,
printed pp. 60–62, applies the characteristic polynomial to the operator
on twisted cuspidal spaces after averaging the approximate identity on
both sides. The same operator argument underlies Bernstein–Lapid
Lemma 8.3, p. 223. Here the preserved ambient ideal gives a finite-dimensional
space on the quotient itself, and Cayley–Hamilton applies directly to the
twist of the input.
[Mœglin–Waldspurger (1995), I.2](https://doi.org/10.1017/CBO9780511470905.004),
[Mœglin–Waldspurger (1995), I.4](https://doi.org/10.1017/CBO9780511470905.006),
[Bernstein–Lapid (2024)](https://doi.org/10.1090/jams/1020).

The registered sources are `moeglin-waldspurger-1995-spectral-decomposition`,
collection fingerprint `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
and `bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
