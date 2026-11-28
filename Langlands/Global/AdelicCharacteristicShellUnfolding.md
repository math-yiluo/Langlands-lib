# Unfolding a characteristic shell

The actual characteristic shell is the image in \(G(F)\backslash
G(\mathbb A)^1\) of the product of the compact unipotent factor, the
minimal Levi points whose heights lie in \(C^Q_{T+S,T}\), and the
Iwasawa compact subgroup. `characteristicShellLift` takes the same image
in \(Q(F)\backslash G(\mathbb A)^1\).

The smaller rational subgroup consists of the norm-one points whose
underlying adelic points are in the rational parabolic image.
Consequently a minimal-parabolic rational translation leaves the
class in the parabolic quotient unchanged. The proof uses such a
translation to put each representative in the common Siegel set,
where the rational separation theorem applies. For sufficiently
regular \(T\), a rational identification between two representatives
of the same shell is in \(Q(F)\), which gives injectivity. The root
threshold works for all parabolics and increments.

Every real linear functional of the minimal height is continuous.
On the minimal Levi, the norm-one condition, coroot-span condition,
and weak inequalities are closed. The finitely many strict root
inequalities give an open set, which has a countable compact cover.
Intersecting with the closed constraints, multiplying by the two
compact factors and passing to the parabolic quotient gives a
countable union of compact sets. The quotient is Hausdorff because
the rational subgroup is discrete and closed.

`characteristicShellUnfolding` then applies the exact counting
normalization for an injective restriction of discrete quotients.
The projection is measure preserving on the shell for the restricted
quotient measures formed from the same left-invariant measure.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 23–24 and 26–27,
(7.6), (7.7), (7.13), and (7.20).
