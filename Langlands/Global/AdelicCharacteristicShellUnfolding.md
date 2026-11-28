# Unfolding a characteristic shell

Fix a standard parabolic \(Q\) for the chosen generic cocharacter.
Use compact factors with the same minimal-parabolic Iwasawa compact \(K\)
and with both rational covers in (7.1). Thus the minimal unipotent and
the intrinsic norm-one minimal Levi are covered by left rational translates
of their respective compact factors. The actual characteristic shell is the
image in \(G(F)\backslash G(\mathbb A)^1\) of the compact unipotent factor, the
minimal Levi points whose heights lie in \(C^Q_{T+S,T}\), and the
Iwasawa compact subgroup. `characteristicShellLift` takes the same image
in \(Q(F)\backslash G(\mathbb A)^1\). The unipotent rational cover and
\(N_0(F)\subset Q(F)\) identify these quotient images with those using
the full minimal unipotent as in (7.13).

The smaller rational subgroup consists of the norm-one points whose
underlying adelic points are in the rational parabolic image.
Consequently a minimal-parabolic rational translation leaves the
class in the parabolic quotient unchanged. The proof uses such a
translation, using the two rational covers and the shared \(K\), to put
each representative in the common Siegel set,
where the rational separation theorem applies. For sufficiently
regular \(T\), a rational identification between two representatives
of the same shell is in \(Q(F)\), which gives injectivity. The root
threshold works for all standard parabolics and increments.

Every real linear functional of the minimal height is continuous.
On the minimal Levi, the norm-one condition, coroot-span condition,
and weak inequalities are closed. The finitely many strict root
inequalities give an open set, which has a countable compact cover.
Intersecting with the closed constraints, multiplying by the two
compact factors and passing to the parabolic quotient gives a
countable union of compact sets. The quotient is Hausdorff because
the rational subgroup is discrete and closed.

Under these hypotheses, `characteristicShellUnfolding` applies the exact
counting normalization for an injective restriction of discrete quotients.
`CharacteristicShellUnfoldingStatement` gives the resulting measure
preservation for the restricted quotient measures formed from the same
left-invariant measure.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 22–24 and 26–27,
(7.1), (7.6), (7.7), (7.13), and (7.20).
