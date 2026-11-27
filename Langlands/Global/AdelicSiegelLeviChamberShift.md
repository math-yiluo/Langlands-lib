# Complementary simple-root coordinates in a Siegel chamber

`AdelicSiegelLeviChamberShiftStatement` fixes a compatible standard family, its ambient
Siegel torus and a standard Levi index `J`. Every point `a` of the intrinsic positive
Siegel torus admits a correction `s` whose ambient value equals that of a positive
split-component point `b` of `J`. At `s * a` the simple-root logarithms indexed by `J`
are unchanged. Every complementary simple-root logarithm is in `[0, B]` for one
bound `B` independent of `a`.

The proof uses `exists_siegelFundamentalRays`. The ray for an omitted root has positive
logarithmic step at that root and zero logarithmic step at the other simple roots.
The finite product defining `s` uses each omitted ray to the negative floor of the
original root logarithm divided by the step. The logarithmic character turns this
product into a sum. At an omitted root only its own summand contributes, and the
floor inequalities put the resulting logarithm below the ray step. The sum of the
omitted steps is a uniform bound, including when the set of omitted roots is empty.
Each omitted ray has its image in the split component of `J`, and membership is
preserved under the integer powers and the finite product.

This is a coordinate argument for comparing an ambient chamber estimate with its
restriction to the Levi, as used in the Levi reduction of Delorme's Lemma 3.10(i).
The split-component translation is useful there because the ordinary eigencharacter
accounts for its effect on a form.

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, published PDF pp. 14 and 16, Lemma 3.8(iv) and the proof of Lemma 3.10(i).
