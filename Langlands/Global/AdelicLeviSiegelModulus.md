# Siegel modulus on the norm-one subgroup of a standard Levi

`AdelicLeviSiegelModulusStatement` compares the ambient and Levi minimal Siegel
moduli for a represented standard Levi. The defining maximal split torus factors
through the Levi, and both moduli use the same cocharacter to define positivity.
The two positive torus coordinates have equal images in the maximal split torus.
If their value in the Levi lies in its norm-one subgroup, the moduli are equal.

The proof first expresses each modulus as the normalized adelic norm of the
sum of the positive weights with their Lie multiplicities. A standard
cocharacter for the Levi index partitions these ambient weights. Its zero
weights give exactly the Levi summand, by the differential identification of
centralizer weight spaces. The positive weights for the standard cocharacter
give the remaining summand. The standard sign property on positive roots and
root negation show that those weights occur on the positive side of the
ambient chamber. `characterRestrict_centralizerAdjointDeterminant` identifies
their sum with the restriction of the determinant of the Levi action on the
standard parabolic's unipotent radical. This rational character of the Levi
has normalized norm one on the specified subgroup.

The determinant normalization is that of Delorme's positive parabolic modulus.
The comparison uses that normalization in the restriction to a Levi as in the
proof of Lemma 3.10(i).

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, published PDF pp. 5–6 and 16.
