# Common-compact radical normalization for nested constant terms

The outer parabolic is `p`, the inner parabolic in its Levi is `q`,
and the ambient lift is `r`. All groups in the comparison are the
actual rational-point subgroups. `intermediateRadicalHaar` assigns mass
one to the trace of the ambient compact on the copy of the inner
radical inside the literal outer Levi. `intermediateModulus` is the
Haar scaling character of the final Levi acting on that copy.

`sourceRadicalTransitivity` restricts the outer Levi projection to
the radical of `r`. The all-test radical product gives the required
semidirect decomposition. The special compact splits under this
projection, so product Haar in the semidirect coordinates agrees with
Haar of mass one on the compact trace. The ambient intersection and its
copy in the outer Levi are identified by their point inclusions, which
preserve that normalization. The conjugation characters multiply on
the final Levi by the semidirect Haar formula. Each element of the
intermediate radical belongs to the image under the Levi projection of
a compact subgroup of the lifted radical, so the outer modulus is
trivial there. `sourceRadicalConjugation` gives the scaling of the
outer radical Haar under the outer Levi.

`sourceConstantTermModelComparison` takes the compact on the outer Levi
model to be the trace of the ambient compact. The literal point maps
take the inner radical's compact trace to the intermediate radical's
compact trace. Haar uniqueness gives exact equality after transport.
The same maps intertwine conjugation, so the two inner modulus
characters agree at corresponding final-Levi points.

These comparisons use the Haar convention of Waldspurger, *La formule
de Plancherel pour les groupes p-adiques (d’après Harish-Chandra)*, I.1,
printed p. 240, and supply the radical data for the commutative diagram
in III.6, printed p. 272, used in the proof of VIII.2.1, printed p. 322.
