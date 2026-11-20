# Induced Schwartz character comparisons for VIII.2.2

`semistandardInducedSchwartzCharacter` is the trace of the finite-rank
Schwartz action of the normalized induction of a discrete series of the
literal Levi of any semistandard parabolic. The compact picture supplies
admissibility. The action uses the same ambient Haar, square-integrable
Schwartz weight and induced temperedness inputs as the actual Fourier
transform. VII.1.1(iii) multiplies this character by the inducing formal
degree when evaluating a Fourier coefficient.

`SemistandardInducedCharacterSymmetryStatement` gives the three character
identities in VIII.2.2. In the check identity the paired representation
is the smooth contragredient and the original argument uses left
translation by `g⁻¹`. In the conjugation identity the paired
representation has the conjugate complex scalar action. The identity
conjugates the character value and uses the pointwise conjugate of `f`
in the other character. In the twist identity the inducing series is
paired with its twist by `χ` restricted to the actual Levi, and the
original character is multiplied by `χ(g)`. The test uses the existing
Schwartz twist in the canonical coordinates of the ambient valuation
image. Its pointwise value is `f(g) * χ(g)`. In all three identities left
translation is `λ(g)h(x) = h(g⁻¹ * x)`.

The character identities are comparison targets. Reindexing the actual
orbits, comparing their normalized measures, formal degrees and densities,
and applying the identities to the weighted synthesis are separate
inputs to the operator comparisons. The field and representation-carrier
universes are independent. The ambient hypotheses permit arbitrary
characteristic and nonsplit connected reductive groups.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, Journal of the Institute of Mathematics of
Jussieu 2 (2003), III.7, VII.1.1(iii), and VIII.2.2 on printed p. 322.
[DOI](https://doi.org/10.1017/S1474748003000082)
