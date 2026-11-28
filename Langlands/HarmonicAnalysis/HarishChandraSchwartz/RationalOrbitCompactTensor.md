# The coefficient tensor on the fixed compact picture

The proof of Waldspurger V.1.1 evaluates the weak constant term on a coefficient tensor.
`rationalCompactCoefficientTensorEquiv` recovers that tensor from the fixed compact picture
at a specified unitary unramified character. It first extends the compact picture to the
product induction at the character and then applies the inducing compact's Haar-normalized
coefficient duality.

`rationalCompactCoefficientTensorEquiv_section` identifies the resulting tensor for a
section's `sectionCompactPicture` with its `rationalOrbitCoefficientTensor` at the same
character. The section restriction uses the literal representative at the torus
coordinates of the character. Inverting these coordinates recovers the character itself,
so the inverse compact-picture equivalence recovers the section's value.

Source. J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, IV.1 (printed pp. 276–278)
and the proof of V.1.1 (printed pp. 289–290), `waldspurger-2003-plancherel`.
