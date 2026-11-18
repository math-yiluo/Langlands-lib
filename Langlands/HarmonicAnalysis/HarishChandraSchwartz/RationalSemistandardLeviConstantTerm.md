# The actual Levi Schwartz function and its transitivity formula

In III.6, Waldspurger takes the induced constant term of a Schwartz
function at \((g_1,g_2)\) as a Schwartz function on the Levi. In the
reverse direction of VIII.2.1 that function is \(f^M\). The proof
passes its inner induced constant terms through the III.6 diagram.
[Waldspurger, *La formule de Plancherel pour les groupes p-adiques*
(2003), pp. 272, 321–322](https://doi.org/10.1017/S1474748003000082)

`rationalSemistandardLeviConstantTerm` constructs \(f^M\) under the
existing constant-term estimates and translation weights. It uses
`Space.constantTermInd` on the actual subgroup and
`Space.comapLinear` along the canonical
`RationalSemistandard.LeviModel.pointHomeomorph` to the Levi scheme.
The Xi and height comparisons for this pullback are explicit. The
matrix model on the Levi is the restriction of the ambient matrix
model. Its height restricts the ambient height, and its
closedness follows from closedness of the ambient model. The
pointwise formula gives the literal normalized integral. The
vanishing equivalence uses surjectivity of the Levi homeomorphism.

For a semistandard index `q` on the Levi scheme and an ambient
index `r`, `RationalSemistandardConstantTermModelComparison`
records the identifications of the two inner point subgroups,
their agreement with the inclusion, the transported radical
measure and the normalization of the inner modulus.
`rationalSemistandardLeviConstantTerm_induced_model` uses these
comparisons to transport the inner normalized integral. The
transitivity theorem then applies the published
`TransitivityData.constantTermInd_constantTermInd`. Its premises
retain the radical product measure, modulus identities,
conjugation modulus and absolute integrability. In its conclusion
the factor is
\(\delta_P(m_1)^{-1/2}\delta_P(m_2)^{-1/2}\), with \(m_i\) the
images in the literal Levi, and the ambient arguments are
\((m_1g_1,m_2g_2)\). The subsequent Fourier comparison also needs
the inducing-representation and Haar normalizations of VII.1.2
and the lower-rank reconstruction hypothesis on the resulting
Schwartz function.
