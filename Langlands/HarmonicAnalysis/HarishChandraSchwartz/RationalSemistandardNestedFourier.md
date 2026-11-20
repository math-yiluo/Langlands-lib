# Fourier evaluation in the nested constant-term diagram

Waldspurger compares the evaluated induced Fourier tensor of \(f^M\) on an
inner parabolic of \(M\) with the tensor of \(f\) on its lift to \(G\).
[Waldspurger, *La formule de Plancherel pour les groupes p-adiques*
(2003), pp. 272, 315, 322](https://doi.org/10.1017/S1474748003000082)

`rationalSemistandardFourierOrbit_eval_constantTerm` specializes VII.1.2
to the actual value of the Fourier orbit section at each inducing
representation. Its coefficient transform uses the formal degree, Levi Haar
measure and normalized constant-term Schwartz function of that component.
`RationalSemistandardParabolicLift` specifies \(P'=P^M U\) on all test schemes
and matches the final Levi and inner radical through the Levi inclusion.
Containment in the outer parabolic gives properness of the lifted index
whenever the outer index is proper.

`RationalSemistandardNestedFourierStatement` compares the two evaluations
for the actual Schwartz function \(f^M=f^{(P,\mathrm{Ind})}(g_1,g_2)\)
on the outer Levi model. For a point pair \((m_1,m_2)\), the arguments
on \(G\) are \((m_1g_1,m_2g_2)\), using the model's point inclusion.
The scalar is \(\delta_P(m_1)^{-1/2}\delta_P(m_2)^{-1/2}\).
The final Levi comparison to the literal subgroup in \(G\) is
`RationalSemistandardParabolicLift.leviEquiv`, composed from the
given inner comparison and the subgroup inclusion certified by the lift.
The two quotient Haar measures enter through the respective actual formal
degrees. The prescribed inducing representations must match by pullback
along this equivalence and have equal formal degrees.

The conditional proof `rationalSemistandardNestedFourier` uses separate
VII.1.2 analytic inputs on the Levi model and on \(G\). It applies
`rationalSemistandardLeviConstantTerm_induced_transitivity` with the
actual radical measure and modulus comparisons, transitivity data, and
pointwise integral convergence. The resulting scalar relation between
the two constant-term Schwartz functions is transported by
`coefficientFourierTransform_eq_smul_of_modelTransport` under the
measure-preserving comparison of the two literal final Levi Haar measures.
An application to every lower-rank orbit member will need the pertinent
parabolic lifts and corresponding ambient orbit members. Reconstruction
on the outer Levi is a separate hypothesis of the detection argument.
