# Fourier vanishing for the actual Levi constant term

In the proof of VIII.2.1, each semistandard parabolic of the Levi \(M\)
contributes a Fourier component of \(f^M\). Its lift to \(G\) lies in
the original proper parabolic. The nested comparison therefore expresses
each evaluated Fourier tensor of \(f^M\) in terms of a vanishing proper
component of \(f\).
[Waldspurger, *La formule de Plancherel pour les groupes p-adiques*
(2003), pp. 321–322](https://doi.org/10.1017/S1474748003000082)

`RationalSemistandardNestedFourierMatch` states the inputs at two actual
indices of the Fourier families on \(M\) and \(G\). The type of each index
fixes its discrete-series orbit and the quotient Haar measure used to compute
its formal degree. Every member of the inner unitary orbit must match an
ambient member by pullback along the literal final Levi isomorphism, with equal
formal degree. The match also supplies the all-test parabolic lift, both
VII.1.2 evaluation hypotheses, the III.6 radical measure and modulus
comparisons, the equality of final Levi Haar measures under transport and
integrability of the translated radical integral.

`RationalSemistandardNestedFourierCoverage` requires such a match for every
inner index, including the whole-group parabolic of \(M\).
`RationalSemistandardLeviFourierVanishingStatement` then shows that zero of
the actual proper cutoff on \(G\) implies zero of the entire Fourier family
of `rationalSemistandardLeviConstantTerm` at each pair \((g_1,g_2)\).
The statement takes the outer parabolic's properness and its conjugation
modulus. The Levi function uses the specified comparison of the Schwartz
weights along the Levi inclusion and the restriction of the ambient matrix
representation. The field and the complex representation carriers have
independent universes.

The proof applies `rationalSemistandardNestedFourier` pointwise on each orbit
and uses extensionality of the actual normalized induced functions. The lift's
properness follows from containment in the original proper parabolic. The
result supplies the vanishing premise for reconstruction on \(M\), which
is a separate lower-rank input.

The structural inputs are the all-test parabolic lift, the literal subgroup
equivalences and the coverage of the actual orbits under representation
transport. The analytic inputs are the two VII.1.2 evaluations, the III.6
measure and modulus data, the Levi Haar and degree comparisons and the
radical integrability at the indicated translated pair.
