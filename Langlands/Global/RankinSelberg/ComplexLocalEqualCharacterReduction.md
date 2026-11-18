# The complex equal-rank local equation for a standard additive character

`ComplexLocalEqualStandardCharacterStatement` specializes the published
`ComplexLocalEqualFunctionalEquationStatement` to the parameters \(1\)
and \(-1\), keeping the quantifiers over every rank, inducing list of
the required length, compatible quotient measure, Whittaker coefficient
and Schwartz function. It retains both absolute convergence clauses,
both holomorphy clauses, both meromorphic continuations with their
agreement on a common right half-plane, and the functional equation off
a discrete set.

`complexLocalEqualCharacterReduction` proves the implication from that
standard-character statement to the published local statement for
arbitrary \(a\in\mathbb C^\times\). The standard-character statement is
an open premise of this result.

## Source and conventions

The underlying analytic statement is the equal-rank case of Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), printed and PDF p. 6,
Theorem 2.1 (i)–(iii) and integral (2.6). Jacquet gives the additive
character scaling of the gamma and epsilon factors on p. 5. The
formalization below derives the internal implication from the
Library's own model and positive trace Fourier transform, with their
conventions recorded in `ComplexPlaceFunctionalEquationReduction.md`.
The epsilon identity uses the same norm and self-dual measure as the
published target.

## Implemented proof

Translate the two coefficients from \(\psi_a,\psi_{-a}\) to
\(\psi_1,\psi_{-1}\) by the inverse of the change-of-character diagonal.
Use the transported compatible quotient data for the normalized
integrals. With \(n=r+1\), \(b=|a|\) the usual absolute value, and
\(\beta=\omega_d(a)\omega_{d'}(a)\), the primal multiplier is
\(c(s)=b^{-rns}\) and the dual multiplier is
\(c_d(s)=\beta^n b^{n-n(r+2)s}\). The comparisons in
`ComplexLocalEqualKernelChange.lean` give the two integrability
equivalences and the integral identities at every \(s\).

Apply the standard-character hypothesis to the normalized data. Use its
same half-plane and multiply its continuations by \(c\) and \(c_d\),
respectively. Both factors are entire by their complex exponential
formulas. The integral identities transfer holomorphy and agreement,
and products with the entire factors preserve meromorphy.

The determinant character of the pair blocks at \(a\) is \(\beta^n\).
The proof obtains this by distributing the products over the two
inducing lists and using their lengths. The pair epsilon formula then
contributes \(b^{n^2}\) from the self-dual measure, and
\(b^{2n^2(s-1)}\) from the twist. Together with the determinant
character this gives the identity
\(\epsilon_a(s)c(s)=c_d(1-s)\epsilon_1(s)\).
Here \(c_d(1-s)/c(s)=\beta^n b^{n^2(2s-1)}\), in keeping with the
complex normalized absolute value \(b^2\). Substituting the identity on
the standard-character equation's codiscrete set proves the target with
the same central sign. If \(L\) and \(L^\vee\) are the inverses of the
respective denominators in Lean, the resulting identity is
\(L(s)M_d(1-s)=\omega_{d'}(-1)^r\,\epsilon_a(s)\,L^\vee(1-s)M(s)\).
