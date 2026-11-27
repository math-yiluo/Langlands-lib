# Root and norm estimates on characteristic truncation shells

For a connected reductive group and a maximal split torus, let \(\Delta_0\)
be the simple relative roots for the chosen generic cocharacter. For the
standard parabolic \(Q\) let \(J=\Delta_0^Q\). The Library's
`ArthurRelative.levelProjection` projects onto \(\mathfrak a_Q\) along the
Levi coroot span. The `ArthurRelative.weight` coordinates for \(J\) read
that Levi component in its simple coroot basis.

`parabolicCharacteristicChamber` is Delorme's \(C_T^Q\). It consists of
\(X\in\mathfrak a_0^G\) satisfying
\(\alpha(X-T_0)\geq 0\) for \(\alpha\in\Delta_0\),
\(\varpi^Q_\beta(X-T)\leq 0\) for \(\beta\in J\), and
\(\alpha((X-T)_Q)>0\) for \(\alpha\in\Delta_0\setminus J\).
`characteristicShell` is the intersection \(C^G_{T+S}\cap C_T^Q\) in
(7.13), using the Library's `characteristicChamber` for the first set.

For each \(\alpha\in\Delta_0\setminus J\),
`eval_lt_of_mem_parabolicCharacteristicChamber` gives \(\alpha(X)>\alpha(T)\).
The Levi component of \(X-T\) is a combination of simple coroots of \(J\)
with nonpositive coefficients. The off-diagonal Cartan pairings with
\(\alpha\) are nonpositive. Hence this component contributes a nonnegative
sum, while the projected component gives a strict inequality. This proves
the bound used in (7.15).

For the Euclidean norm of a Weyl-invariant scalar product on the real
cocharacter space, `cocharacterNorm_le_of_mem_characteristicChamber` gives
\[
  \|X-T_0\| \leq \|U-T_0\|,\qquad
  \|X\| \leq \|U\|+\|T_0\| \qquad (X\in C_U^G,\ U\in\mathfrak a_0^G).
\]
The weight inequalities express \(U-X\) as a nonnegative combination of
simple coroots. Invariance under the root reflection gives
\(2\langle v,\check\alpha\rangle=\alpha(v)\|\check\alpha\|^2\).
Thus \(\langle X-T_0,U-X\rangle\geq0\) by the root inequalities.
Cauchy–Schwarz gives the first bound. Expanding about the midpoint of
\(T_0\) and \(U\) bounds the distance to that midpoint by
\(\|U-T_0\|/2\). The triangle inequality gives the second bound.

The basepoint shift on the right of the first bound is needed for the
chamber as defined on p. 23. In rank one take \(T_0=-v\), \(U=X=2v\)
with \(v\) strictly dominant. Then \(X\in C_U^G\) and
\(\|X-T_0\|=3\|v\|>\|U\|\), whereas the printed (7.16) bounds that distance
by \(\|U\|\) for \(U=T+S\). The second bound above supplies the required
estimate at the origin with the constant used in the source.

`characteristicShell_bounds` proves `CharacteristicShellBoundsStatement`.
For \(T,S\in\mathfrak a_0^G\), \(\delta,k_0\geq0\), assume
\(\|T_0\|\leq\|T\|\), \(\|S\|\leq k_0\|T\|\), and
\(\alpha(T)\geq\delta\|T\|\) for every \(\alpha\in\Delta_0\).
For \(X\) in the shell the second norm bound yields
\(\|X\|\leq(2+k_0)\|T\|\). Combining it with the strict root comparison
gives \(\alpha(X)\geq\delta\|X\|/(2+k_0)\) for every simple root outside
\(J\), as in (7.14).

The source is P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §2, pp. 6–7, for the scalar product, relative
roots and weights, and §7, pp. 23, 26–27, for the chambers and (7.13)–(7.16).
The published PDF in `delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
