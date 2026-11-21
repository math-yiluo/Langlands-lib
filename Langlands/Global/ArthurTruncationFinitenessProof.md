# Pointwise finiteness of Arthur's truncation sums

`Langlands.Global.ArthurTruncation.truncationFiniteness` proves
`TruncationFinitenessStatement`. For each standard parabolic $P=P_J$, each
truncation parameter $T_p$, and each $x\in G(\mathbb A_F)$, it proves that
the shifted hatted chamber has finite support on $P(F)\backslash G(F)$.
The height $H_0$ uses the supplied compact Iwasawa factor and the supplied
bijectivity of real character restriction for $P_0$. See the
[statement and its conventions](ArthurTruncationStatement.md).

Arthur 2005, §13, p. 68, asserts finiteness immediately after (13.1). Arthur
1978, Lemma 5.1, pp. 936–937, proves a quantitative estimate over $\mathbb Q$
on $G(\mathbb A)^1$ using highest-weight representations and Siegel
representatives. The formal theorem gives the qualitative conclusion over
number fields on the full adelic group, by bounding projective heights.
[Arthur 2005, §13](https://www.claymath.org/library/cw/arthur/pdf/62.pdf#page=68),
[Arthur 1978, Lemma 5.1](https://www.claymath.org/library/cw/arthur/pdf/7.pdf#page=26).

## Implemented proof

1. Use Chevalley's line stabilizer theorem to choose a representation $\rho$
   with a coordinate line $[v]$ whose exact stabilizer is $P_J$. Denote
   the line character on $P_0$ by $\chi$ and its restriction to the
   maximal split torus by $\psi$. For each simple root $\alpha\in J$ the
   line is stable under the standard Levi for $J$. Its character is fixed
   by the simple reflection in that Levi's Weyl group. Applying the
   reflection formula and pairing with $\alpha^\vee$ gives
   $\langle\psi,\alpha^\vee\rangle=0$.
2. For $\alpha\notin J$, intersect the stabilizer with the standard Levi
   for $\{\alpha\}$. The intersection is the minimal standard parabolic
   of this rank-one Levi. The published rank-one line character theorem
   supplies $d\psi=\eta|_{A_0}+b\alpha$, with $d,b>0$ and $\eta$
   a rational character of that Levi. Its restriction is fixed by the
   simple reflection, so pairing gives
   $d\langle\psi,\alpha^\vee\rangle=2b>0$.
   The stabilizer intersection and rank-one theorem are in
   [ParabolicWeylDisplacement](../GroupScheme/Rational/ParabolicWeylDisplacement.md)
   and
   [RankOneStandardParabolicLineCharacter](../GroupScheme/Rational/RankOneStandardParabolicLineCharacter.md).
3. Put $c_\alpha=\langle\psi,\alpha^\vee\rangle$ and
   $L=\sum_{\alpha\in\Delta_0}c_\alpha\varpi_\alpha$, where
   $\varpi_\alpha$ is Arthur's weight for the full simple system. These
   weights are dual to the simple coroots, so $L$ and evaluation by
   $\psi$ agree on the simple coroot span. For $\delta\in G(F)$, the
   difference $H_0(\delta x)-H_0(x)$ belongs to that span. Indeed every
   ambient rational character evaluates on $H_0$ by its adelic logarithmic
   norm, which vanishes on $K$. The product formula makes this norm
   unchanged by rational left translation. The
   published real Levi decomposition identifies the annihilator of those
   restricted characters with the simple coroot span.
4. The nonzero cutoff makes $\varpi_\alpha(H_0(\delta x)-T_p)>0$ for
   $\alpha\notin J$. The other coefficients vanish, so
   $L(H_0(\delta x)-T_p)\ge 0$. Evaluating on the height difference in
   step 3 gives the lower bound
   $$
   \langle\psi,H_0(\delta x)\rangle\ge
   B,\qquad B=\langle\psi,H_0(x)\rangle-L(H_0(x)-T_p).
   $$
   The left side equals evaluation of the $P_0$-Iwasawa height at $\chi$.
5. The published projective embedding sends the coset $P(F)\delta$
   injectively to $E(P(F)\delta)=[\rho(\delta^{-1})v]$. The adelic
   line-character height estimate gives
   $$
   H_{P_0}(\delta)(\chi)\le A-\log H(E(P(F)\delta)).
   $$
   The Iwasawa increment formula expresses
   $H_{P_0}(\delta x)-H_{P_0}(\delta)$ as $H_{P_0}(kx)$ for some
   $k\in K$. Since $Kx$ is compact and height evaluation is
   continuous, the evaluation of the increment at $\chi$ is bounded
   above by a constant $M$. The projective logarithmic height of every
   coset in the support is therefore at most $A+M-B$.
   [AdelicParabolicProjectiveHeight](AdelicParabolicProjectiveHeight.md),
   [AdelicIwasawaOrbitHeight](AdelicIwasawaOrbitHeight.md),
   [AdelicEisensteinCompactBounds](AdelicEisensteinCompactBounds.md).
6. The published projective height summability theorem gives a summable
   family $H(q)^{-d}$ for some $d\ge 0$. On a logarithmic height
   sublevel $\log H(q)\le R$ every term is at least the positive
   constant $\exp(-dR)$. The sublevel is finite by comparison with the
   constant family. Its preimage under the injective embedding $E$
   contains the support and is finite. The proof uses the chosen
   quotient representative from the target to apply the bounds.
   [ProjectiveHeightSummability](ProjectiveHeightSummability.md).
