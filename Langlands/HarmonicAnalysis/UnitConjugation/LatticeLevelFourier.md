# Finite character expansion of a lattice level

Let \(A\) be a topological additive group coming from a ring, with a self-dual
bicharacter \(e\). Assume \(A\) is locally compact, second countable and has a
compact open exhaustion, with its Borel measurable space. For a compact additive
subgroup \(L\) and a compact open additive subgroup \(N\), let \(S\) be the set of
distinct characters \(x\mapsto e(x,z)\) on \(L\) obtained from \(z\in N^*\).
`latticeLevelFourier` shows that \(S\) is finite and nonempty, and
\[
\sum_{\chi\in S}\chi(x)=|S|\,\mathbf 1_N(x)\qquad (x\in L).
\]

The restriction map on frequencies factors through the discrete quotient
\(A/L^*\). The image of the compact subgroup \(N^*\) in this quotient is finite,
and its character image is an additive group containing the trivial character.
Evaluation at \(x\) is a character of that finite group. It is trivial exactly
when \(x\) belongs to \(N^{**}=N\). Finite additive character orthogonality
then gives the formula.

This gives the additive indicator expansion needed when using compact character
sums in the descent argument of Clozel, *Characters of nonconnected, reductive
p-adic groups*, §3.4, Lemma 5, p. 154 and §3.5, pp. 156–157.
