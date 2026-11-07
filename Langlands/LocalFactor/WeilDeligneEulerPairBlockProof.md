# The ordinary pair-block Euler statement

`Langlands.LocalFactor.wdEulerPairBlock` proves the existing
`WDEulerPairBlockStatement.{uK, uG, uV, uW}` with independent coefficient,
group and two carrier universes. Every hypothesis and all three conclusions
of the published proposition are retained: the field has characteristic zero,
`I` is normal, the norm character is trivial on `I`, and the two block lengths
are `n+1` and `m+1`. The Weil representations may have rank zero.

This is an internal deduction from the published block-pair kernel calculation
in `Langlands.LocalFactor.WeilDeligneBlockPair` and the full-degree result in
`Langlands.LocalFactor.UnramifiedDegree`. It makes no additional source claim
and assumes no pair-block formula. It does not prove assembly epsilon
inheritance or any local-constant-system existence assertion.

The published `WeilDeligne.eulerPolynomial_block_block` identifies the Euler
polynomial of the inertia-fixed monodromy kernel of the actual block tensor
with that of a componentwise operator on `min(n+1,m+1)` copies of `(A tensor B)^I`.
The component of index `j` is the action of the supplied group element scaled
by `nu(Phi)^(n+m-j)`. Applying `eulerPolynomial_pi` yields exactly the first
conjunct. Taking the reciprocal after the polynomial algebra map and distributing
over the finite product yields the rational-factor conjunct.

For the rank conjunct, apply the same published polynomial identity at the
identity group element. The componentwise operator there is the identity,
since the character and representation send the identity to the identity.
The kernel representation also acts invertibly. The published full-degree
identities therefore identify the polynomial degrees with the dimensions of
the two spaces. The dimension of the finite function space is the number of
indices times the dimension of `(A tensor B)^I`. This proves the exact kernel
rank formula without any positive-rank assumption.
