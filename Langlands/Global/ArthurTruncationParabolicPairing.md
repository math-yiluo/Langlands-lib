# Pairing a periodized compact radical average

Let $\Lambda\leq\Gamma$ be discrete adelic subgroups and let $A_U$ be
the normalized average over the compact rational quotient of a closed
adelic subgroup $U$. The radical hypotheses are those of
[Measurable averages along a compact radical quotient](ArthurTruncationAverage.md).
Let $w$ be bounded by one, measurable and invariant on the left under
$\Lambda$ and $U(\mathbb A_F)$. Assume the set of cosets in
$\Lambda\backslash\Gamma$ on which $w(\delta x)$ is nonzero is
contained in a fixed finite set for $x$ in each compact set. In Arthur's
formula the respective inputs are $P(F)$, $G(F)$, $N_P$, and the hatted
chamber cutoff.

`periodize` sums $a(\delta x)$ over $\Lambda\backslash\Gamma$ using
the chosen coset representatives. Right translation permutes the cosets,
so a left $\Lambda$-invariant summand gives a left $\Gamma$-invariant
sum. `periodize_locallyBounded` uses countability for measurability and
bounds the sum on a compact set by the number of active cosets times a
bound on the finite union of the corresponding translates.

`periodize_radical_pairing` compares the products of the periodization
of $(A_U f)w$ with $b$ and the periodization of $(A_U b)w$ with $f$.
Here $f$ and $b$ are locally bounded, measurable and $\Gamma$-invariant,
and $b$ has compact support modulo $\Gamma$. Both products are
integrable on a Borel fundamental domain of $\Gamma$ and have equal
integrals there. The proof proceeds as follows.

1. Choose a compact set $C$ representing the support of $b$ modulo
   $\Gamma$. Wherever $wb$ is nonzero, write $x=\lambda\delta c$ with
   $c\in C$ and $\lambda\in\Lambda$. Invariance of $w$ restricts
   $\delta$ to the finite active set for $C$. Thus $wb$ is supported
   modulo $\Lambda$ on a finite union $L$ of translates of $C$.
2. If $w A_U b$ is nonzero at $x$, some $n\in U(\mathbb A_F)$ has
   $b(nx)\ne 0$. Then $w(nx)\ne 0$, so $nx=\lambda y$ with
   $y\in L$. Conjugating $n^{-1}$ by $\lambda^{-1}$ leaves it in the
   radical. Write that element as the product of a rational radical
   point and a point in a compact set $E$ of radical representatives.
   It follows that $x$ belongs to the $\Lambda$-saturation of $EL$.
   The two products $(A_U f)bw$ and $f(A_U b)w$ on the smaller
   quotient are therefore bounded on compact sets and supported on
   compact images. Local finiteness of the discrete quotient measure
   gives absolute integrability.
3. Use the discrete unfolding formula on these two products to obtain
   integrable periodized products on the larger quotient. On the
   $\Lambda$ fundamental domain, each product has the same integral
   as its normalized radical average. The two averages agree
   pointwise with $(A_U f)(A_U b)w$ because $w$ and both averages are
   invariant under the adelic radical. [Discrete integral unfolding](EisensteinConstantTerm/QuotientUnfolding.md)

The derivation is the absolutely convergent, bilinear form of the
parabolic calculation in Arthur 2005, Proposition 13.1(c), p. 69.
[Source details](ArthurTruncationSelfAdjointProof.md#sources)
