# The hatted cutoff on standard adelic parabolic quotients

`chamberCutoff` is the complex-valued cutoff $\widehat\tau_P(H_0(x)-T_p)$
from Arthur's truncation formula (13.1). The parabolic is indexed by
$J=\Delta_0^P$. The height uses the given compact Iwasawa subgroup $K$
and the comparison with the real character space of the maximal split
torus. [Truncation conventions](ArthurTruncation.md)

`chamberCutoff_properties` proves measurability, a norm bound of one, and
left invariance under $P(F)$ and $N_P(\mathbb A_F)$. For a simple root
$\beta\notin J$, the weight $\varpi_\beta$ vanishes on each coroot in $J$
by `ArthurRelative.weight_coroot`. The perfect character pairing writes
it as evaluation against a vector in the coroot annihilator.
`standardLeviCharacterAnnihilator` realizes that vector as a restricted
real rational character of the standard Levi. Pullback along the dynamic
limit homomorphism supplies a character parameter of $P$. A minimal
parabolic Iwasawa factorization computes both heights, so evaluating
$\varpi_\beta$ on $H_0(x)$ is the same as evaluating this parameter on
$H_P(x)$. The character logarithm vanishes on rational points by the
product formula and on the unipotent radical by character triviality.
The shifted inequalities are measurable by continuity of the scalar
height evaluations. [Character restriction to the split torus](../GroupScheme/Rational/StandardLeviCharacterAnnihilatorProof.md)
[The character logarithm and Iwasawa height](AdelicIwasawaHeight.md)

`chamberCutoff_finite_on_compact` gives a single finite set of cosets
for all $x$ in a compact subset $C$ of $G(\mathbb A_F)$. The Iwasawa
increment formula expresses $H_0(\delta x)-H_0(\delta)$ as $H_0(kx)$
for some $k\in K$. The evaluations of the finitely many weights are
bounded above on $KC$. The image $v$ of the positive cocharacter $\nu$
has strictly positive evaluation under every full simple weight. Choose
$M$ to bound the increments by $M\varpi_\beta(v)$ simultaneously for
all simple weights. A coset active at some $x\in C$ with parameter $T_p$
is then active at the identity with parameter $T_p-Mv$. The published
pointwise finiteness theorem gives the finite set at this shifted
parameter. [Iwasawa height increments](AdelicEisensteinCompactBounds.md)
[Positivity of full weights](ArthurTruncationRay.md)
[Pointwise finiteness](ArthurTruncationFinitenessProof.md)

This is the compact-uniform support bound used in the local boundedness
and compact-support pairing for Arthur 2005, §13, pp. 68–69. The argument
uses the Library's qualitative finiteness theorem for the source assertion
in Arthur 1978, Lemma 5.1, pp. 936–937.
[Source details](ArthurTruncationSelfAdjointProof.md#sources)
