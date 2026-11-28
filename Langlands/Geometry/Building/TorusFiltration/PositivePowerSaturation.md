# Coprime powering in positive minimal congruent terms

`minimalCongruentPoints_mem_of_coprime_pow` applies to a point in the
strictly positive union over the maximal unramified field. If its
power by an exponent prime to the residue characteristic belongs to
a specified minimal congruent term, then the point belongs to that
term.

Choose a strictly positive shallow term containing the point, using
`minimalCongruentPoints_antitone`. Its smooth realizing model has
unipotent special fibre by `minimalCongruentPositiveUnipotent`.
A power of the residue characteristic therefore puts the integral
section in the first reduction kernel. Further powers enter
arbitrarily deep congruence kernels by
`IntegralModel.pow_pow_mem_congruenceKernelAt`. The formula
`minimalCongruentPoints_add_pnat` identifies these kernels with the
integer shifts of the shallow depth. In particular a power of the
residue characteristic puts the point in the specified term.
Bézout's identity for the two coprime powers gives membership of the
original point.

The calculation derives from the congruence shift and positive-depth
geometry of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition B.10.10 and Proposition B.10.12.
