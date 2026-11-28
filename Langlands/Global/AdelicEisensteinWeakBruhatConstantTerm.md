# The weak Eisenstein constant term and its Weyl summands

`EisensteinWeakBruhatConstantTermStatement` formulates Delorme
(4.3). It takes a standard inducing parabolic \(P\), a standard
target parabolic \(Q\), minimal Weyl representatives of the double
cosets, and a meromorphic continuation of the Eisenstein series
of a square-integrable inducing form. The compact satisfies
Iwasawa coverage and has maximal intersections with the standard
Levis.

The conclusion retains an individual meromorphic family for each
minimal Weyl element whose source intersection is the entire
inducing parabolic. This is the source condition in \(W(P,Q)\).
Each family agrees on a sufficiently regular convergence chamber
with the corresponding `summand` of the full constant-term
formula. The summand is the actual series of intertwining
integrals over the rational cosets of the target intersection
parabolic.

On one common domain containing the entire imaginary axis, all
pointwise evaluations of the families are holomorphic. At each
imaginary parameter every continued term is automorphic on the
target parabolic quotient. Its normalized left action by a
positive split point of \(Q\) is multiplication by \(a^{w\lambda}\).
In Lean, `transportedParameter` restricts the inducing parameter
and takes its Weyl transport to the target intersection. Then
`splitWeylCharacter` evaluates it at the lift of \(a\) to the
positive split component of that intersection. The lemma
`norm_splitWeylCharacter_imaginary` checks that this scalar has
norm one. The sum of these families satisfies `IsWeakConstantTerm`
for the given continuation and every imaginary parameter.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 6–7 and 16–17,
particularly (4.1)–(4.3). The decomposition of the full constant
term and the strict exponent criterion for the other terms are
given in E. Lapid, *On the asymptotic inner product formula for
Eisenstein series*, (12)–(13) and Lemma 6, pp. 321–323.
