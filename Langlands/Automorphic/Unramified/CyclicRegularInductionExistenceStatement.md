# Actual cuspidal existence for cyclic regular induction

`Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceStatement.{uF,uE,uV,uW}`
and `CyclicRegularInductionExistenceTCStatement.{uF,uE,uV,uW}` give the
existence used in the regular induction and regular orbit-lift reductions.
In a cyclic Galois extension `E/F` with a supplied generator `σ`, the
upper cusp `T` has unitary central character and is stable under none of
`σ^i` for `0 < i < [E:F]`. The conclusion chooses an actual lower cusp
`S` with unitary central character and rank multiplied by `[E:F]`. Its
class is weakly induced from the class of `T` through their genuine
spectral attachments. The companion adds total complexness to the base.
The existence claim does not depend on a choice of norm-kernel character.

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula* (1989), Chapter III, Lemma 6.4, pp. 217–218, gives the
cuspidality in arbitrary cyclic degree. The prime existence input is
III.4.2(e), pp. 202 and 207–210. Chapter III, Definition 6.1 and Theorem 6.2,
pp. 214–217, identify the induction and give induction by stages.

For the tower argument, let `K` be the fixed field of a subgroup of prime
order in `Gal(E/F)`. The upper cusp remains regular for `E/K`. Take its
prime regular-orbit realization over `K`. Choose the norm-kernel character
for `E/K` using `cyclicNormKernelCharacter`. The pair-multiplicity
comparison for the singleton lower datum with itself counts exactly
`[E:K]` diagonal pairs in the upper orbit. This forces the actual lower
class to be fixed by all powers of the norm-kernel character. The orbit
comparison recovers weak induction through the prime layer.

To continue down the tower, suppose the class over `K` were fixed by a
nontrivial automorphism of `K/F`. Lift that automorphism to `Gal(E/F)`.
Equivariance of weak base change, as in III.4.4(iii), printed p. 211,
makes the conjugate prime orbit a weak base change of the same class over
`K`. Their cofinite Euler factors agree by comparison of attachments and
the base-change power rule. Constituent recovery, III.(2.4), p. 200,
identifies the two multisets. The conjugate of `T` must then belong to the
prime subgroup orbit of `T`. This gives a nonidentity automorphism of
`E/F` fixing the class of `T`, a contradiction. This argument treats every
nonidentity power in the quotient. Apply induction on the field degree
and compose the weak inductions by stages. In degree one, transport the
realization, its unitary central character and its spectral data along
the field equivalence. If `F` is totally complex, so is every intermediate
field and the proof can use the totally complex prime and pair inputs.
