# Twisted induction transfer inside a block Levi

`Langlands.BaseChange.TwistedLeviPaleyWiener.twistedLeviInductionTransfer`
proves `TwistedLeviInductionTransferStatement` with independent universes
for \(F\), \(E\) and the inducing representation. For \(C\) refining \(B\)
and arbitrary Haar measures \(\mu\) on \(M_B\) and \(\nu\) on \(M_C\), the
linear map \(CT\) takes tests on \(M_B\) to tests on \(M_C\). For each
admissible inducing pair \((\Xi,A)\) with admissible induction, the twisted
character of \((\Xi,A)\) evaluated at \(CT(f)\) equals the twisted character
of the unnormalized induction evaluated at \(f\).
[Statement](TwistedLeviPaleyWienerStatements.md)

## Proof

The cyclic extension and the module topology give \(E\) its nonarchimedean
local field structure. Write \(P=\operatorname{relParabolic}(E,B,C)\) and
\(p=\operatorname{relProjection}(E,B,C)\). To show that \(p\) is open, the
proof uses a transvection at each allowed off-diagonal entry of the finer
parabolic. Containment forces the same entry to be allowed in the coarser
parabolic. Applying this in both directions to entries in the same finer
diagonal block shows that the block lies inside a coarser diagonal block.
Extracting the coarser blocks of a finer block diagonal matrix therefore
defines a section \(M_C\to P\). The block maps make the section and \(p\)
continuous. For an identity neighborhood \(U\) in \(P\), its inverse image
under the section is a neighborhood in \(M_C\) contained in \(p(U)\). Translation gives
openness. [Relative parabolic and projection](TwistedLeviParabolic.md)

The subgroup \(P\) is closed as the inverse image of the finer parabolic
under the block diagonal embedding of \(M_B\). For each \(m\in M_B\), the
blockwise Iwasawa theorem supplies a tuple \(k\) in the product of integral
subgroups such that \(mk\) is upper triangular in every block. Its
block diagonal image is upper triangular in \(\mathrm{GL}_n(E)\), so
\(mk\in P\) and the class \(Pm\) is represented by \(k^{-1}\). The product
of integral subgroups is compact and maps onto \(P\backslash M_B\),
which proves compactness of the quotient.

The modular character of \(M_C\) is the product of the modular characters of
its general linear factors. Each factor is unimodular, so the arbitrary
Haar measure \(\nu\) is right invariant. The positive cyclic exponent of
\(\sigma\) also kills its action on every block of \(M_B\). The entrywise
actions preserve \(P\) and commute with \(p\), and the action on \(M_B\)
is continuous in both directions. The induced operator in the common-test
theorem is `relInducedSigmaIntertwiner`. On a section \(s\) it sends
\(s\) to the section with value \(A(s(\sigma^{-1}g))\) at \(g\).

With these hypotheses `twistedInducedTest` gives, for each ambient test,
one inducing test valid for every admissible pair and admissible
induction. Its trace calculation uses a finite double-coset model of
induced fixed vectors and a sum of translated normalized indicators
from the diagonal entries. The proof chooses such a test for each
element of a complex basis of the ambient Schwartz–Bruhat space.
It extends those choices linearly to \(CT\) and uses equality on basis
vectors to obtain the equality of distributions.
[Common inducing-test theorem](TwistedCharacter/InducedTest.md)

## Relation to the sources

Henniart–Lemaire II.4.5, formula (2), gives the descent identity on
\(\mathrm{GL}_n(E)\) for tensor-product pairs, normalized induction and
measures of volume one on the indicated compact subgroups. In that formula
the half modulus can be absorbed into the inducing representation to
compare normalized and unnormalized covariance. The proof here obtains
the identity on Levi products directly from the unnormalized common-test
theorem, with the given measures and an arbitrary admissible inducing
pair. The inverse change of variable in the induced operator is the one
used in Henniart–Lemaire II.4.4 and Rogawski §3.
[Comparison of conventions](TwistedLeviPaleyWiener.md)

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe
  pour GL_n en caractéristique non nulle*, Mém. SMF 124 (2011).
  II.4.4, printed p. 85, and II.4.5, formula (2), printed p. 86.
  Literature ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
  SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
- J. D. Rogawski, *Trace Paley–Wiener theorem in the twisted case*, Trans.
  Amer. Math. Soc. 309 (1988), 215–229. §3, printed p. 218.
  Literature ID `rogawski-1988-twisted-trace-paley-wiener`.
  SHA-256 `86fbe930fc1db80a3a0f279db5d83af85b7e37dc7e041d813ebc9f5fdcb7c274`.
