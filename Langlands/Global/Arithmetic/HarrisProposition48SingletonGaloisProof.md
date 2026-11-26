# Galois stability of the singleton Mackey constituent

`Langlands.Global.Harris.proposition48SingletonMackeyGaloisStableTC` proves
`Langlands.Global.Harris.Proposition48SingletonMackeyGaloisStableTCStatement`
with independent universes for the local field and the spectral carriers.
Given totally complex spectral rigidity and isobaric invariance, every
\(E\)-automorphism of the step field \(D\) fixes the actual cuspidal class
weakly induced from the identity Mackey character.

Normality of \(L/E\) extends an automorphism \(\sigma\) of \(D/E\) to an
automorphism \(g\) of \(L/E\) by `AlgEquiv.liftNormal`. Let \(H\) fix \(D\)
and \(K\) fix the image of \(E'\) under the given embedding into \(L\).
The cardinality-one hypothesis identifies the double coset of \(g\) with
that of \(1\). By `DoubleCoset.eq` this gives \(g=h\tau\) with \(h\in H\)
and \(\tau\in K\). For \(x\in D\), \(h\) fixes \(\sigma(x)\), so
cancelling \(h\) from \(h(\tau(x))=g(x)=h(\sigma(x))\) gives
\(\tau|_D=\sigma\). Membership in \(K\) identifies the embedding
\(\tau\circ(E'\hookrightarrow L)\) with the original embedding.

`proposition48MackeyConstituentGaloisConjugate` transports the constituent
from \(1\) to \(\tau\). That theorem uses naturality of the idele-class
norm and arithmetic transport of weak induction. The equality of
embeddings identifies the two image fields, the composita with \(D\), and
the inducing characters obtained by transport of \(\xi\) followed by
pullback along the norm. In Lean the weak-induction predicate is
expressed as a function of the embedding, including its dependent
inclusion algebras, so equality of embeddings identifies the entire
predicate.

The two weak inductions now give attached spectral systems for the
original and conjugate classes. On the intersection of their cofinite
sets, at places where both systems are defined, choose a common family
of uniformizers in the compositum above the given place. Both Euler
polynomials equal the induced polynomial of that family for the same
character. The CM field \(E\) is totally complex, and
`isTotallyComplex_of_algebra` gives total complexity of \(D\).
Apply the supplied rigidity and isobaric invariance to the singleton
data of the original class. Equality of singleton multisets gives
equality of their constituents, which is the claimed Galois stability.

## Source

Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`. The proof of Proposition 4.8 gives the
norm-pulled Mackey characters on printed p. 202, derives isobaric Galois
invariance on p. 202, and applies it in the singleton case on p. 203
(PDF pp. 26–27,
SHA-256 `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`).
The companion `math_9611226v1.tex` gives these passages at lines
1579–1597, 1630–1644 and 1666–1674
(SHA-256 `984b1397ac75baee5d261becad137a9ae91e1593f3da0d166df5136fb52e4af7`).
Harris compares the isobaric spectrum through an invariant restricted
\(\lambda\)-adic family. The singleton specialization uses the fixed
inducing character to obtain the Euler comparison directly.
