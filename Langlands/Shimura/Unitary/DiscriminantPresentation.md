# The discriminant presentation and its split finite local invariants

Let \(K/E\) be a CM extension and \(A\) a central simple algebra over \(K\)
of dimension \((2m)^2\). `EvenDiscriminantPresentation.fromDimension`
chooses a finite Galois matrix splitting after presenting \(K\) and \(A\)
in the universe of \(E\).
`EvenDiscriminantPresentation.brauerClass` transports the given
CM conjugation and involution through that presentation and takes the
determinant-factor-set discriminant class. It is killed by two. The
original CM field and base field have independent universes.

For \(2m>0\), fix embeddings into the local algebraic closures, a split
place identification at a finite place of \(E\), and an actual upper
place with supplied completed Brauer invariant \(x\).
`localInvariant_discriminant_at_split` gives \(m x\) for the invariant of
the discriminant at the lower completion. The degree-one completion equivalence allows
extension through the quadratic center via the chosen place. The
restriction formula gives \(m\) times the upper algebra class in that
presentation. A semilinear ring equivalence of completed algebras
compares vanishing of this multiple with vanishing on the original
completed algebra, using tensor powers. Both invariants are killed
by two, so agreement on vanishing determines the value in
\(\mathbb Q/\mathbb Z\).
