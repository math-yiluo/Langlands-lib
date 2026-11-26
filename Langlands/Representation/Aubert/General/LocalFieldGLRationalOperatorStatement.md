# The unadjusted GL operator over a nonarchimedean local field

`Langlands.Aubert.General.RationalPointFamily.GL.localFieldMatrixAlternatingOperator`
is the signed sum of normalized Jacquet restriction followed by normalized
induction, using the actual `LocalFieldData` matrix functors. Each summand
uses `SmoothRep.FiniteLengthGrothendieckGroup.map`, so the Grothendieck group
has the relations from all actual short exact sequences of finite-length
smooth complex representations. The matrix operator takes the finite-length
and exactness proofs for those functors in `LocalFieldMatrixParabolicExactLength`.
The sign for a block shape \(B\) of rank \(n\) is \((-1)^{n-\operatorname{length}(B)}\)
because the corresponding simple roots are the adjacent roots within its blocks.

`LocalFieldGLRationalOperatorComparisonStatement` takes the two global dynamic
finite-length inputs of the canonical point operator,
`DynamicInductionFiniteLengthStatement` and `DynamicJacquetFiniteLengthStatement`.
It asserts that the matrix functors then satisfy their finite-length and
exactness requirements. It also asserts the equality of integer-linear
maps

\[
e^*D_{\mathrm{matrix}}=D_{\mathrm{points}}e^*
\]

for every witness of those matrix requirements, where \(e^*\) is the exact
Grothendieck pullback along the continuous isomorphism from the rational points
to matrices. The equality applies to every virtual class and uses the actual
upper standard parabolic families and positive and inverse half-moduli. These
are the functors of Bernstein and Zelevinsky 1977 §§1.7–1.8 and 2.1–2.3.
The resulting sum is Aubert's Definition 1.5 specialized to her choice of
torus and Borel in §2. The matrix and point operators use complex coefficients
and carrier universe `max (u + 1) v` with independent universes \(u,v\).
The comparison covers positive characteristic and includes the trivial group
at rank zero, with the sign of its unique block shape equal to one.

- `bernstein-zelevinsky-1977-induced-i`,
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §§1.7–1.8 and 2.1–2.3, printed pp. 444 and 446.
- `aubert-1995-duality`,
  SHA-256 `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
  Definition 1.5 and opening of §2, printed pp. 2180–2181 and 2183–2184.
