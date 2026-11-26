# Normalized GL functors on rational points and on matrices

`Langlands.Aubert.General.RationalPointFamily.GL.LocalFieldGLRationalFunctorsStatement`
compares the two pairs of actual normalized functors used for the GL
specialization of Aubert's operator. It is stated for every `LocalFieldData F`,
every rank \(n\), every strictly decreasing diagonal cocharacter and every
ordered block shape \(B\). The cocharacter selects the upper triangular
chamber. The standard index \(J\) consists of the adjacent simple roots
within blocks.

Let \(e\) be the continuous group isomorphism from the actual rational
points, in the evaluation topology, to the matrix group. Let \(e_L\) be its
restriction to the Levi, followed by the inverse of the block diagonal
embedding. Thus \(e_L\) maps to the product of the actual matrix block
groups. The natural isomorphisms in the statement are

\[
e^* i_B \simeq i_J e_L^*, \qquad e_L^* r_B \simeq r_J e^* .
\]

They act on the full smooth complex categories. In the induction isomorphism,
a function \(f\) goes to \(x\mapsto f(e(x))\) in the right-translation model.
In the Jacquet isomorphism, the class of a vector goes to the class of the
same vector in the actual rational-point radical quotient. The statement
requires both formulas on the components of the natural isomorphisms, so
these formulas also describe how the comparisons act in diagrams of
intertwiners. The functors use the positive induction half-modulus and
the inverse Jacquet half-modulus.

This is the transport of the functors of Bernstein and Zelevinsky 1977
§§1.7–1.8 and 2.1–2.3 between two models of their standard GL triple.
Aubert uses these functors in Definition 1.5, and uses the diagonal torus
and upper triangular parabolics for GL in §2. The field can have positive
characteristic. The rank-zero case uses the empty root set and the empty
block shape. Field and representation universes are independent and
the carrier universe is `max (u + 1) v`.

- `bernstein-zelevinsky-1977-induced-i`,
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §§1.7–1.8 and 2.1–2.3, printed pp. 444 and 446.
- `aubert-1995-duality`,
  SHA-256 `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
  Definition 1.5 and opening of §2, printed pp. 2180–2181 and 2183–2184.
