# The p-adic specialization of the local-field matrix functors

`Langlands.Aubert.General.RationalPointFamily.GL.PadicMatrixFunctorSpecializationStatement`
compares two realizations of the normalized matrix functors for a `PadicField F`.
The first uses `T.toLocalFieldData`, which keeps the topology and residue
normalization of `T`. The second uses the existing p-adic `TopologicalData`
functors. Both use the same actual upper block parabolic and diagonal-block
product Levi for each ordered block shape.

The statement gives equality of the bundled functors on the full smooth
complex categories. For induction this identifies the right-translation
action and maps with the same positive half of the block modulus. For
Jacquet restriction it identifies the actual radical quotient and its maps
with the same inverse half. It also supplies preservation of finite length
and actual short exact sequences of finite-length objects for the
`LocalFieldData` functors.

For every choice of the preservation proofs, the resulting maps on the
exact Grothendieck groups equal `Parabolic.normalizedInductionK0` and
`Parabolic.normalizedJacquetK0`. These are the maps in
`Langlands.Aubert.alternatingOperator`. The field and representation
universes are independent and the comparison includes rank zero.

The mathematical inputs are the normalized functors on the standard GL
triple of Bernstein and Zelevinsky, which Aubert uses in Definition 1.5.
The comparison uses the identity on the underlying field and matrix groups.
The normalized determinant of each block agrees under `toLocalFieldData`
because it uses the same residue cardinality and valuation.

- `bernstein-zelevinsky-1977-induced-i`,
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §§1.7–1.8 and 2.1–2.3, printed pp. 444 and 446.
- `aubert-1995-duality`,
  SHA-256 `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
  Definition 1.5 and opening of §2, printed pp. 2180–2181 and 2183–2184.
