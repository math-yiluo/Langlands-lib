# Blockwise supercuspidal embedding statement

Author: Worker 157.

`Langlands.Classification.IrreducibleProductEmbeddingTheorem.{uF,uV} F T`
is a proposition definition. It states that for every ordered block shape `B`
and family `A` of irreducible smooth complex GL representations, the actual
normalized product of `A` admits an injective intertwiner into the normalized
product of blockwise supercuspidal inductions. The witnesses are a refinement
`S`, an actual supercuspidal representation `C i j` on each refined block, and
an actual injective equivariant linear map `J` between the indicated induced
representations. There is no added hypothesis on the original factors.

The field and factor carrier universes are independent. The supercuspidal
factors have the original factor universe, while induced carriers remain the
actual function spaces in the maximum universe. Every block has positive rank
by `BlockShape.positive`. The statement also includes the empty outer block
family at total rank zero. It uses the Library's upper-parabolic normalization
with positive half-modulus covariance and right translation.

This is an internal intermediate statement for the finite-length proof. Its
mathematical derivation uses the published cuspidal embedding, factorization
of irreducible cuspidal Levi data into supercuspidal GL factors, tensoring of
injections over the complex field, and preservation of injections by normalized
induction. It asserts no finite length and no comparison with an induction
from flattened Levi data. Those conclusions require subsequent results.

The original source for the cuspidal embedding input is Bernstein–Zelevinsky
1977, Theorem 2.5 and Example 2.7, printed p.447 (PDF page 8). Casselman 1995,
Proposition 2.4.4, printed p.28 (PDF page 28), supplies the induction exactness
principle, of which preservation of injections is the part used here. These
passages were read directly. The combination and the independent-universe
formulation are internal to this formalization, rather than a separate quoted
literature theorem. This file only specifies the proposition; a separate
proof is required.

Registered originals:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- `casselman-1995-admissible-representations`, draft 1 May 1995, SHA256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
