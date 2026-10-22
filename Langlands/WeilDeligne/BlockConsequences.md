# Numerical consequences of uncentered block operations

Worker 39 supplies proposition definitions supplementing the published
`Langlands.WeilDeligne.BlockStatements` family. No proof of the propositions is
claimed, and no block identity or classification is assumed as an input.

The coefficients are an arbitrary field `K`, the group is arbitrary, and
`ν : G →* Kˣ` is explicit. Only the tensor clause assumes characteristic zero.
The field, group, and two Weil-factor carrier universes are independent.
Positive length is required where the kernel has the same dimension as the
Weil factor. Tensor lengths may be zero; the tensor and its kernel then vanish.

## Exact statements and derivations

Write `d = rank σ`, `e = rank τ` and
`D(σ,m) = (det σ)^m ν^(d · (m(m-1)/2))`. The natural division is exact, because
`m(m-1)` is even. For a positive length, the natural subtraction `m-1` is the
actual top index. All determinants are characters into `Kˣ`, not merely
pointwise scalar equalities. All kernel isomorphisms are actual
`FiniteRepresentation.Equiv` values under `Nonempty`.

| Declaration in `Langlands.WeilDeligneRepresentation.Blocks` | Content |
| --- | --- |
| `BlockNumericalConsequencesFor ν` | For `m>0`, `σ ⊗ S_m` has rank `dm`, determinant `D(σ,m)`, kernel dimension `d`, and kernel representation `ν^(m-1) ⊗ σ`. |
| `DualBlockConsequencesFor ν` | For `m>0`, the actual negative-transpose dual of the block has rank `dm`, determinant `D(σ,m)⁻¹`, kernel dimension `d`, and kernel representation `σ^∨`. |
| `TwistBlockConsequencesFor ν` | For `m>0` and any character `χ`, the twisted block has rank `dm`, determinant `χ^(dm)D(σ,m)`, kernel dimension `d`, and kernel representation `(χ ν^(m-1)) ⊗ σ`. |
| `TensorBlockConsequencesFor ν` | In characteristic zero, the tensor of blocks of lengths `m,n` has rank `(dm)(en)`, determinant `D(σ,m)^(en)D(τ,n)^(dm)`, and kernel dimension `de·min(m,n)`. |
| `BlockOperationConsequences` | The conjunction of the first three universally over fields and groups, and the fourth universally over characteristic-zero fields and groups. |

The uncentered block has weights `ν^j` for `0≤j<m` and raising monodromy.
Thus its rank is `dm`, its determinant is the product of the determinants of
the weight spaces, and its kernel is the top copy of `σ`, of weight `ν^(m-1)`.
This gives the first clause.

For the dual block, the published identity is
`(σ ⊗ S_m)^∨ ≅ (σ^∨ ⊗ ν^(1-m)) ⊗ S_m`, with the integer exponent `1-m`.
Its top kernel is therefore `σ^∨`: the shifts `1-m` and `m-1` cancel.
Equivalently, the kernel of the negative transpose is the dual of the quotient
by the image of `N`, and the block's quotient is its bottom-weight copy of `σ`.
Dualization preserves dimension and inverts the determinant. In particular,
the kernel here is not the dual of the original top-weight kernel.

A twist changes no underlying linear space or monodromy operator. It
multiplies every action by `χ`, so its determinant gains `χ^(dm)` and its
kernel action gains `χ`.

For the tensor clause, dimensions multiply and the determinant of a tensor
of operators of dimensions `dm` and `en` is the product of the two determinants
raised to the opposite dimensions. The published `TensorBlockKernel` target
identifies the kernel with
`⨁_{i<min(m,n)} ν^(m+n-2-i) ⊗ σ ⊗ τ`; every summand has dimension `de`.
The characteristic-zero hypothesis is retained from the full graded
block-tensor decomposition used in this derivation; this is a sufficient
hypothesis, not a claim that it is necessary for the kernel dimension alone.
No irreducibility assumption on `σ`, `τ` or their tensor product is needed.

## Original sources and provenance

These are derived numerical consequences, not verbatim numbered theorems of
the sources. Worker 39 read the original pages in the earlier conversation and
re-read their text on 2026-10-21.

- Tate, *Number theoretic background*, §4.1.2–4.1.5, printed page 20,
  retained `Part II.pdf` page 29: the pair and covariance, the uncentered
  basis and monodromy, and tensor monodromy.
  Literature ID `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- Henniart, *Une caractérisation de la correspondance de Langlands locale
  pour GL(n)*, §2.1–2.4, printed pages 593–594, PDF pages 7–8:
  direct sums, dual block shift `1-m`, graded tensor decomposition, and the
  top-weight exponents of the kernels in the displayed L-factor identities.
  Literature ID `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- Deligne, *Les constantes des équations fonctionnelles des fonctions L*,
  §8.4.1 and §8.5–8.6, retained internal/PDF pages 68 and 70:
  finite-dimensional norm-covariant nilpotent pairs and Frobenius
  semisimplicity, which permits nonzero monodromy.
  Literature ID `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

All originals are retained under `/home/taskhub/central-library/`, as recorded
in the literature index. The determinant rules and dimension formulas above are
elementary derived linear algebra. The kernel representations, rather than
their inertia invariants or L-factors, are asserted here.

Henniart's weight decomposition and sum of tensor blocks are direct sums;
the tensor-like symbols in those positions in the retained printing/OCR
cannot be interpreted as tensor products (the ranks would be wrong).
No centered normalization is used. If a centered block is written as
`ν^((1-m)/2) ⊗ S_m`, returning to this file's convention requires the inverse
scalar shift; no fractional power or choice of square root is introduced in
Lean. Deligne §8.4.3's scaling discussion concerns a nonzero scalar; that
statement is neither used nor restated here.

## Dependencies and validation

The only direct project import is the published
`Langlands.WeilDeligne.BlockStatements`. Its existing propositions are not
assumptions or proofs of this supplement. It supplies access to Worker 17's
actual `block`, `dual`, `twist`, `tensor`, `kernelRepresentation`, and
`FiniteRepresentation.determinantCharacter` constructors, and to genuine
linear-intertwiner isomorphisms. Worker 25's statement module and its dependency
documentation remain unchanged.

The declaration-level dependency map is:

| Targets | Constructors and published related statements |
| --- | --- |
| `BlockNumericalConsequencesFor` | `block`, `kernelRepresentation`, `determinantCharacter`; `rank_block`, `BlockInvariants`. |
| `DualBlockConsequencesFor` | WD and Weil `dual`; `BlockDual` and `BlockInvariants`. |
| `TwistBlockConsequencesFor` | WD and Weil `twist`; `BlockTwist` and `BlockInvariants`. |
| `TensorBlockConsequencesFor` | WD `tensor`; `BlockTensor`, `TensorBlockKernel`, `BlockInvariants`. |
| `BlockOperationConsequences` | Exactly the four definitions in this file. |

The pinned Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`
check completed with zero errors and warnings (diagnostic
`aab11867-83a0-41e3-b02a-0ac161b53508`). The entry is a definition returning
`Prop`, with universe parameters `uK uG uV uW` and only `propext`,
`Classical.choice`, and `Quot.sound` in its inspected assumptions.

- Checked source fingerprint: `618b76f5a1e00b4bebe534b3a44d038ded30655f10e1ab68391f26b8d6dea3f8`.
- Whole declaration type fingerprint: `7eb9c843b0fd71b8fd2d1fabbb34bb5e51c5767a961a5fe1323fb9a277b48cde`.
- Whole proposition expression fingerprint: `3ae4a4aae304b4e3c4624d0db0b4a00d632168a093d16771885a006eeffe9bfe`.

The expression references the component definitions; its fingerprint must be
read together with the source fingerprint, not as a hash of all unfolded bodies.
Independent semantic acceptance and publication remain separate requirements.

Project import source closure in Library `0592c757c0c0cfe8eda5eb1ccc5ea5e38ade5e30`:

| Module | Lean SHA-256 |
| --- | --- |
| `Langlands.Representation.Dual.Definitions` | `53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5` |
| `Langlands.Representation.Twist.Definitions` | `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf` |
| `Langlands.Weil.Representation.Basic` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` |
| `Langlands.Weil.Representation.Determinant` | `9a327d3755e33b6b585efc2f2545583a64239044cb0e9cb99a913fb7116ebac3` |
| `Langlands.Weil.Representation.DirectSum` | `b0d730015d7456225937210ba69093a92e268cdde0454d4ed035742ed27e91e1` |
| `Langlands.Weil.Representation.Dual` | `38cafaca417661df1fd2462cb71fcb880341c4fc561de35797c8b713229a8f74` |
| `Langlands.Weil.Representation.Invariants` | `6b8ce494e92094357b8035f0a2c782cd67be997a7eb420f01a0ae0b7e78bd87f` |
| `Langlands.Weil.Representation.Predicates` | `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148` |
| `Langlands.Weil.Representation.SumsTensor` | `d5ce49ecda33a85b025d201c0cb114a98bbed8c65d36050aa6fc1b55cf42275b` |
| `Langlands.Weil.Representation.Twist` | `cbeda9cff731f24d07c356c7e24e5e9a20a6e248fc9439bc0888cc909ab862c8` |
| `Langlands.WeilDeligne.Basic` | `2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf` |
| `Langlands.WeilDeligne.BlockStatements` | `2f4ab84697214a1da71331d727f2bbbdbd5e5606e9e8e29621eda10dd756718f` |
| `Langlands.WeilDeligne.Determinant` | `c3f623a122f2154873d75bdedf195bffaf7ccf9b2abf31478ef8e4e0aa085091` |
| `Langlands.WeilDeligne.DirectSum` | `a8ec6276d9edcf0f8e811559c982e9ba03deaa2803c7ccaa22c77d26669e6907` |
| `Langlands.WeilDeligne.Dual` | `f93dac4cc8e4a22401bff9a548fca0d3103439ae2c859bcd08d833c9d74f12e9` |
| `Langlands.WeilDeligne.FrobeniusStatements` | `1fb0329d6d33b89fec0770e8e97058265c82526e671ccf19b01c8218ee3ae5aa` |
| `Langlands.WeilDeligne.Kernels` | `fc80f9ec895d5bfbc1ae4b397c799aa657eac45b2a4154be30a0fc8f5d560da6` |
| `Langlands.WeilDeligne.LinearAlgebraStatements` | `31dab68f45eca19af6533a9ae09933e55a974a4027c20c990b066f07fc42eddc` |
| `Langlands.WeilDeligne.Parameters` | `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c` |
| `Langlands.WeilDeligne.SpecialBlocks` | `1280fb510bf4f1d71c707c3b142b404d1d2914d1aacdeee3dff67e81c6312e07` |
| `Langlands.WeilDeligne.SumsTensor` | `b022cece208c2429280b3485628442f05da9e0097cb1fb558448a36bc6e0c06d` |
| `Langlands.WeilDeligne.Twist` | `772f17a7cd090d61a70b7a410aff4b7a0ba14609b5687d378497f696f345faa0` |

Supplement Lean SHA-256: `882512251c0c886ead96098546df17ea54ed75bf938c5c6ca6f2fea1d29f0225`.
