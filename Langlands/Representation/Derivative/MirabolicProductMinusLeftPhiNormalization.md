# Actual left-Phi scalar normalization

Worker 499 constructs `leftPhiSectionCharacter` and proves
`leftPhiSectionCharacter_eq` in
`Langlands.Derivative.MirabolicProductMinus`. This is an internal scalar
normalization calculation on the actual lower left mixed subgroup. It gives
an equality of unit-valued homomorphisms, including the source inverse-half
character. It does not construct a localization or induction equivalence,
a natural isomorphism, or any of the six conclusions of the mixed-product
minus compatibility statement.

## Source and provenance

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b), printed pp.444–445 (one-based PDF pages 5–6), defines
normalized localization using the exponent `-1/2`. Sections 3.1–3.2,
printed pp.450–451 (PDF pages 11–12), define the mirabolic group and the
minus functors. Section 4.12(II), printed pp.456–457 (PDF pages 17–18),
defines the left mixed product, and §4.13(b), printed p.458 (PDF page 19),
states its compatibility with Phi-minus. These passages and their page
images were read during this task. The bounded supplied-source and public
note search found no applicable BZ77 errata entry; no global absence claim
is made.

The present homomorphism and its proof are derived internal content. They
use the published explicit determinant-normalized conventions in
`MirabolicMinus` and `MixedProducts`. No result identifying a Haar modulus
with a determinant norm is asserted or needed here. In particular this
scalar calculation is not a proof of the source's representation
comparison. The successor determinant identity reuses Worker 593's published
`JacquetNormalization.determinant_successor`, extracted unchanged with its
two supporting determinant lemmas into `MirabolicDeterminant`. The
real-exponent argument adapts Worker 499's own elementary argument in the
earlier left-Psi induction helper, without importing that helper or any
compatibility conclusion. No peer draft is an input.

## Parameters and actual groups

The algebraic determinant lemmas quantify an arbitrary commutative ring
`R : Type u` and all natural indices. The normalization section quantifies
`{p : ℕ} [Fact p.Prime]`, `{F : PadicField.{uF} p}` and the supplied
`T : F.TopologicalData`. Its determinant norm is exactly
`T.determinantNorm`; no canonical topology or different absolute value is
substituted. The formula itself needs no topology instance or additive
character parameter.

Here `k` is the actual GL rank, while `mirabolic r R` is `P_(r+1)`.
For every `h : leftSubgroup k r R`, set

```text
(a, q) = leftProjection h ∈ GL_k(R) × P_(r+1)(R).
```

The domain is the published actual upper-block subgroup of
`P_(k+r+1)(R)`. Its matrix is upper block triangular with diagonal blocks
`a` and the entire underlying `GL_(r+1)` element of `q`.
`successor q` is the published embedding `diag(q, 1)` into `P_(r+2)`.
All `k,r : ℕ`, including zero, are retained. To apply this calculation to
the host's positive-rank GL factor, substitute its GL rank `K = k_host+1`
for this module's `k`. There are no representations or carrier-universe
restrictions in this scalar unit, and no fictitious `P_0` is introduced.

The relevant functor indexing is `phiMinus T ψ r : P_(r+2) → P_(r+1)`.
Consequently `phiMinusCharacter T r` is a character of the output
`P_(r+1)`. The ambient output here is `P_(k+r+1)`, and its character is
`phiMinusCharacter T (k+r)`.

## Definition and exact identity

Write `ν` for the supplied determinant norm in the appropriate GL rank,
`λ_(k,r) = T.leftLeviCharacter k r`, and
`α_n = Mirabolic.phiMinusCharacter T n`. The published definitions give

```text
λ_(k,r)(a,q) = ν(a)^((r+1)/2) ν(q)^(-k/2),
α_n(g)       = ν(g)^(-1/2).
```

These are complex unit-valued homomorphisms, with positive real powers
embedded in the complex numbers. The new definition is precisely

```text
leftPhiSectionCharacter T k r (h)
  = α_(k+r)(h) λ_(k,r+1)(a, successor q).
```

It is the product of the ambient character composed with the actual
subgroup inclusion and the higher left coefficient character composed
with `id.prodMap successor` after the actual `leftProjection`.
`leftPhiSectionCharacter_apply` records this evaluation by reflexivity.
No assumed identification of inducing representations enters the definition.

The theorem `leftPhiSectionCharacter_eq` proves the equality of the
complete homomorphisms

```text
leftPhiSectionCharacter T k r
  = (λ_(k,r) ∘ leftProjection)
      * (α_r ∘ snd ∘ leftProjection).
```

Thus its pointwise value is `λ_(k,r)(a,q) α_r(q)` with no residual scalar.
The second factor uses the entire `q`, not a discarded block or a chosen
unit. This is only the character arithmetic for the explicit successor
pair `(a, successor q)`. Relating this pair to orbit sections, constructing
the surviving localization comparison and proving naturality remain
separate obligations.

## Implemented proofs

The shared `JacquetNormalization.determinant_successor` proves the
unit-valued equality `det(successor q) = det(q)` by the determinant of the
actual block sum with a scalar identity. Applying `T.normalizedAbsUnits`
gives `determinantNorm_successor_for_leftPhi`.

`leftPhiSubgroup_determinant` reindexes the actual matrix of `h` by
`leftIndex`. Determinant is unchanged by simultaneous row and column
reindexing. `TwoBlock.display` writes the result as an actual block
matrix with zero lower-left block; `Matrix.det_fromBlocks_zero₂₁` gives

```text
det(h) = det(a) det(q).
```

The proof is first an equality of determinant units, by `Units.ext`.
`leftPhiSubgroup_determinantNorm` applies the supplied multiplicative
normalized absolute value to obtain `ν(h) = ν(a) ν(q)`.
Neither proof assumes that `h` is a selected block-diagonal representative;
they quantify every element of the actual subgroup.

The private scalar lemma takes arbitrary `x,y : ℝ≥0ˣ`. Their real values
are strictly positive. `Real.mul_rpow` distributes the exponent `-1/2`
over `xy`. `Real.rpow_add` and elementary ring arithmetic give

```text
x^(-1/2) x^((r+2)/2) = x^((r+1)/2).
```

Commutativity arranges the remaining factors as
`x^((r+1)/2) y^(-k/2) y^(-1/2)`. In the final theorem,
`MonoidHom.ext` and `Units.ext` reduce the character equality to this
scalar lemma after expanding the published character formulas and the
two determinant norm identities. Hence the conclusion is equality in
`ℂˣ`, not merely an informal equality of exponents.

## Import and mathematical dependency audit

The direct project imports are
`Langlands.Representation.Mirabolic.MixedProducts`,
`Langlands.Representation.Derivative.MirabolicMinus` and the shared
`Langlands.Representation.Derivative.MirabolicDeterminant`. The complete
71-module project closure below was reconstructed from import directives.
The original 70 imported pairs match the published Library at commit
`8f53f05bb76983088fd64f190658c6ac4c3edc1b`. The additional shared pair
contains the three unchanged elementary determinant lemmas extracted from
Worker 593's published `PartialDerivativeJacquetNormalization`. Its
project imports were already in the original closure; neither derivative
iteration nor the Jacquet comparison is introduced by this extraction.
The original independence findings are preserved.

The direct mathematical project inputs are the actual mixed subgroup,
its block projection and display, the actual successor determinant
identity, the supplied multiplicative normalized determinant norm, and
the two explicit character evaluation formulas. The new proofs use only
matrix reindexing and block determinants,
homomorphism and unit extensionality, positivity of real units, real-power
laws and ring arithmetic. The induction, localization, category, tensor
and smoothness constructions present in the import closure provide no
representation-comparison conclusion to this proof. The Whittaker
modules there supply algebraic character infrastructure, not coinvariant
finiteness. Proposition definitions in the closure do not supply their
unproved conclusions.

The following audit applies directly and transitively to every condition
in the host task's inherited upstream restrictions.

| Condition | Actual dependency finding |
| --- | --- |
| Six mixed-minus host conclusions | None is an input. The final compatibility statement and its proof module are not imported. This scalar unit proves none of the six representation-level clauses. |
| Plus functors, adjunction and BZ77 §4.13(d) | No plus functor, adjunction or submodule-detection conclusion is imported or used. The successor matrix embedding is an elementary group homomorphism. |
| General Leibniz and derivative formulas | No Leibniz filtration, unproved BZ77 comparison, Ze80 §3.5 or §9.6 derivative formula, or segment derivative conclusion is used. The minus module supplies its character definition only. |
| Segment head, socle and Jacquet formulas | No individual head/socle existence, unlinked or linked segment-socle conclusion, juxtaposed reverse-product structure, reverse-product quotient homomorphism, or full/head/socle/special Jacquet formula is used. |
| Segment product, commutation and gluing | No `SegmentSocleProductIrreducibility`, adjacent socle swap, two-segment commutation, linked-segment gluing, or Ze80 4.2 or 9.7 criterion supplies an input. |
| Special-head criterion and generic uniqueness | Neither `SegmentHeadProductIrreducibility` nor `GenericSegmentProductUniqueness` supplies an input. |
| Ordered existence and exhaustion | No ordered multisegment-socle existence, socle exhaustion, ordered strong-head existence, special-head multisegment exhaustion, quotient coverage or ordered conversion supplies an input. |
| Analytic, tempered and square-integrable conclusions | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable or regular exhaustion, or Ze80 9.3 conclusion supplies an input. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility, two-supercuspidal product structure nor its full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and single-block finiteness | No supercuspidal coinvariant-finiteness statement, all-character single-block conclusion, arbitrary-character finiteness theorem or consequence supplies an input. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion, downstream consequence, or mirabolic finite-length route through the prohibited finiteness is used. |
| Generality and normalization | The ring lemmas and scalar identity cover every natural `k,r`, including zero. The entire source block and supplied `T` are retained. There is no finite-dimensional, admissible, irreducible, finite-length or generic representation premise, no canonical topology, no selected vector and no theorem-valued assumption. |
| Published-input requirement | The original imported pairs are published and unchanged; the shared determinant pair contains unchanged proofs extracted from the published Jacquet normalization module. Citations, proposition definitions, pending comparison statements and consumer tasks supply no theorem premise. Only the displayed elementary algebra proves this identity. |
| Separate owners and user controls | This unit adds scalar arithmetic only and does not duplicate the restriction-sequence or exactness owners. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding; no peer message waives them. |

The source scan of this module and its entire project closure finds no
occurrence in Lean code of the host's 38 excluded task identifiers or
24 named consumer declarations, and no proof holes, new axioms or unsafe
evaluation commands. Excluded names in paired explanatory Markdown are
audit prose, not proof inputs. Declaration inspection of
`leftPhiSectionCharacter_eq` reports only the field universe `uF` and the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. Development
compilation and this audit are not independent acceptance or publication.

## Complete project import closure

The list includes both direct roots and every transitive project import,
excluding the present module. Mathlib is supplied by the pinned environment;
no Mathlib source was modified.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
