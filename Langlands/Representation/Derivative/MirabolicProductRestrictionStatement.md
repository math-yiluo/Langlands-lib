# Restriction of a binary product to the mirabolic subgroup

Author: Worker 1129.

This module defines
`Langlands.Derivative.MirabolicProductRestrictionStatement.{uF,uV} F T`
as a proposition. It states Bernstein–Zelevinsky (1977), Proposition 4.13(a),
as a natural short exact sequence on the product category of smooth
representations of `GL_a(F)` and `GL_b(F)`, for every pair of positive ranks
`a, b`. It supplies no proof of the sequence.

## Source and correspondence

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, source ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained PDF is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
The passages read are §1.8, printed pp.444–445 (one-based PDF pages 5–6);
§§3.1–3.2, printed pp.450–451 (PDF pages 11–12); and §§4.12–4.14, printed
pp.456–458 (PDF pages 17–19). The complete image of printed p.458 was
inspected, including the case (III) block description, the statement of 4.13
and the functoriality and boundary sentence after 4.13(d). A bounded filename
search in the current Library notes, project notes and literature found no
BZ77-specific errata entry. This is not a global absence claim.

Proposition 4.13 takes `ρ ∈ Alg G_k` and `σ ∈ Alg G_m`. Clause (a) reads:
in `Alg P_(k+m)` there exists an exact sequence
`0 → (ρ|_P) × σ → (ρ × σ)|_P → ρ × (σ|_P) → 0`.
The sentence after 4.13(d) states that all morphisms in (a), (b), (c) are
functorial, and sets the convention `P_0 = ∅`, `ρ|_(P_0) = 0`.
The three products are those of §4.12. The middle product is case (I), the
binary product of `GL_k` and `GL_m` representations. The first term
`(ρ|_P) × σ` has a mirabolic first factor and a `GL` second factor, which
is case (III). The last term `ρ × (σ|_P)` has a `GL` first factor and a
mirabolic second factor, which is case (II). Restriction to `P` is
restriction along the inclusion `P_n ⊂ G_n`.

This module states clause (a) only for positive `k` and `m`, which are `a`
and `b` here. It does not introduce a fictitious `P_0`; the rank-zero
`GL` boundary belongs to separate all-rank filtration work. Clauses (b)–(d)
and Corollary 4.14 are not stated here.

## Parameters, universes and ranks

All statements use a prime `p`, the actual `F : PadicField.{uF} p`,
supplied `T : F.TopologicalData`, and `letI := T.topology`.
The input representations are arbitrary `SmoothRep.{0,uF,uV} ℂ` objects,
where `uV` is independent of `uF`. All three terms have output carrier
universe `max uF uV`; restriction and rank transports preserve universes.
The inspected level parameters are `[uF, uV]`.

The Lean indices `m n : ℕ` encode the positive ranks `a = m+1` and
`b = n+1`. As `m` and `n` range over all of `ℕ`, this covers every positive
pair `(a, b)` exactly once. The Library group `mirabolic r F.Carrier` is
the source's `P_(r+1)`. The common target `mirabolic (m+n+1) F.Carrier`
is `P_(a+b)`, which is `mirabolic (a+b-1)` in the task's indexing.

| Native functor | Source and target in source notation |
| --- | --- |
| `generalLinearRestriction T r` | `GL_(r+1) → P_(r+1)` |
| `T.binaryNormalizedProductFunctor a b` | `GL_a × GL_b → GL_(a+b)` |
| `T.leftMixedProductFunctor K r` | `GL_K × P_(r+1) → P_(K+r+1)` |
| `T.rightMixedProductFunctor K r` | `P_(r+1) × GL_K → P_(K+r+1)` |
| `generalLinearRankCast T h` | `GL_s → GL_t` for `h : s = t` |
| `mirabolicRankCast T h` | `P_(s+1) → P_(t+1)` for `h : s = t` |

The products are the published actual constructions with their explicit
normalizations. `binaryNormalizedProductFunctor` at positive ranks is the
published normalized product on the binary block shape. The mixed products
use the published upper-block positive-half normalized compact induction.
The right mixed product includes the case (III) factor
`ε(m₁,m₂) = ν(m₂)^(-1/2)`, where `m₂` lies in the `GL` factor; in the first
term this is the group of the second input `B`.
`generalLinearRestriction` is the actual pullback along the subgroup
inclusion `P_(r+1) ⊂ GL_(r+1)`. This module adds no character or scalar
adjustment and suppresses no residual twist.

## The three terms

The helper functors are in namespace
`Langlands.Derivative.MirabolicProductRestriction`. Each has source
`SmoothRep ℂ (GL_(m+1)) × SmoothRep ℂ (GL_(n+1))` and target
`SmoothRep.{0,uF,max uF uV} ℂ (mirabolic (m+n+1) F.Carrier)`.

1. `restrictedProduct T m n` is `(A × B)|P_(a+b)`. It is
   `binaryNormalizedProductFunctor (m+1) (n+1)`, then
   `generalLinearRankCast` along `(m+1)+(n+1) = (m+n+1)+1`, then
   `generalLinearRestriction T (m+n+1)`.
2. `restrictionSubobject T m n` is `(A|P_a) × B`. It applies
   `generalLinearRestriction T m` to the first input and the identity to the
   second, then `rightMixedProductFunctor (n+1) m`, then
   `mirabolicRankCast` along `(n+1)+m = m+n+1`. In the task's indexing this
   is `rightMixedProductFunctor b (a-1)`.
3. `restrictionQuotient T m n` is `A × (B|P_b)`. It applies the identity to
   the first input and `generalLinearRestriction T n` to the second, then
   `leftMixedProductFunctor (m+1) n`, then `mirabolicRankCast` along
   `(m+1)+n = m+n+1`. In the task's indexing this is
   `leftMixedProductFunctor a (b-1)`.

The functor names and product-category packaging are internal. Their
provenance is composition of the published actual constructions with
proved natural-number equalities, chosen to match the three terms of
4.13(a). Both rank-cast constructions are equality elimination of the
identity functor, with object and morphism transport. No map is discarded.

## The statement

`MirabolicProductRestrictionStatement F T` states: for all `m n : ℕ`, there
exist natural transformations
`i : restrictionSubobject T m n ⟶ restrictedProduct T m n` and
`q : restrictedProduct T m n ⟶ restrictionQuotient T m n` such that, at every
object `X = (A, B)` of the product category, the underlying intertwiners
satisfy:

- `SmoothRep.hom (i.app X)` is injective;
- the linear-map range of `i.app X` equals the linear-map kernel of
  `q.app X`;
- `SmoothRep.hom (q.app X)` is surjective.

This is the predicate used by the published
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact`.
The range–kernel equality includes `q ∘ i = 0` and exactness in the middle.
Naturality of `i` and `q` gives functoriality in both representations and in
all pairs of maps, as the source asserts. The statement is not about classes
in a Grothendieck group, characters, semisimplifications or subquotient lists.

There are no admissibility, irreducibility, finite-dimension, finite-length,
genericity, universe-saturation, chosen-vector, canonical-topology or
theorem-valued assumptions. Zero inputs, repeated factors and arbitrary
multiplicities remain covered.

## Imports and independence

Direct project imports are `Derivative.Homogeneity`,
`Induction.BinaryProduct` and `Mirabolic.MixedProducts` under
`Langlands.Representation`. `Homogeneity` is used solely for
`mirabolicRankCast`; it also imports `Derivative.Iteration`, from which
`generalLinearRestriction` and `generalLinearRankCast` are used.
No homogeneity or iteration conclusion is used.

The recursively read actual project import closure has 72 modules, listed
below. It consists of matrix and block-group constructions, local-field
topology and normalization, smooth-category and subquotient constructions,
twists, tensors, actual compact induction and localization, actual mirabolic
characters and minus functors, and derivative iteration and homogeneity
definitions. It includes `Tensor.Finite` through `Induction.BlockFactors`;
the statement does not use `FiniteTensor.externalFunctor`. It includes
elementary admissibility and twist infrastructure and algebraic Whittaker
character infrastructure. It includes no Whittaker finiteness result.

There are no segment, multisegment, socle, head, square-integrable, tempered,
classification, product-irreducibility, exhaustion or two-supercuspidal
modules in this closure. The statement uses no mathematical conclusion of the
excluded consumers. It has no mathematical proof dependencies: the sequence is
a proposition definition awaiting a separate proof. In particular no
derivative formula, exactness theorem, finiteness result, geometric lemma or
pending statement is used as a proved input.

The separate exact proof successor must preserve every inherited task
restriction directly and transitively and audit its actual mathematical proof
dependencies. Acceptance of this proposition definition does not establish
the proposition.

### Complete project import inventory

The following inventory excludes this entry module and lists the actual
recursively read project imports; Mathlib imports are omitted.

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
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
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
Langlands.Topology.Nonarchimedean.Subgroup
```
