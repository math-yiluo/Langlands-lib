# Mixed products and normalized mirabolic minus functors

Author: Worker 593.

This module defines
`Langlands.Derivative.MirabolicProductMinusCompatibilityStatement.{uF,uV} F T`
as a proposition. It states the minus clauses of Bernstein–Zelevinsky (1977),
Proposition 4.13(b,c), naturally in both representation inputs, including the
two boundary clauses for source mirabolic rank one. It supplies no proof of
these comparisons or of the short exact sequence.

## Source and correspondence

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, source ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained PDF is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
The passages read are §1.8, printed pp.444–445 (one-based PDF pages 5–6);
§§3.1–3.2, printed pp.450–451 (PDF pages 11–12); and §§4.12–4.14, printed
pp.456–458 (PDF pages 17–19). Page images were inspected for the normalization
signs, block embeddings, epsilon factor, functoriality and boundary convention.
A bounded filename search in the current Library notes, project notes and
literature found no BZ77-specific errata entry. This is not a global absence
claim.

Section 1.8(a) uses upper-block positive-half covariance for compact induction;
§1.8(b) uses inverse-half normalization for localization. Sections 3.1–3.2
define `Ψ⁻` by localization at the trivial radical character and `Φ⁻` by
localization at the character obtained from a fixed nontrivial additive
character on the final radical coordinate. Section 4.12 defines cases (I),
(II), (III) as binary GL, left mixed and right mixed products. The right
mixed product includes the case (III) factor `ε=ν(ρ)^(-1/2)`.

On printed p.458, 4.13(b) states compatibility with the functors in that
clause, and 4.13(c) gives the right `Ψ⁻` compatibility and the right `Φ⁻`
exact sequence. The sentence following 4.13(d) explicitly makes every
morphism in (a), (b), (c) functorial and sets the convention `P_0=empty`,
with restriction to `P_0` zero. The present module selects only the minus
clauses of (b,c). Its rank-one clauses translate that convention into the
existing positive-rank mirabolic API. Section 4.14 explains how these
comparisons contribute to subsequent derivative calculations; no such
calculation is asserted here.

## Parameters, universes and shifts

All statements use a prime `p`, the actual `F : PadicField.{uF} p`,
supplied `T : F.TopologicalData`, and `letI := T.topology`.
The input representations are arbitrary `SmoothRep.{0,uF,uV} ℂ` objects,
where `uV` is independent of `uF`. Every product has output carrier universe
`max uF uV`; minus functors and rank transports preserve that universe.
`ψ : UnitaryAdditiveCharacter F.Carrier` under `T.topology` already
bundles continuity and nontriviality.

The Lean indices `k r : ℕ` encode positive GL rank `K=k+1` and source
mirabolic rank `m=r+1`. The Library group `mirabolic r F.Carrier` is
`P_(r+1)`. In particular:

| Native functor | Source and target in source notation |
| --- | --- |
| `Mirabolic.psiMinus T r` | `P_(r+1) → GL_r` |
| `Mirabolic.phiMinus T ψ r` | `P_(r+2) → P_(r+1)` |
| `T.leftMixedProductFunctor K r` | `GL_K × P_(r+1) → P_(K+r+1)` |
| `T.rightMixedProductFunctor K r` | `P_(r+1) × GL_K → P_(K+r+1)` |
| `generalLinearRestriction T k` | `GL_(k+1) → P_(k+1)` |

The products and minus functors are the published actual constructions, with
their explicit determinant characters. The module adds no character or
scalar adjustment and suppresses no residual twist.

## The six components

The component definitions are in namespace
`Langlands.Derivative.MirabolicProductMinus`.
`Nonempty (A ≅ B)` means existence of an actual natural isomorphism of
functors on the product category of the two representation inputs.

1. `LeftPsiCompatibility` states
   `Ψ⁻(ρ × τ) ≅ ρ × Ψ⁻τ` for every `K>0`, `m>0`.
   The right side uses `binaryNormalizedProductFunctor K (m-1)`.
2. `LeftPhiCompatibility` states
   `Φ⁻(ρ × τ) ≅ ρ × Φ⁻τ` for `m≥2`.
3. `LeftPhiBoundary` states that `Φ⁻(ρ × τ)` has a subsingleton carrier
   at every pair when `m=1`. Since this is a module carrier, this is
   precisely zero. The product has positive enough rank for its own `Φ⁻`.
4. `RightPsiCompatibility` states
   `Ψ⁻(τ × ρ) ≅ Ψ⁻τ × ρ` for every `K>0`, `m>0`.
   Its binary product retains all of the `GL_0` input when `m=1`.
5. `RightPhiShortExact` states the natural short exact sequence
   `0 → (Φ⁻τ) × ρ → Φ⁻(τ × ρ) → (Ψ⁻τ) × (ρ restricted to P_K) → 0`
   for `m≥2`. It quantifies actual natural transformations `i` and `q`,
   whose component intertwiners satisfy injectivity, equality of the
   linear-map range and kernel, and surjectivity at every object pair.
   Thus the middle composite is zero and the last term is the actual
   quotient up to the supplied exact maps. It is not a statement only
   about classes, characters or subquotient lists.
6. `RightPhiBoundary` states the actual natural isomorphism
   `Φ⁻(τ × ρ) ≅ (Ψ⁻τ) × (ρ restricted to P_K)` when `m=1`.
   The entire `GL_0` carrier of `Ψ⁻τ` remains in the left mixed product.

The named aggregate is their conjunction. The `Ψ⁻` components do not need
`ψ`; the `Φ⁻` components quantify every bundled `ψ`. There is no `P_0`,
no `Φ⁻` on `P_1`, and no rank-zero input GL factor is required.
There are no admissibility, irreducibility, finite-dimension, finite-length,
genericity, universe-saturation, chosen-vector or theorem-valued assumptions.
Zero inputs, repeated factors and arbitrary multiplicities remain covered.

## Concrete helpers and rank transports

Five internal functors expose the terms without assuming comparisons.
Their provenance is composition of published actual constructions and proved
natural-number equalities; these functor names and product-category
packaging are internal and are not attributed verbatim to the source.

`leftPhiProduct T ψ k r` and `rightPhiProduct T ψ k r` compose the
respective mixed product with `mirabolicRankCast T (Nat.succ_add k r)`
and `phiMinus T ψ (k+r)`. The cast identifies the product's index
`(k+1)+r` with `(k+r)+1`. Their common output is `P_(k+r+1)`.

For source `P_(r+2)`, `leftPhiExpected` and `rightPhiSubobject` first
apply `phiMinus T ψ r` to the mirabolic input, form the appropriate mixed
product, and cast `(k+1)+r = k+r+1`. Each lands in `P_(k+r+2)`.
The middle term `rightPhiProduct T ψ k (r+1)` has this same target.

`rightPhiQuotient T k r` applies `psiMinus T r` and
`generalLinearRestriction T k` to the two inputs, forms the left mixed
product with ranks `r,k`, and casts `r+k=k+r`. Its output is
`P_(k+r+1)`. With source `P_(r+2)`, substitute `r+1` to obtain
`P_(k+r+2)`, exactly the other terms' target. With source `P_1`,
substitute `r=0`; the output is `P_(k+1)`.

The right `Ψ⁻` comparison casts the output of the binary product along
`r+(k+1)=(k+1)+r` using `generalLinearRankCast`. The left `Ψ⁻`
comparison already has identical target indices.
Both rank-cast constructions are equality elimination of the identity
functor, including object and morphism transport. No map is discarded.

## Imports and independence

Direct project imports are `Derivative.Homogeneity`,
`Induction.BinaryProduct` and `Mirabolic.MixedProducts` under
`Langlands.Representation`. `Homogeneity` is used solely for
`mirabolicRankCast`; it also imports `Derivative.Iteration`, from which
`generalLinearRestriction` and `generalLinearRankCast` are used.
No homogeneity conclusion is used.

The recursively read actual project import closure has 72 modules, including
these three. It consists of matrix and block-group constructions, local-field
topology and normalization, smooth-category and subquotient constructions,
twists, tensors, actual compact induction and localization, actual mirabolic
characters/minus functors and derivative iteration/homogeneity definitions.
It includes `Tensor.Finite` through `Induction.BlockFactors`; the statement
does not use `FiniteTensor.externalFunctor`. It includes elementary
admissibility/twist infrastructure and algebraic Whittaker character
infrastructure; it includes no Whittaker finiteness result.

There are no segment, multisegment, socle, head, square-integrable, tempered,
classification, product-irreducibility or exhaustion modules in this closure.
The statement uses no mathematical conclusion of the excluded consumers and
has no mathematical proof dependencies for any comparison: those comparisons
are proposition definitions awaiting a separate proof. In particular no
derivative formula, exactness theorem, finiteness result, detection theorem,
geometric lemma or pending statement is used as a proved input.

The separate exact proof successor must preserve every inherited task
restriction directly and transitively and audit each comparison's actual
mathematical proof dependencies. Acceptance of this proposition definition
does not establish the proposition. Plus functors, adjunction, 4.13(d),
Leibniz filtrations, arbitrary-character finiteness, supercuspidal and segment
results remain outside this statement.

### Complete project import inventory

The following inventory excludes this entry module and lists the actual recursively
read project imports; Mathlib imports are omitted.

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
