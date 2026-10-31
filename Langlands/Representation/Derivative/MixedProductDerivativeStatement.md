# Minus functors and derivatives of mirabolic mixed products

Authors: Worker 999 (the supplied Lean draft) and Worker 1012 (independent source,
rank and import audit, paired English statement, and validation).

This module defines four propositions about the actual smooth mixed products,
minus functors and derivatives already in the Library. It proves none of these
propositions. In particular, stating either natural isomorphism or nonvanishing
provides no proof input for a consumer.

## Original source and correspondence

The registered original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Printed page numbers are one-based PDF page numbers plus 439.

- §3.2, printed pp.450–451 (PDF pp.11–12), fixes a nontrivial additive
  character and the normalized minus functors.
- §3.5 and footnote (2), printed p.452 (PDF p.13), define the order-`i`
  derivative of a representation of `P_m` as `i-1` successive `Φ⁻` functors
  followed by `Ψ⁻`, with target `GL_(m-i)`.
- §4.12(II), printed pp.457–458 (PDF pp.18–19), defines the left mixed
  product `ρ × τ`, with `ρ` on `GL_k` and `τ` on `P_m`, as a representation
  of `P_(k+m)`. §4.12(III) defines the right mixed product `τ × ρ`, including
  its additional inverse-half determinant factor on the GL factor.
- Proposition 4.13(d), printed p.458 (PDF p.19), asserts nonvanishing under
  `Φ⁻` of every nonzero invariant subspace of `τ × ρ` when the GL rank is
  positive. This is `RightMixedProductPhiMinusDetection` below, with the
  source GL rank written `k+1` and `m=r+1`.
- Corollary 4.14(a), printed p.458 (PDF p.19), identifies the positive-order
  derivative of `ρ × τ` with `ρ × τ^{(i)}`. The source identifies these
  functors naturally (§4.13), rather than only their representation classes.
  Its convention `P_0=0` accounts for vanishing when `i>m`. The two order
  ranges are `LeftMixedProductDerivativeIso` and
  `LeftMixedProductDerivativeVanishing`; their conjunction is
  `LeftMixedProductDerivative`.
- §7.3, printed p.471 (PDF p.32), proves 4.13(d) using compact support
  modulo the inducing subgroup and the noncompact radical orbit for positive
  GL rank. The sentence following 4.14(a) attributes it to 4.13(b), whose
  geometric-lemma argument is in §7.2 on printed p.471. These are proof
  locators, not proofs implemented in this module.

The author independently read PDF pp.11–13, 18–19 and 32 and visually checked
pp.18–19 and 32, including the product directions and normalization. A bounded
search of the project/Library source-specific notes found no applicable BZ77
erratum; this is no claim about all possible errata. The rank/order splitting,
`Nonempty` packaging and conjunction below are internal formal packaging of
these source assertions, rather than additional source theorems.

## Parameters, carriers and actual constructions

Each definition has outer parameters `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`. It installs
`letI := T.topology`. The carrier universe `uV` is independent of `uF`.
Each `ψ : UnitaryAdditiveCharacter F.Carrier` is continuous, unitary and
nontrivial, for this supplied topology. No canonical topology is chosen.

All inputs are actual smooth complex representations in
`SmoothRep.{0,uF,uV} ℂ _`. They may be zero, have arbitrary dimension, and
need not be admissible, irreducible, finite length or generic. All ranks are
natural numbers. `GeneralLinear.mirabolic r F.Carrier` denotes `P_(r+1)`;
there is no mirabolic group `P_0` in these interfaces. An arbitrary
representation of `GL_0`, including a carrier of any allowed dimension, is
permitted wherever rank zero occurs. There is no restriction to the scalar
unit representation. The mixed and binary products have carrier universe
`max uF uV`; rank casts and minus functors preserve the carrier universe at
which they are applied.

The imported constructions are concrete functors on these categories:

- `T.leftMixedProductFunctor k r` sends `(A,B)` on `GL_k × P_(r+1)` to
  `A × B` on `P_(k+r+1) = mirabolic (k+r)`.
- `T.rightMixedProductFunctor k r` sends `(B,A)` on `P_(r+1) × GL_k` to
  `B × A` on the same target. These are the normalized compact inductions
  of pulled-back actual external tensors specified in `MixedProducts`.
- `Mirabolic.phiMinus T ψ n` goes from `P_(n+2)` to `P_(n+1)`;
  `Mirabolic.psiMinus T n` goes from `P_(n+1)` to `GL_n`.
- `mirabolicDerivativeOfOrder T ψ N i hi`, where
  `hi : 0<i ∧ i≤N+1`, goes from `P_(N+1)` to `GL_(N+1-i)`. It first
  transports along `N=(N+1-i)+(i-1)`, then takes `i-1` actual `Φ⁻` steps
  followed by the actual `Ψ⁻`.
- `mirabolicRankCast T h` and `generalLinearRankCast T h` are equality
  elimination (`Eq.rec`) of identity functors, including transport on
  morphisms. `T.binaryNormalizedProductFunctor k m` is the actual binary
  normalized product from `GL_k × GL_m` to `GL_(k+m)`.

Write `ν_n=T.determinantNorm n`. The left inducing character is
`ν_k(a)^((r+1)/2) ν_(r+1)(q)^(-k/2)`. The right inducing character is
`ν_r(projection q)^(k/2) ν_k(a)^(-(r+1)/2)`. The latter is explicitly
factored by `rightLeviCharacter_eq_mul` as the rectangle half character
`ν_r(projection q)^(k/2) ν_k(a)^(-r/2)` times the case (III) factor
`ν_k(a)^(-1/2)`. Each minus functor twists its descended output by the
inverse-half determinant character: `ν_n^(-1/2)` for `Ψ⁻` on `GL_n`, and
the restriction of `ν_(n+1)^(-1/2)` for `Φ⁻` on `P_(n+1)`. No character
factor is discarded, and the propositions use these actual normalized
functors, not their unnormalized counterparts.

These explicit determinant characters are the inherited Library convention.
The imported construction pairs do not prove their comparison with an actual
Haar-measure modulus in the source normalization. This module neither assumes
nor proves that comparison. Any future proof using such an identification
must justify it independently; it cannot remove a residual twist by citation.

## Right mixed product detection: 4.13(d)

`Langlands.Derivative.RightMixedProductPhiMinusDetection.{uF,uV} F T` says:
for every `ψ`, all `k r : ℕ`, every `B` on `P_(r+1)` and every `A` on
`GL_(k+1)`, and every actual subrepresentation

```lean
U : Subrepresentation
  ((T.rightMixedProductFunctor (k+1) r).obj (B,A)).representation
```

with `U ≠ ⊥`, the carrier of its image under `Φ⁻` is `Nontrivial`.
The source GL rank `k+1` encodes exactly the positive-rank hypothesis.
The right mixed product has mirabolic index `(k+1)+r`, and hence group
`P_((k+1)+r+1)`. Its restricted smooth representation
`SmoothRep.subrepresentation _ U` is transported by
`mirabolicRankCast T (Nat.add_right_comm k 1 r)`, along
`k+1+r=k+r+1`, to the source of `Mirabolic.phiMinus T ψ (k+r)`.
That functor lands on mirabolic index `k+r`, namely `P_(k+r+1)`.
`Nontrivial` refers to the actual quotient carrier. The assertion quantifies
over all invariant subspaces, not only the whole product. It has no chosen
nonzero vector among its parameters. If either factor is zero, its same
universal assertion still applies, with the nonbottom condition on `U`.

## Left mixed product derivatives: 4.14(a)

`Langlands.Derivative.LeftMixedProductDerivativeIso.{uF,uV} F T` says:
for every `ψ`, `k r i : ℕ` and `hi : 0<i ∧ i≤r+1`, there exists a natural
isomorphism between the following functors, whose common source is the full
product category of smooth representations of `GL_k` and `P_(r+1)`:

```lean
T.leftMixedProductFunctor k r ⋙
  mirabolicDerivativeOfOrder T ψ (k+r) i ⟨hi.1, by omega⟩ ⋙
    generalLinearRankCast T
      (show k+r+1-i = k+(r+1-i) by omega)
```

and

```lean
(𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi) ⋙
  T.binaryNormalizedProductFunctor k (r+1-i)
```

Their common target is the category of smooth representations of
`GL_(k+(r+1-i))`, at carrier universe `max uF uV`. The left derivative
initially lands on `GL_(k+r+1-i)`; the displayed proved natural-number
equality supplies the actual target rank cast. The product derivative is
valid because `i≤r+1≤k+r+1`. The right functor leaves the first factor
unchanged and differentiates the second, which lands on `GL_(r+1-i)`.
`Nonempty (L ≅ R)` asserts existence of a natural isomorphism for all
objects and morphisms simultaneously. It includes naturality in both
factors and asserts neither just an objectwise isomorphism nor a
Grothendieck-group, character or semisimplification identity.

The range includes `k=0`, `r=0` and `i=r+1`; in the last case the second
factor's derivative is an arbitrary actual representation of `GL_0`.
There is no derivative of order zero in this assertion.

`Langlands.Derivative.LeftMixedProductDerivativeVanishing.{uF,uV} F T`
says: for every `ψ`, all `k r i : ℕ`, a proof
`hi : 0<i ∧ i≤k+r+1`, and `r+1<i`, and for every `A` on `GL_k` and `B`
on `P_(r+1)`, the carrier of

```lean
(mirabolicDerivativeOfOrder T ψ (k+r) i hi).obj
  ((T.leftMixedProductFunctor k r).obj (A,B))
```

is `Subsingleton`. This is a zero vector space carrier, since every complex
representation carrier contains zero. The output is on `GL_(k+r+1-i)`;
no further rank cast is needed for carrier vanishing. The source convention
that the second factor's derivative is zero above its rank is encoded here
without defining an invalid-order derivative of `B` or a group `P_0`.
For `k=0` the two inequalities make this order range empty. For `k>0` it
includes the top order `i=k+r+1`, whose target is `GL_0`.

Finally, `Langlands.Derivative.LeftMixedProductDerivative.{uF,uV} F T` is
exactly the conjunction of these two propositions. Together they cover
all positive valid derivative orders of the left mixed product. They do
not make an assertion at orders above its own rank.

## Dependency and independence audit

The two direct project imports are
`Langlands.Representation.Mirabolic.MixedProducts` and
`Langlands.Representation.Derivative.Homogeneity`. The following is the
complete transitive project import graph at Library commit
`c5eebf94883144ce00adc4e252995c28082f08a7`, excluding this new module and
Mathlib: 73 modules and their 146 Lean/Markdown files. Each imported pair
was checked byte-for-byte against that Library tree; none is changed.
An empty right column means no further project import, not no Mathlib
import. Names in the table are full Lean module names.

| Module | Direct project imports |
| --- | --- |
| `Langlands.Group.GL.Basic` | — |
| `Langlands.Group.GL.BlockModulus` | `Langlands.Group.GL.PadicBlocks`, `Langlands.Group.GL.NormalizedCharacter`, `Langlands.Representation.Jacquet.PositiveCharacter` |
| `Langlands.Group.GL.Blocks` | `Langlands.Group.GL.Basic` |
| `Langlands.Group.GL.Mirabolic` | `Langlands.Group.GL.UpperUnipotent` |
| `Langlands.Group.GL.MirabolicMixedProductSubgroups` | `Langlands.Group.GL.MirabolicProjection` |
| `Langlands.Group.GL.MirabolicOppositeIntersection` | `Langlands.Group.GL.Mirabolic`, `Langlands.Group.GL.OppositeBlocks` |
| `Langlands.Group.GL.MirabolicProjection` | `Langlands.Group.GL.MirabolicRadical` |
| `Langlands.Group.GL.MirabolicRadical` | `Langlands.Group.GL.Mirabolic`, `Langlands.Group.GL.RankMaps` |
| `Langlands.Group.GL.Nonarchimedean` | `Langlands.Group.GL.NonarchimedeanStatement` |
| `Langlands.Group.GL.NonarchimedeanStatement` | — |
| `Langlands.Group.GL.NormalizedCharacter` | `Langlands.Group.GL.Padic`, `Langlands.LocalField.Normalization.Proof`, `Langlands.Topology.CompactNormCharacter` |
| `Langlands.Group.GL.OppositeBlocks` | `Langlands.Group.GL.Blocks` |
| `Langlands.Group.GL.Padic` | `Langlands.Group.GL.Basic`, `Langlands.LocalField.Canonical`, `Langlands.LocalField.Topology` |
| `Langlands.Group.GL.PadicBlocks` | `Langlands.Group.GL.Blocks`, `Langlands.Group.GL.Padic` |
| `Langlands.Group.GL.RankMaps` | `Langlands.Group.GL.Basic`, `Langlands.Group.GL.Padic` |
| `Langlands.Group.GL.RankReindex` | `Langlands.Group.GL.Basic` |
| `Langlands.Group.GL.UpperUnipotent` | `Langlands.Group.GL.Basic` |
| `Langlands.HarmonicAnalysis.Basic` | — |
| `Langlands.LocalField.Canonical` | `Langlands.LocalField.Definitions` |
| `Langlands.LocalField.Definitions` | — |
| `Langlands.LocalField.Normalization.Definitions` | `Langlands.LocalField.Definitions` |
| `Langlands.LocalField.Normalization.Proof` | `Langlands.LocalField.Normalization.Statement` |
| `Langlands.LocalField.Normalization.Statement` | `Langlands.LocalField.Normalization.Definitions` |
| `Langlands.LocalField.Topology` | `Langlands.LocalField.Definitions` |
| `Langlands.Representation.Category.Basic` | `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Category.Subquotients` | `Langlands.Representation.Category.Basic`, `Langlands.Representation.Smooth.Transfer.SubquotientProof` |
| `Langlands.Representation.Category.Twist` | `Langlands.Representation.Category.Basic`, `Langlands.Representation.Twist.AdmissibilityProof`, `Langlands.Representation.Twist.AlgebraProof`, `Langlands.Representation.Twist.SubquotientProof` |
| `Langlands.Representation.Derivative.Homogeneity` | `Langlands.Representation.Derivative.Iteration`, `Langlands.Representation.Category.Subquotients` |
| `Langlands.Representation.Derivative.Iteration` | `Langlands.Representation.Derivative.MirabolicMinus` |
| `Langlands.Representation.Derivative.MirabolicCharacter` | `Langlands.Group.GL.MirabolicRadical`, `Langlands.Group.GL.Nonarchimedean`, `Langlands.Topology.Nonarchimedean.Subgroup`, `Langlands.Representation.Jacquet.Localization`, `Langlands.Representation.Whittaker.GeneralLinear`, `Langlands.Representation.Twist.ContinuousCharacterProof` |
| `Langlands.Representation.Derivative.MirabolicMinus` | `Langlands.Representation.Derivative.MirabolicCharacter`, `Langlands.Representation.Category.Twist`, `Langlands.Representation.Twist.RealPower`, `Langlands.Representation.Smooth.Transfer.PullbackProof`, `Langlands.Group.GL.NormalizedCharacter` |
| `Langlands.Representation.Dual.Definitions` | — |
| `Langlands.Representation.Induction.BinaryProduct` | `Langlands.Representation.Tensor.OneFactor`, `Langlands.Group.GL.MirabolicOppositeIntersection`, `Langlands.Group.GL.RankReindex`, `Langlands.Representation.Induction.BlockFactors`, `Langlands.Representation.Smooth.Transfer.SubquotientProof` |
| `Langlands.Representation.Induction.BlockFactors` | `Langlands.Representation.Induction.Parabolic`, `Langlands.Representation.Tensor.Finite` |
| `Langlands.Representation.Induction.Definitions` | `Langlands.Representation.Category.Basic`, `Langlands.Representation.Smooth.SmoothPart.Definitions`, `Langlands.Representation.Twist.Definitions` |
| `Langlands.Representation.Induction.Parabolic` | `Langlands.Group.GL.BlockModulus`, `Langlands.Representation.Category.Basic`, `Langlands.Representation.Induction.Definitions` |
| `Langlands.Representation.Jacquet.Coinvariants` | — |
| `Langlands.Representation.Jacquet.Localization` | `Langlands.Representation.Jacquet.SmoothTwist`, `Langlands.Representation.Category.Basic` |
| `Langlands.Representation.Jacquet.PositiveCharacter` | — |
| `Langlands.Representation.Jacquet.SmoothTwist` | `Langlands.Representation.Jacquet.Coinvariants`, `Langlands.Representation.Smooth.Transfer.PullbackProof`, `Langlands.Representation.Smooth.Transfer.SubquotientProof`, `Langlands.Representation.Twist.SmoothProof` |
| `Langlands.Representation.MatrixCoefficient.Definitions` | — |
| `Langlands.Representation.MatrixCoefficient.LawsProof` | `Langlands.Representation.MatrixCoefficient.LawsStatement` |
| `Langlands.Representation.MatrixCoefficient.LawsStatement` | `Langlands.Representation.MatrixCoefficient.Definitions`, `Langlands.Representation.Dual.Definitions`, `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Mirabolic.MixedProducts` | `Langlands.Group.GL.MirabolicMixedProductSubgroups`, `Langlands.Group.GL.NormalizedCharacter`, `Langlands.Representation.Induction.BinaryProduct`, `Langlands.Representation.Induction.Definitions`, `Langlands.Representation.Twist.RealPower`, `Langlands.Representation.Smooth.SmoothPart.BasicProof`, `Langlands.Representation.Smooth.Transfer.PullbackProof` |
| `Langlands.Representation.Smooth.Admissibility.CofinalProof` | `Langlands.Representation.Smooth.Admissibility.CofinalStatement` |
| `Langlands.Representation.Smooth.Admissibility.CofinalStatement` | `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Smooth.Definitions` | — |
| `Langlands.Representation.Smooth.SmoothPart.BasicProof` | `Langlands.Representation.Smooth.SmoothPart.BasicStatement` |
| `Langlands.Representation.Smooth.SmoothPart.BasicStatement` | `Langlands.Representation.Smooth.SmoothPart.Definitions` |
| `Langlands.Representation.Smooth.SmoothPart.Definitions` | `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Smooth.Transfer.PullbackProof` | `Langlands.Representation.Smooth.Transfer.PullbackStatement` |
| `Langlands.Representation.Smooth.Transfer.PullbackStatement` | `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Smooth.Transfer.SubquotientProof` | `Langlands.Representation.Smooth.Transfer.SubquotientStatement` |
| `Langlands.Representation.Smooth.Transfer.SubquotientStatement` | `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Tensor.Finite` | `Langlands.Representation.Category.Basic`, `Langlands.Representation.Smooth.SmoothPart.BasicProof`, `Langlands.Representation.Smooth.Transfer.PullbackProof` |
| `Langlands.Representation.Tensor.OneFactor` | `Langlands.Representation.Smooth.SmoothPart.BasicProof` |
| `Langlands.Representation.Twist.AdmissibilityProof` | `Langlands.Representation.Twist.AdmissibilityStatement`, `Langlands.Representation.Twist.SmoothProof`, `Langlands.Representation.Smooth.Admissibility.CofinalProof` |
| `Langlands.Representation.Twist.AdmissibilityStatement` | `Langlands.Representation.Twist.Definitions`, `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Twist.AlgebraProof` | `Langlands.Representation.Twist.AlgebraStatement` |
| `Langlands.Representation.Twist.AlgebraStatement` | `Langlands.Representation.Twist.Definitions` |
| `Langlands.Representation.Twist.ContinuousCharacterProof` | `Langlands.Representation.Twist.ContinuousCharacterStatement` |
| `Langlands.Representation.Twist.ContinuousCharacterStatement` | — |
| `Langlands.Representation.Twist.Definitions` | — |
| `Langlands.Representation.Twist.RealPower` | `Langlands.Representation.Twist.SmoothProof` |
| `Langlands.Representation.Twist.SmoothProof` | `Langlands.Representation.Twist.SmoothStatement` |
| `Langlands.Representation.Twist.SmoothStatement` | `Langlands.Representation.Twist.Definitions`, `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Twist.SubquotientDefinitions` | `Langlands.Representation.Twist.Definitions` |
| `Langlands.Representation.Twist.SubquotientProof` | `Langlands.Representation.Twist.SubquotientStatement` |
| `Langlands.Representation.Twist.SubquotientStatement` | `Langlands.Representation.Twist.SubquotientDefinitions` |
| `Langlands.Representation.Whittaker.Algebraic` | `Langlands.Representation.MatrixCoefficient.Definitions`, `Langlands.Representation.Smooth.Definitions` |
| `Langlands.Representation.Whittaker.GeneralLinear` | `Langlands.Group.GL.UpperUnipotent`, `Langlands.HarmonicAnalysis.Basic`, `Langlands.Representation.MatrixCoefficient.LawsProof`, `Langlands.Representation.Whittaker.Algebraic` |
| `Langlands.Topology.CompactNormCharacter` | — |
| `Langlands.Topology.Nonarchimedean.Subgroup` | — |

This closure consists of matrix and local-field constructions, determinant
characters, topology, actual smooth representations, subquotients, smooth
parts, twists, tensor products, compact/parabolic induction, elementary
Jacquet localization, algebraic Whittaker functionals and matrix-coefficient
laws, and the concrete minus/iteration/order-wrapper infrastructure. It
includes generic twist admissibility results and dual definitions through
existing imports; no admissibility or duality assumption is imposed here.
The `Homogeneity` module also defines level and homogeneity and proves
finite-maximum and zero-carrier laws. None of its homogeneity conclusions
is a premise of these statements. In particular, importing that module to
use its order wrapper does not prove a detection or mixed-product theorem.

No project import is a segment derivative or Jacquet formula, segment
socle/head existence, product irreducibility, classification, exhaustion,
Whittaker coinvariant-finiteness statement, or a proof of those conclusions.
No theorem-valued premise appears in any of the four definitions. The only
local proof terms establish natural-number rank equalities and valid-order
bounds; the mathematical contents of 4.13(d) and 4.14(a) remain unproved.
There is therefore no mathematical proof of either assertion in this pair
whose dependencies could be supplied by an excluded consumer.

Both complete exclusion sets of task
`f9454f68-5916-40af-9970-3425330b4a97` revision 2 bind every future proof
and prerequisite: the inherited Ze80 6.2 scope and the shared upstream
scope of task `3238f371-e9a2-42ce-8b5d-9c4d3400ff55` revision 2,
including its additional Whittaker-finiteness restrictions. Their proof
dependency audit must be performed afresh on actual proofs, directly and
transitively. A proposition definition, draft, citation, conditional
assembly or pending task supplies no proved input. Operator-paused minus
exactness task `b65bc667-6951-4bd5-82af-10fb7046df7f` remains under its
existing controls; Worker 127 is not contacted or resumed by this work.

The separate tasks for 4.13(a), 4.13(b,c), 4.14(b), GL Leibniz filtrations,
homogeneity, supercuspidal or segment results are outside this statement
unit. The future 4.14(a) proof may use 4.13(b) only after the corresponding
exact proof is independently accepted and published. No such proof is
asserted by these declarations.
