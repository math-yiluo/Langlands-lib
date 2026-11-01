# Compact-induction models for the normalized left Psi comparison

This is a focused internal construction for the left Psi clause of
Bernstein–Zelevinsky, Proposition 4.13(b). Its principal declaration is
`Langlands.Derivative.MirabolicProductMinus.leftPsiInductionEquiv`.
It constructs the actual normalized Psi-minus of a left mixed product as
compact induction of an explicitly computed quotient coefficient. The
coefficient action, evaluation formula, and naturality in both inputs are
proved. The source-P₁ specialization is identified with the actual binary
product, retaining its entire GL₀ output carrier.

This module does not prove the all-rank `LeftPsiCompatibility` proposition,
the positive Phi comparisons, or the host six-part
`MirabolicProductMinusCompatibilityStatement`. Passing from the section
subgroup to the positive binary parabolic and then to the binary product
remains a separate assembly. The existing statement module is imported for
the unchanged targets and their native functor definitions.

## Provenance and conventions

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472; registered source `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant passages are §1.8, printed pp.444–445 (PDF pp.5–6), for
normalized induction and character localization; §§3.1–3.2, pp.450–451
(PDF pp.11–12), for the mirabolic radical and minus functors; §4.12,
pp.456–458 (PDF pp.17–19), case (II), for the left mixed product; and
Proposition 4.13(b), p.458 (PDF p.19), for its functorial Psi compatibility.
These passages and their page images were read during this task. A bounded
project and literature search found no BZ77-specific erratum entry.

The new equivalences and elementary adapters are derived internal content.
They are not presented as verbatim definitions from the original. The
implementation uses the published normal-coinvariant and split-quotient
comparisons instead of the original's full geometric-lemma route.

Fix arbitrary `p`, `[Fact p.Prime]`, `F : PadicField.{uF} p`, and the supplied
`T : F.TopologicalData`. All topological hypotheses are installed from
`T`; no canonical replacement topology is chosen. The representation
carrier universe `uV` is independent of `uF`.
For natural numbers `k,r`, write

- `G = mirabolic (k+r) F.Carrier = P_(k+r+1)`;
- `N = radical (k+r) F.Carrier`, its translation radical;
- `L = GeneralLinear (k+r) F.Carrier`;
- `H = leftSubgroup k r F.Carrier`;
- `S = H.comap levi`, a subgroup of `L`;
- `I = N.subgroupOf H`.

The pair `X=(ρ,τ)` consists of arbitrary smooth complex representations on
`GL_k` and `P_(r+1)`, with their full carriers in universe `uV`. The mixed
product has carrier universe `max uF uV`. Here
`psiMinus T r : P_(r+1) → GL_r`. No finiteness, admissibility,
irreducibility, nonzero-vector or nonzero-object hypothesis occurs.
Although the final host clause requires positive `k`, these internal
constructions also permit `k=0`.

## Concrete subgroup and determinant calculations

`radical_le_leftSubgroup` checks the actual lower-left matrix equations
entry by entry. Every prescribed entry lies off the diagonal in the
radical's identity block. `leftSubgroup_comap_levi` identifies `S` with
the consecutive two-block upper subgroup, including empty blocks.
`leftSubgroup_comap_levi_binary` identifies it with the published binary
parabolic when both block sizes are positive. All these are equalities
of the actual matrix subgroups.

The radical projection has first coefficient block equal to one and
second block again radical. `leftRadicalProjection` retains the last
`r` translation coordinates; its surjectivity proof inserts those
coordinates and sets the first `k` coordinates to zero. The map
`leftCoefficientRadicalProjection : I →* radical r` also accounts for
the actual subgroup-of carrier.

On a Levi element, the second coefficient block has no translation
part. Its projected GL block and the first coefficient block are exactly
the two diagonal blocks of `leftPsiSectionTwoBlock`. The two-block
determinant formula follows from `Matrix.det_fromBlocks_zero₂₁`.
The local last-row determinant calculation identifies the determinant
of a mirabolic element with that of its GL projection.
Consequently the actual left normalizing character is trivial on `N`,
and the determinant norm on `S` is the product of its two block norms.

## Full tensor coinvariants and the quotient coefficient

The generic `tensorCoinvariantsEquiv` applies to groups `N₀,M₀`, a
surjective homomorphism `f : N₀ →* M₀`, and an action on `V ⊗ W`
whose pure-tensor formula is
`n(v ⊗ w) = v ⊗ τ(f(n))w`.
It identifies its coinvariants with `V ⊗ Coinvariants τ`.
The forward map applies the second quotient map. To construct the
inverse, the bilinear map to the tensor coinvariants descends through
the second quotient: a preimage of each `m` under `f` verifies its
relation. Tensor and quotient universal properties prove the two maps
inverse. This algebraic argument imposes no topology or dimension
condition and retains zero and arbitrary first factors.

`leftPsiCoefficient T X`, denoted `σ_X`, is exactly the actual left
inducing representation twisted by `T.leftCharacter k r`.
The radical pure-tensor formula applies the preceding comparison.
`leftPsiCoefficientEquiv T X`, denoted `e_X`, then uses the inverse of
the published trivial-character localization equivalence on the second
factor. Its codomain is
`ρ ⊗ (psiMinus T r).obj τ`, with the actual Psi quotient carrier.
On a pure-tensor class its value is
`v ⊗ psiMinusQuotient T r τ w`.

The section coefficient `leftPsiNormalizedCoefficient T X`, denoted
`κ_X`, is the restriction of `σ_X.toCoinvariants I` along
`levi.subgroupComap H`, twisted by the ambient determinant inverse-half
character restricted to `S`.
For `g ∈ S`, let `a` be the first coefficient GL block of `levi(g)`
and `b` the GL projection of its second mirabolic coefficient block.
The proved action formula is

```text
e_X(κ_X(g)z) =
  ν_k(a)^(r/2) ν_r(b)^(-k/2)
    (ρ(a) ⊗ (Ψ⁻τ)(b)) e_X(z).
```

Here each real power is the explicit real power of the positive
determinant norm, embedded in ℂ; there is no implicit twist.
The proof first descends the section action through coinvariants and
checks pure tensors. It then factors the ambient determinant norm and
combines the first-block exponents `-1/2+(r+1)/2=r/2`.
The remaining second-block inverse-half power is exactly the source
Psi normalization. `leftPsiSection_halfModulus` separately checks that
the displayed pair of powers is the published binary parabolic half
modulus in positive ranks, using its actual finite product formula.

`leftPsiCoefficientMap` is the tensor of the two input maps, restricted
to `H` and twisted. `leftPsiNormalizedCoefficientMap` is its map on
`I`-coinvariants, restricted to `S` and twisted. The equation
`leftPsiCoefficientEquiv_natural` states that `e_Y` carries this map to
`f₁ ⊗ (Ψ⁻f₂)`. Its proof uses coinvariant hom-ext and tensor extensionality;
the resulting pure-tensor equality is definitional.

## The actual induction equivalence

`psiMinusOrdinaryEquiv` is the published trivial-character quotient
equivalence restricted along the actual Levi section. Its naturality
is the published `trivialEquiv_natural`, with no new choice of quotient.
`leftPsi_mirabolic_compactOpenBasis` restricts the published
nonarchimedean GL topology to the closed mirabolic subgroup and applies
the compact-open subgroup basis theorem.

`leftPsi_normalSplitEquiv` applies the published
`Induction.normalSplitCompactEquiv` using the actual maps `projection`
and `levi`. The section identity, continuity, equality of the projection
kernel with `N`, closedness of `H,N`, containment `N ≤ H`, and
smoothness of `σ_X` are all discharged. A private generic wrapper
transports the proved equality of kernel subgroups before specialization;
it adds no assumption to the concrete construction.

The principal `leftPsiInductionEquiv T X` has type

```text
Representation.Equiv
  (Ψ⁻_(k+r) ((leftMixedProductFunctor k r).obj X)).representation
  (Induction.compactInduced S κ_X).
```

It composes the ordinary quotient comparison with the normal-split
comparison, twists by the actual ambient inverse-half character, and
uses `compactInductionTwistEquiv` to move that twist into `κ_X`.
For an inducing function `f` and `l ∈ GL_(k+r)`, its value on the actual
Psi quotient class evaluates to

```text
ν_(k+r)(l)^(-1/2) · [leftMixedEval X f (levi l)]_I.
```

This is `leftPsiInductionEquiv_eval_quotient`. In particular it retains
the actual section, function support conditions and quotient map.
`leftPsiInductionEquiv_natural` carries the Psi of the actual mixed
product map to
`compactInducedMap S (leftPsiNormalizedCoefficientMap T X f)`.
Its proof composes the published trivial-quotient and normal-split
naturality laws with the fact that a linear coefficient map commutes
with character multiplication.

## Source rank one and the full GL-zero output

When `r=0`, `mem_leftPsiSection_zero` proves that `S` contains every
element of `GL_(k+0)`. Its first block is the original GL element and
its second projected GL block is the identity of `GL₀`.
The coefficient scalar in the displayed action is one. Thus
`leftPsiZeroCoefficientEquiv` is an equivariant identification with
the published `BinaryTensor.rankZeroRight` action on
`ρ ⊗ (Ψ⁻τ)`. Its second tensor factor is the entire actual GL₀
representation carrier, not a chosen one-dimensional object.

Smoothness of that coefficient follows from the published
`binaryRightZeroTensorEquiv` and transfer of smoothness through
surjective and injective intertwiners.
`leftPsiZeroTensorEquiv` composes the principal induction comparison
with `compactInducedTopEquiv` (evaluation at one) and the coefficient
equivalence. `leftPsiZeroEquiv` follows by the inverse of the published
binary right-zero tensor equivalence; its target is precisely
`(binaryNormalizedProductFunctor k 0).obj (ρ, Ψ⁻τ)`.
The two naturality theorems use evaluation of the induction naturality
law, the coefficient naturality law, and the published binary
right-zero tensor naturality. This includes `k=0` internally and never
removes either full carrier.

## Mathematical dependency and restriction audit

Every row concerns the actual proofs above, including their transitive
inputs. The imports listed below contain only lower constructions,
their statements and published proofs. A statement definition is not
used as a proof of its comparison.

| Obligation or restriction | Inputs and scope of the implemented construction |
| --- | --- |
| Concrete left subgroup, radical and section | Actual matrix definitions in `MirabolicMixedProductSubgroups`, `MirabolicRadical`, `MirabolicProjection`, `TwoBlock` and `BlockShape.binary`; elementary finite-index and determinant calculations. No orbit comparison is assumed. |
| Full coefficient quotient | Quotient-span and tensor universal properties; the explicitly surjective radical projection; published trivial-character localization equivalence. No finiteness theorem occurs. |
| Normalization | Published explicit `leftCharacter`, `psiMinusCharacter`, and binary half-modulus definitions; determinant factorization and real-power algebra. No suppressed character or Haar-scaling premise remains in the model. |
| Induction comparison | Published normal-coinvariant comparison (pointwise quotient, compact-induction surjectivity, and the normal relation-kernel theorem), split-quotient comparison, character-twist comparison, and compact-open basis. Their proofs use quotient relations, compact local sections, cutoffs and compact averaging, not derivative consumers. |
| Rank-zero specialization and naturality | Published whole-subgroup evaluation equivalence, binary right-zero tensor equivalence, smoothness transfer, and the explicit naturality calculations above. Arbitrary zero objects, repeated factors and GL₀ carriers remain admissible. |
| Plus functors, adjunction, BZ77 4.13(d), and general Leibniz proofs | No such conclusion supplies an input. No plus-functor or adjunction module belongs to this closure. Matrix subgroup constructions do not assert a plus-functor theorem. |
| Segment formulas, segment socle/head existence, commutation, gluing and product irreducibility | No segment derivative/Jacquet formula, Ze80 §3.5 or §9.6 result, Ze80 4.2 or 9.7 criterion, or any named excluded segment consumer supplies an input or appears in the import closure. |
| Classification and exhaustion | No analytic or square-integrability result (including Ze80 9.3), special-head criterion, multisegment, ordered-head, quotient coverage, tempered, square-integrable or regular exhaustion theorem is imported or used. This includes the full inherited exclusion union of the host task. |
| Two-supercuspidal consumers | Neither `TwoSupercuspidalNonadjacentProductIrreducible` nor `TwoSupercuspidalProductStructure`, their successors, or transitive consequences is used. No supercuspidal theorem occurs in this closure. |
| Whittaker and arbitrary-character finiteness | No `SupercuspidalCoinvariantFinitenessStatement`, `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`, all-character single-block conclusion, or mirabolic finite-length route using them is imported or used. The Whittaker imports below supply basic characters and algebraic definitions only. |
| Other clauses of the host task | The imported target module contributes proposition and functor definitions. No unproved Psi/Phi compatibility, short exact sequence, derivative formula, pending artifact or draft is used as a mathematical premise. This construction does not complete those clauses. |
| Parameters and authority | All hypotheses are discharged for arbitrary supplied `T` and independent `uF,uV`; no theorem-valued premise, saturation, genericity, dimension or length condition is added. No suspended worker or consumer was used to waive an inherited restriction. |

## Complete project import closure

The following are all 104 transitive project imports, excluding this
module itself, computed from its four direct imports against Library
`b22e185743f7c318f709e14e422801f4360105d5`. Mathlib imports are supplied by the
pinned environment. Every existing project Lean/Markdown pair is unchanged.

```text
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientTopology
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
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
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
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
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CharacterTwistProof
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.CompactSurjectivityProof
Langlands.Representation.Induction.CompactSurjectivityStatement
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.NormalCoinvariantKernelProof
Langlands.Representation.Induction.NormalCoinvariantKernelStatement
Langlands.Representation.Induction.NormalCoinvariantMap
Langlands.Representation.Induction.NormalCoinvariantProof
Langlands.Representation.Induction.NormalCoinvariantStatement
Langlands.Representation.Induction.NormalSplitComparison
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
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
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
