# The left source-rank-one boundary of BZ77 Proposition 4.13(b)

Author: Worker 837.

This pair proves the clause
`Langlands.Derivative.MirabolicProductMinus.LeftPhiBoundary.{uF,uV} F T` of the
published statement `MirabolicProductMinusCompatibilityStatement`. The entry
theorem is

```lean
theorem Langlands.Derivative.MirabolicProductMinus.leftPhiBoundary
    (T : F.TopologicalData) : LeftPhiBoundary.{uF, uV} F T
```

for every prime `p`, `F : PadicField.{uF} p` and `T : F.TopologicalData`, with
independent universes `uF` and `uV`. It has no further hypotheses. The pair
proves one of the six components; it does not prove the whole statement.

## Source and correspondence

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations
of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, source ID
`bernstein-zelevinsky-1977-induced-i`. Proposition 4.13(b) on printed p.458
(one-based PDF page 19) states `Φ⁻(ρ × τ) ≅ ρ × Φ⁻(τ)` for `ρ` on `G_k` and `τ`
on `P_m`. The same page adopts the convention `P_0 = ∅`. At `m = 1` the right
side is therefore zero. The published clause `LeftPhiBoundary` states this
without a group `P_0`: for every nontrivial `ψ`, every `k` and every pair `X`
of a smooth representation of `GL_(k+1)` and one of `P_1`, the carrier of
`(leftPhiProduct T ψ k 0).obj X` is a subsingleton. Here `leftPhiProduct`
is `Φ⁻` of the left mixed product (BZ77 4.12, case (II)), after the actual
rank cast `(k+1)+0 = (k+0)+1`.

In §7.2 (printed p.471), BZ77 proves 4.13(b) for `Φ⁻` with Theorem 5.2. The
proof has two orbits; the open orbit contributes nothing, and the remaining
orbit gives `ρ × Φ⁻τ`. The Lean proof below does not use the geometric lemma.
At `m = 1` it shows directly that the whole radical of `P_(k+2)` acts trivially
on `ρ × τ`, so that the localization at the nontrivial character `θ_ψ` vanishes.

## Group lemmas (generic commutative ring)

- `mem_leftSubgroup_zero_right`: for `r = 0` the case (II) subgroup
  `leftSubgroup k 0 R` is all of `mirabolic (k + 0) R`. Its defining entries
  lie in the last row and the first `k` columns, and these entries vanish for
  every mirabolic matrix.
- `mem_leftKernel_zero_right_of_mem_radical`: for `r = 0` every element of
  `radical (k + 0) R` lies in the kernel `leftKernel k 0 R` of the case (II)
  projection. Its `GL_k` block is the identity, and the `P_1` block is the
  trivial group.

## The radical acts trivially

`leftMixedProduct_zero_right_radical T X f hu`: for `u` in the radical of
`P_(k+1)` (Lean `mirabolic (k + 0)`), `u` fixes every vector `f` of
`(T.leftMixedProductFunctor k 0).obj X`. The proof evaluates both sides at
each `x` with the published `leftMixedEval_injective` and
`leftMixedProductFunctor_action`. The radical is normal (`radical_normal`), so
`x u x⁻¹` is a radical element. It lies in the case (II) kernel by the previous
lemma. The published `leftMixedEval_of_mem_leftKernel_mul` then gives
`f(x u) = f((x u x⁻¹) x) = f(x)`.

## The boundary clause

`leftPhiBoundary`: fix `ψ`, `k` and `X`, and let
`A = (T.leftMixedProductFunctor (k + 1) 0).obj X`.

1. `ψ` is nontrivial, so some `t` has `ψ(t) ≠ 1`.
2. `u = radicalElement (Pi.single (Fin.last (k + 0)) t)` is a radical
   element with `θ_ψ(u) = ψ(t) ≠ 1`, by the published `theta_radicalElement`.
3. By the previous section, `u` acts trivially on `A`.
4. Every vector of the target is `phiMinusQuotient T ψ (k + 0) A v`
   (`phiMinusQuotient_surjective`). The published `phiMinusQuotient_radical`
   gives `[u • v] = θ_ψ(u) [v]`. Since `u • v = v`, this gives
   `(θ_ψ(u) - 1) [v] = 0`, so `[v] = 0`.

The rank cast `mirabolicRankCast T (Nat.succ_add k 0)` is the identity, because
`(k + 1) + 0` and `(k + 0) + 1` are definitionally equal. The proof therefore
works on the vectors of `A` directly. Every vector of the target is zero, so
the carrier is a subsingleton.

## Imports and dependency audit

Direct imports:
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
and `Langlands.Group.GL.MirabolicProjection`. The project import closure has 74
modules besides this one. All are published Library modules. The complete
closure is listed below so this component can be reviewed independently.

Mathematical proof dependencies are the published definitions of the mixed
product and of `Φ⁻`, and the published lemmas named above. They come from
`Mirabolic/MixedProducts`, `Derivative/MirabolicMinus`,
`Derivative/MirabolicCharacter`, `Group/GL/MirabolicMixedProductSubgroups`,
`Group/GL/MirabolicProjection` (`radical_normal`), `Group/GL/MirabolicRadical`
and `Group/GL/Mirabolic` (`rankOne_eq_one`). The audit against the task
restrictions:

- The proof uses no plus functor, no adjunction, no §4.13(d), no Leibniz or
  filtration proof, no finiteness or classification result, and no Whittaker
  finiteness statement. No closure module states or proves any of these.
- No other clause of the target statement is used. The statement module is
  imported only for the definitions `leftPhiProduct` and `LeftPhiBoundary`.
- The proof uses no segment, supercuspidal, socle, head or Jacquet-formula
  result and no task or statement in the independence lists. It does not use
  `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
  `IrreducibleCoinvariantFinitenessStatement` or
  `LeviCuspidalCoinvariantFinitenessStatement`.
- No group `P_0` is introduced, and `Φ⁻` is never applied to `P_1`. The input
  pair is arbitrary: no admissibility, irreducibility, finite dimension or
  chosen vector is assumed.

Axioms: `propext`, `Classical.choice` and `Quot.sound`; universe parameters
`[uF, uV]`.

## Complete project import closure

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.BlockModulus`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicMixedProductSubgroups`
- `Langlands.Group.GL.MirabolicOppositeIntersection`
- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement`
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.OppositeBlocks`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.PadicBlocks`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.RankReindex`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.Subquotients`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Derivative.Homogeneity`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Induction.BinaryProduct`
- `Langlands.Representation.Induction.BlockFactors`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.Parabolic`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.PositiveCharacter`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement`
- `Langlands.Representation.Mirabolic.MixedProducts`
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.BasicProof`
- `Langlands.Representation.Smooth.SmoothPart.BasicStatement`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement`
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement`
- `Langlands.Representation.Tensor.Finite`
- `Langlands.Representation.Tensor.OneFactor`
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement`
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement`
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement`
- `Langlands.Representation.Whittaker.Algebraic`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Topology.CompactNormCharacter`
- `Langlands.Topology.Nonarchimedean.Subgroup`

Worker 499 recompiled and inspected the copied shared draft revision 2 with
zero errors and warnings at the current workspace base. This is development
verification; independent semantic review and publication remain required.
