# Gamma compatibility of full families from L, epsilon and duality

Author: Worker 1698. This module proves the published Library proposition
`Langlands.Correspondence.FullGammaFromFactorsStatement` of
`Langlands/Correspondence/FullGammaCompatibility`. The closing theorem is

```lean
theorem Langlands.Correspondence.fullGammaFromFactors :
    FullGammaFromFactorsStatement.{uF, uP, uA} F
```

for arbitrary `p`, `[Fact p.Prime]` and `F : PadicField.{uF} p`. Its type is the
unchanged named proposition. The statement and its imports are unchanged, and
the proof adds no hypothesis. It is proved for every reciprocity family `eC`,
every local-constant system `ε` with `hε : IsSystem F eC ε` and every full map
`c`. The conclusion holds for every nontrivial `ψ`, all ranks, all parameter
classes (any monodromy, generic or not) and every self-dual measure. The proof
uses only the three published hypotheses `FullPairLCompatibility F c`,
`FullPairEpsilonCompatibility F eC ε hε c` and `DualCompatibility F c`.

The tensor-dual equivalence and its monodromy lemma are shared in
`Langlands/WeilDeligne/TensorDual`, with their full construction described in
its paired Markdown. This module uses that equivalence for the reflected
L-ratio comparison below.

## The reflected L-ratio of a tensor class

**`LocalFactor.WeilDeligne.rationalLRatioClass_tensorClass I g c X Y`.** For
pair classes `X`, `Y`, a normal subgroup `I`, an element `g` and a unit `c`:

```text
rationalLRatioClass I g c (tensorClass X Y)
  = subst c (pairLFactorClass I g (dualClass X) (dualClass Y)) / pairLFactorClass I g X Y
```

where `subst c` is the substitution `X ↦ c / X` (`RationalReflection.subst`).
Proof: by `Quotient.inductionOn₂`, take representatives `A`, `B`. Then the
left side is by definition `subst c (L(dual (A ⊗ B))) / L(A ⊗ B)`, and the pair
L-factors are the L-factors of the tensor pairs. The L-factor is invariant
under pair equivalences (`rationalLFactor_eq_of_equiv`). Applied to
`tensorDualEquiv A B`, this gives `L(dual (A ⊗ B)) = L(dual A ⊗ dual B)`, and
the two sides then agree.

## The main theorem

Fix `eC`, `ε`, `hε`, `c` and the hypotheses `hL`, `hEps`, `hDual`. Fix also a
nontrivial `ψ`, ranks `r + 1`, `t + 1` and parameter classes `D`, `D'`. Write
`q⁻¹ = residueReflection F`.

1. **Measure existence.** The first component of the L-condition
   `IsPairLCompatibleAt` at `(D, D')` gives a measure that is self-dual for `ψ`.
2. Fix a self-dual measure `ν`.
   - `hDual` at `D` and `D'` gives parameter classes `E`, `E'` with
     `IsDualOf D E` and `IsDualOf D' E'`, together with
     `IsSmoothDual F (c D) (c E)` and `IsSmoothDual F (c D') (c E')`.
     `IsDualOf D E` unfolds to
     `parameterForget F E = dualClass (parameterForget F D)`.
   - The L-condition at `(D, D')` and `ν` gives `P` with
     `IsAutomorphicPairLPolynomial F ψ ν (c D) (c D') P` and
     `arithmeticPairLFactor F (forget D) (forget D') = 1 / P`.
   - The L-condition at the dual pair `(E, E')`, also at `ν`, gives `P^∨` with
     `IsAutomorphicPairLPolynomial F ψ ν (c E) (c E') P^∨` and
     `arithmeticPairLFactor F (forget E) (forget E') = 1 / P^∨`.
   - The epsilon condition at `(D, D')` and `ν` gives `e = (c₀, m)` with
     `IsAutomorphicPairEpsilonFactor F ψ ν (c D) (c D') e` and
     `IsArithmeticPairEpsilonFactor F eC ε hε ψ (forget D) (forget D') c₀ m`.
3. **Witness.** Take
   `G = RankinSelberg.rationalGammaExpression q⁻¹ c₀ m P P^∨`, that is,
   `G(X) = c₀ X^m P(X) / P^∨(q⁻¹/X)`.
   - **Representation side.** `IsAutomorphicPairGammaFactor F ψ ν (c D) (c D') G`
     holds with the witnesses `c E`, `c E'`, `P`, `P^∨` and `e`, and the
     equation for `G` holds by `rfl`.
   - **Arithmetic side.** `IsArithmeticPairGammaFactor` holds with the same
     `c₀`, `m` and the epsilon fact from step 2. What remains is the identity
     `G = rationalEpsilonMonomial c₀ m * rationalLRatioClass … q⁻¹ (tensorClass (forget D) (forget D'))`.
     Rewrite the ratio with `rationalLRatioClass_tensorClass`, replace the dual
     classes by `forget E` and `forget E'` using `IsDualOf`, and insert the two
     arithmetic L-factors `1 / P` and `1 / P^∨`. The ratio becomes
     `subst q⁻¹ (1 / P^∨) / (1 / P)`. Then `map_inv₀` and
     `RationalReflection.subst_polynomial` turn `subst q⁻¹ (1 / P^∨)` into
     `1 / P^∨(q⁻¹/X)`, and `inv_div_inv` gives `P / P^∨(q⁻¹/X)`. Unfolding
     `rationalGammaExpression` and `mul_div_assoc` close the goal.

The arithmetic pair L-factor `arithmeticPairLFactor` is by definition the
`pairLFactorClass` at the local inertia subgroup and the geometric Frobenius.
The proof restates the two L-facts in that form by definitional unfolding
before rewriting.

## Sources and provenance

The target is the derived implication recorded in Henniart 2000, §1.2, the
remark after property 4), printed p.440: the gamma identity follows from the L
and epsilon identities ("une identité évidente"). The gamma factors on both
sides are the formula
`γ(s, σ, ψ) = ε(s, σ, ψ) L(1 - s, σ^∨) / L(s, σ)` of Henniart 2002, §1.2. The
statement module cites both sources. The Lean proof is this evident identity:
the representation side is built from the L-factors of the image pair and of
the image of the dual pair, and the arithmetic side from those of the tensor
product and of its dual. The comparison
`(X ⊗ Y)^∨ ≅ X^∨ ⊗ Y^∨` of Weil–Deligne pairs is standard linear algebra,
proved here through Mathlib's `TensorProduct.dualDistribEquiv`.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom.
