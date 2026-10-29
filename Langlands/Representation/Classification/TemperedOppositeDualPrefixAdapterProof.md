# Necessary upper bounds imply opposite full-dual prefix bounds

Author: Worker 363.

`Langlands.glTemperedOppositeDualPrefixAdapter.{uF,uV}` proves exactly
`Langlands.GLTemperedOppositeDualPrefixAdapterStatement.{uF,uV}` from
[TemperedOppositeDualPrefixAdapterStatement](TemperedOppositeDualPrefixAdapterStatement.md).
The field and representation universes are independent. Its type is the
implication from `GLProductLeviTemperedExponentNecessityStatement` to
`GLTemperedOppositeDualPrefixStatement`. The upper necessity proposition
remains the sole premise; the proof does not import its separate proof module.

For every positive rank, ordered block shape `B`, actual irreducible
analytically tempered source `A : Rep ℂ (GL_n(F))`, full-transpose-dual
opposite exponent `χ` with open kernel, and scalar real part `s` of `χ`,
the conclusion is

```text
sum_(k <= i) s(k) <= 0
```

for every block index `i`, including the final index. These are block-scalar
coordinates, so the sum has no additional block-size factors. The supplied
topological data and the all-Haar analytic definition of temperedness are
retained, as are the original character and its given real part.

## Implemented proof

The proof composes four published constructions from
[TemperedOppositeJacquetScalarLayerAssembly](TemperedOppositeJacquetScalarLayerAssembly.md),
in namespace `Langlands.ScalarLayer`.

1. **Detect the same primal generalized character.**
   Temperedness supplies admissibility through `IsTempered.isAdmissible`.
   Apply `isGeneralizedEigencharacter_of_isDualJacquetExponent` to
   irreducibility, this admissibility and the actual full-dual occurrence.
   That helper proves finite span of the block-scalar action operators on
   the opposite Jacquet module, using finite generation and admissibility.
   Its generalized character spaces span the module. A nonzero dual
   eigenfunctional is nonzero on one of those spaces; applying powers of
   the character defects forces that space's character to equal `χ`.
   This yields primal generalized occurrence of exactly `χ`.

2. **Transport the upper necessity input to GL sources.**
   `temperedUpperExponentBound_of_productLeviNecessity` applies the supplied
   necessity proposition to the actual one-block Levi. Evaluation at its
   unique block gives a topological group equivalence with `GL_n(F)`,
   preserving irreducibility. A Haar measure on the GL quotient by its
   full center is pushed through the inverse central-quotient equivalence.
   The proved change-of-variables theorem transports analytic temperedness
   to that measure on the one-block Levi. The refined-Jacquet adapter then
   gives the upper exponent bound for every block shape of the original GL
   source. All these hypotheses are discharged inside the published helper.

3. **Reverse the actual normalized Jacquet module.**
   Apply `isJacquetExponent_reverse` to the primal generalized occurrence
   and the open kernel from the original dual exponent. It gives an upper
   exponent along `B.reverse` for the character
   `χ.comp (MaximalConeAssembly.precomp Fin.rev)`. Its underlying
   `oppositeJacquetReverseEquiv` uses the actual coinvariant maps
   `[v] ↦ [A.ρ(q)v]` and their inverses, where `q` is the block reversal
   matrix. The identity
   `T.leviModulus B.reverse (leviReverseEquiv B m) =
     (T.leviModulus B m)⁻¹`
   makes the inverse upper half-modulus equal the positive upper
   half-modulus of the opposite quotient. Reversing coordinates is
   continuous, so the new character has open kernel.

   For an arbitrary tuple `a` with antitone absolute values, the tuple
   `a ∘ Fin.rev` has monotone absolute values by `Fin.rev_le_rev`.
   Evaluate the upper bound from step 2 at that reversed tuple and the
   exponent just constructed. Since reversing twice is the identity,
   the result is `‖χ a‖ ≤ 1`. This gives a bound for the original
   character on every antitone tuple.

4. **Test all inclusive scalar prefixes.**
   `prefix_nonpos_of_antitone_bound` applies this bound to the given real
   part `s`. For each `i` it constructs the tuple with inverse-uniformizer
   entries at `k ≤ i` and entries one elsewhere. Their absolute values
   are respectively `q > 1` and one, hence antitone. The real-part formula
   gives character norm `q^(sum_(k <= i) s(k))`. A norm at most one forces
   that exponent to be nonpositive. The construction works for every
   `i`, including the final index whose prefix is the full sum.

## Scope and provenance

This is a derived internal proof assembling existing Library results in
their established conventions. It introduces no definitions, analytic
necessity proof, comparison certificates or additional premises. Its
provenance is the published statement pair and the four helper
implementations named above; no new literature theorem is asserted.
Their paired Markdown records the underlying analytic and algebraic
sources.

The proof requires no tensor presentation, finite-dimensional carrier,
finite-length hypothesis, scalar-layer choice or unitarizability premise.
It uses no weakly critical refinement or support, critical-to-minimal
equivalence, tempered discrete-series support, tempered block exhaustion,
tempered unitarity or genericity, regular exhaustion or equal-exponent
grouping. Some imported statement modules contain proposition definitions
for later classification results; none supplies a proof used here. The
target statement pair and all existing imported pairs remain unchanged.
