# Root factorization of intertwining operators from continuation, cocycle and chain inputs

Module `Langlands.Global.AdelicIntertwiningRootFactorizationAssembly`. It proves that
`Langlands.Global.IntertwiningRootFactorizationStatement` (module
`Langlands.Global.AdelicIntertwiningRootFactorizationReduction`) follows from four
propositions:

- `IntertwiningMeromorphicContinuationStatement` (module
  `Langlands.Global.AdelicIntertwiningContinuationStatement`): `M(w, λ)φ` agrees on the regular
  region with finite sums `∑ i, coeff i λ • ψ i`, with `ψ i` automorphic for the target and
  meromorphic coefficients;
- `IntertwiningCocycleStatement` (module `Langlands.Global.AdelicIntertwiningCocycleStatement`):
  for any such expansions of `M(w, λ)φ`, `M(w', μ)ψ i` and `M(w'w, λ)φ`, the relation
  `M(w'w, λ) = M(w', wλ) M(w, λ)` holds on the common domains;
- `IntertwiningStandardizationStatement` and `IntertwiningElementaryChainStatement` (module
  `Langlands.Global.AdelicIntertwiningElementaryChainStatement`).

It does not prove any of the four, so it does not prove
`IntertwiningRootFactorizationStatement` by itself.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`,
§8.6, pp. 225–226 (TeX `1911.02342.tex` lines 3517–3523): the operator of an elementary
symmetry depends on one coroot coordinate; a general `w` is decomposed into elementary
symmetries (Mœglin–Waldspurger I.1.8) and the operators multiply (Mœglin–Waldspurger II.1.6,
and Theorem 2.3 (5)). The proof below is this argument, carried out in finite bases.

## Definitions and lemmas

- `exists_isOpen_regular_and_translate`: for a root presentation, a bound `R₀` and a parameter
  `ν`, some chart contains a nonempty open set of points `s` such that `e s` and `e s + ν` are
  both `R₀`-regular. The set is open as the intersection of the regular region of the chart
  (`isOpen_regularParameter_inCoordinates`) with its translate. A point is
  `e.symm λ` for a parameter `λ` that is `(R₀ + c)`-regular (`exists_regularParameter`), where
  `c` is the sum, over the finitely many roots, of `|B((Re ν)|_A, α)|`.
- `IntertwiningRootFactorizationAssemblyStatement`: the implication from the four propositions
  above to `IntertwiningRootFactorizationStatement`.

## Theorem: `intertwiningRootFactorization_of_inputs`

`intertwiningRootFactorization_of_inputs : IntertwiningRootFactorizationAssemblyStatement.{u}`.

Proof, as implemented.

1. **Standardization.** Apply `IntertwiningStandardizationStatement` to the data of the target.
   It gives the standard family `fam`, the indices `I`, `I'`, the maximal compact subgroup `K₀`
   with Iwasawa coverage for every standard parabolic of `fam`, the element
   `(w₀, c₀)` of `W(P_I, P_{I'})` with retraction `π₀`, the isomorphism `iota`, the entire
   coefficients `E j`, the functions `h j`, the maps `τ j`, the automorphic functions `φ₀ j`,
   the three instances, the transports of regularity and of root kernels along `iota`, and the
   comparison `M(w, λ)φ (g) = ∑ j, E j λ * h j g * M₀(w₀, iota λ)(φ₀ j)(τ j g)`.
2. **Chain.** Apply `IntertwiningElementaryChainStatement` to `fam`, `K₀`, `I`, `I'`,
   `(w₀, c₀)` and `π₀`. It gives the chain `J' = Fin.cons I J`, the steps, the partial
   composites `(W t, C t)`, the retractions, the invariance and transport of each step and the
   identity with the operator of `(W n, C n)` on the regular region.
3. The parameter spaces are finite-dimensional, since rational characters of a presented
   parabolic form a finitely generated free abelian group
   (`ParabolicRootPresentation.rationalCharacters_free_finite`). By induction on `t`
   (`Fin.induction`) every partial composite satisfies
   `IsWeylConjugation (fam.p I) (fam.l I) (fam.p (J' t)) (fam.l (J' t)) (W t) (C t)`: for
   `t = 0`, `(1, 𝟙)` presents the identity because `G.innerIso 1` is the identity
   (`innerIso_one_hom`); the inductive step is the composition of Weyl conjugations
   `AdelicGroupPoints.IsWeylConjugation.comp` (module `Langlands.Global.AdelicWeylSetAssociation`),
   applied to the partial composite and the step.
4. **Induction along the chain.** For every `t` and every `ψ` automorphic for `P_I` and `K₀`,
   the family `μ ↦ M(W t, C t, πs t)(ψ)(μ)` from `P_I` to `P_{J' t}` has a root factorized
   expansion (`HasRootFactorizedExpansion`) for the root forms and unipotent roots of
   `fam.rootPresentation I`, the regular regions of that presentation, and functions
   automorphic for `P_{J' t}`:
   - `t = 0`: `W 0 = 1` and `C 0 = 𝟙`, and the identity operator returns `ψ`
     (`IsIwasawaCompact.intertwiningOperator_one_self`, using the left invariance of `ψ` under
     `U_I(𝔸)`, a consequence of its invariance under `U_I(𝔸)M_I(F)`). Then
     `hasRootFactorizedExpansion_of_eq` applies.
   - `t → t + 1`: `HasRootFactorizedExpansion.step` (module
     `Langlands.Analysis.Meromorphic.RootFactorizedExpansion`) with `We` the linear equivalence
     equal to `weylParameter (fam.l I) (C t) (πs t)` (`exists_weylParameter_linearEquiv`),
     `α` the root form of the step's root, the regular regions of `fam.rootPresentation (J' t)`
     (monotone in the bound, with the open sets of `exists_isOpen_regular_and_translate`), the
     transport clause of the chain for the kernel, the induction hypothesis for `Op₀`,
     `IntertwiningMeromorphicContinuationStatement` for the step operators on automorphic
     functions for `P_{J' t}` and for the composite `(W (t+1), C (t+1))`, the invariance clause
     of the chain, and `IntertwiningCocycleStatement` for the composition rule. For the last,
     the expansion of the composite is rewritten with `W (t+1) = ws t * W t` and
     `C (t+1) = cs t ≫ C t`, and `We x` is rewritten as the Weyl parameter.
5. **Comparison.** For `λ` regular enough, `iota λ` is regular for the identity clause of the
   chain, so `M₀(w₀, iota λ)(φ₀ j) = M(W n, C n, πs n)(φ₀ j)(iota λ)` (the `φ₀ j` are left
   invariant under `U_I(𝔸)M_I(F)` because they are automorphic). With the comparison of step
   1 this gives `M(w, λ)φ (g) = ∑ j, E j λ * h j g * Op j (iota λ) (τ j g)`, where `Op j` is
   the family of step 4 for `ψ = φ₀ j` at `t = n`.
6. **Assembly.** `exists_rootFactorization_of_combination` (module
   `Langlands.Analysis.Meromorphic.RootFactorizedExpansion`) with the forms
   `r.rootFunctional hA hT`, the set `r.unipotentRoots`, the regular regions of `r`, `iota`
   and its two transports gives `k`, `ψ`, `coeff`, `D`, the meromorphy of the coefficients,
   the agreement on a regular region and root factors `fac i j t` with common lengths. A root
   factor (`IsRootFactorOn`) for these forms is literally the alternative required of each
   factor in `IntertwiningRootFactorizationStatement`, which concludes.

The proof uses the four propositions, the Library modules named above and Mathlib. Its axioms
are `propext`, `Classical.choice` and `Quot.sound`.
