# Finitely many rational parabolics share an embedded rational Levi (Renard V.3.1)

Module `Langlands.GroupScheme.Rational.LeviParabolicFiniteProof`, namespace
`Langlands.GroupScheme`, universe `u` (the base field).

`leviParabolicFinite` proves exactly
`Langlands.GroupScheme.LeviParabolicFiniteStatement.{u}` from
[LeviSplitComponentRecallStatements](LeviSplitComponentRecallStatements.md). For a field `k`,
a connected reductive `G`, a rational parabolic `p : P ⟶ G` and a rational Levi factor
`l : M ⟶ P`, it gives a natural number `N` such that every family `q i : Q i ⟶ G`
(`i : Fin n`) of rational parabolics with rational Levi factors `lQ i : M ⟶ Q i`,
`lQ i ≫ q i = l ≫ p`, and pairwise distinct images `SubgroupFunctor.range (q i)` has
`n ≤ N`. The statement and its hypotheses are unchanged and no premise is added.

## Proof

The bound is `N = 2 ^ |Φ(T₀)|`, where `Φ(T₀)` is the finite set of relative roots of one
maximal split torus `T₀` chosen from `(p, l)` alone, before the family is given.

1. *Choices from `(p, l)`.* `splitComponentStatement` applied to the connected reductive `M`
   gives a split component `a : A ⟶ M`. `parabolicRootPresentationExistence` gives a
   compatible root presentation `R` of `(p, l, a)`. Its torus `i₀ : T₀ ⟶ G` is a maximal
   split torus, and its factor `f₀ : A ⟶ T₀` satisfies `f₀ ≫ i₀ = a ≫ l ≫ p`
   (`isCompatible.factor_comp`). `IsSplitTorus.finite_relativeRoots` shows that the
   relative roots `relativeRoots i₀` form a finite set. Its `Finset` is `roots`, and
   `N = 2 ^ roots.card`.

2. *Each member is a dynamic parabolic in `T₀`.* For each `i`,
   `parabolicRootPresentationExistence` gives a presentation `S i` of `(q i, lQ i, a)`, for
   the same split component `a`. Its chosen cocharacter `ν_i` of `A`
   (`splitComponentCocharacter`) satisfies
   `range (q i) = P_G(ν_i ≫ a ≫ lQ i ≫ q i)`
   (`parabolic_eq_splitComponentCocharacter`). Let `ζ_i = f₀ ∘ ν_i`, a cocharacter of
   `T₀` (`cocharacterMapInt`). Since `lQ i ≫ q i = l ≫ p` and
   `f₀ ≫ i₀ = a ≫ l ≫ p`, the composite `ζ_i ≫ i₀` equals `ν_i ≫ a ≫ lQ i ≫ q i`. Hence
   `range (q i) = P_G(ζ_i ≫ i₀)` for every `i`, all in the one torus `T₀`.

3. *Sign sets.* Put `sign i = {α ∈ roots | 0 ≤ ⟨α, ζ_i⟩}`, a subset of `roots`. If
   `sign i = sign j`, then every relative root `α` of `T₀` has `0 ≤ ⟨α, ζ_i⟩` exactly when
   `0 ≤ ⟨α, ζ_j⟩`. The first conjunct of the published `relativeRootSignInclusions`, applied
   to `T₀` in both orders, gives both inclusions of dynamic parabolics. So
   `P_G(ζ_i ≫ i₀) = P_G(ζ_j ≫ i₀)`, hence `range (q i) = range (q j)`, and the injectivity
   hypothesis gives `i = j`.

4. *Count.* `sign` maps `Fin n` injectively into `roots.powerset`.
   `Finset.card_le_card_of_injOn` and `Finset.card_powerset` give `n ≤ 2 ^ roots.card`.

The proof generalizes the published `maximalLeviParabolicCount_core` (at most two
parabolics for a maximal Levi) and step 4 of `MaximalLeviConeComplementLine.range_eq_of_line`.
Those compare the root signs of two members on the torus of one presentation. Here the
torus is the one of the given pair `(p, l)`, so that the bound is fixed before the family.
The axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source

Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026), V.3.1, printed
pp.109–111 / PDF pp.115–117, states that `P(M)` is finite and refers to Borel–Tits and
Springer. The statement Markdown sketches a proof by parabolic subsets of the relative
root system of `A_M`. The implemented proof does not construct that bijection or count
`P(M)` exactly. It proves only the uniform bound requested by the statement, through
nonnegative root-sign sets on one maximal split torus.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.LeviSplitComponentRecallStatements` | the target `LeviParabolicFiniteStatement` |
| `Langlands.GroupScheme.Rational.SplitComponentProof` | `splitComponentStatement` |
| `Langlands.GroupScheme.Rational.ParabolicRootPresentationProof` | `parabolicRootPresentationExistence` |
| `Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter` | `splitComponentCocharacter`, `parabolic_eq_splitComponentCocharacter` |
| `Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof` | `relativeRootSignInclusions` |
| `Langlands.GroupScheme.Rational.RootSupportFiniteness` | `IsSplitTorus.finite_relativeRoots` |
