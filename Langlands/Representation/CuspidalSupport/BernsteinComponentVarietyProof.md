# Each component of `Ω(G)` is `X(M)/W` (Renard VI.7.1, Theorem)

Module `Langlands.Representation.CuspidalSupport.BernsteinComponentVarietyProof`.

## Result

`Langlands.CuspidalSupport.bernsteinComponentVariety :
BernsteinComponentVarietyStatement.{uF, uV}`

This proves the published statement `Langlands.CuspidalSupport.BernsteinComponentVarietyStatement`
(Renard 2026, French version dated 9 July 2026, VI.7.1, Theorem, printed pp.180–181 / PDF
pp.186–187). The universes are the statement's, and no hypothesis is added. Only the standard
axioms `propext`, `Classical.choice` and `Quot.sound` are used.

For a standard cuspidal datum `a = (M, ρ)` of a standard family, write:

- `X = X(M)` for the unramified characters of `M(F)`;
- `ℂ[X]` for `unramifiedRegularFunctions`;
- `ω ~ ω'` when some self-conjugacy `c` of `M` gives `ρ ⊗ ω ≅ (ρ ⊗ ω')^c`.

The theorem gives:

1. a finite group `W` of permutations of `X` that preserves `ℂ[X]` and whose orbits are the
   classes of `~`;
2. the `~`-invariant elements of `ℂ[X]` form a finitely generated `ℂ`-algebra that is a domain,
   whose `ℂ`-points are evaluations and which separates the classes;
3. the components clause for every other datum `a'`.

## Generic part (namespace `Langlands.CuspidalSupport.ComponentWeyl`)

Throughout, `j : H ⟶ G` is an arbitrary group-scheme homomorphism and `ρ` is a smooth
representation of `H(F)`.

- `weyl_and_variety j ρ hj hN hS hFT hD hK` proves conclusions 1 and 2 for `(j, ρ)`. It assumes
  `[IsTopologicalGroup H(F)]` and:
  - `hj`: `j.hom.hom` is a monomorphism;
  - `hN`: finitely many normalizer representatives modulo `j(H(F))`;
  - `hS`: the unramified stabilizer of `ρ` is finite;
  - `hFT`, `hD`: `ℂ[X(H)]` is finitely generated and a domain;
  - `hK`: the common norm kernel of `H(F)` is open.

  *Proof.* Take `W = weylGroup j ρ` from `BernsteinComponentWeylGroup`. Its finiteness is
  `weylGroup_finite`, its preservation of `ℂ[X]` is `weylGroup_comp_mem_regular`, and the
  description of its orbits is `assoc_iff_exists_weylGroup`. Then apply
  `InvariantFunctions.exists_invariantSubalgebra` (module `FiniteGroupInvariantFunctions`) to
  `R = ℂ[X(H)]` and `W`. The required evaluation property is
  `unramifiedRegularFunctions_algHom_eq_eval` (using `hK`), and separation is
  `unramifiedRegularFunctions_separates` (module `UnramifiedRegularFunctionPoints`). The
  `W`-invariant functions are exactly the `~`-invariant ones, because the orbits are the
  classes.
- `component_transfer j ρ j' ρ'` proves conclusion 3 for a second pair `(j', ρ')`. It
  states the inertia relation as `∃ c : RationalLeviConjugacy j j',
  IsRationalInertiaRelated H ρ (rationalIsoPullback c.iso ρ')`, which is the definition of
  `IsBernsteinInertiaRelated`.
  - *Key step (`hreach`):* if `ρ'^c ≅ ρ ⊗ χ₀`, then
    `(ρ' ⊗ ω')^c ≅ ρ ⊗ (χ₀ · (ω' ∘ c))` for every `ω'`. This combines `pullback_twist`,
    `twist_congr`, `twist_twist` and commutativity.
  - *Associated twists ⇒ inertia:* from `ρ ⊗ ω ≅ (ρ' ⊗ ω')^c`, the character
    `(ω' ∘ c)⁻¹ · ω` exhibits `ρ'^c` as a full twist of `ρ`.
  - *Inertia ⇒ associated twists:* take `ω = χ₀` and `ω' = 1`.
  - *Every twist of `a'` is reached:* the key step with `ω = χ₀ · (ω' ∘ c)`.
  - *Transfer of invariant functions:* set `f'(ω') = f(χ₀ · (ω' ∘ c))`. It lies in
    `ℂ[X(M')]` by `comp_affine_mem_regular`. Suppose `ω` is associated to `ω'` through `c'`.
    Then `ω ~ χ₀ · (ω' ∘ c)` through the self-conjugacy `c'.trans c.symm`, using the key step,
    `rationalIsoPullbackCancelIso` and `rationalIsoPullbackTransIso`. So invariance of `f`
    gives `f'(ω') = f(ω)`.

## Specialization (theorem `Langlands.CuspidalSupport.bernsteinComponentVariety`)

Introduce the data and set `j = Standard.leviHom i ν (rootSet i ν a.roots)`, typed as a
morphism out of `M = bernsteinLeviScheme i ν a.roots`. The hypotheses of `weyl_and_variety`
come from published results:

- **Monomorphism, `hj`.** `j` is a closed subgroup (`Standard.isClosedSubgroup_leviHom`), so
  `j.hom.hom.left` is a closed immersion, and `Over.mono_of_mono_left` applies.
- **Reductivity.** `M` is connected reductive by `standardLeviScheme_isConnectedReductive`,
  with the proved `standardCocharacter` and `dynamicCentralizerReductive` and the family's
  data. The instances `IsAffineHom`, `IsAffine`, `LocallyOfFiniteType` and the point topology
  on `M(F)` are restated locally; the statement's `haveI`/`letI` are inlined. `IsTopologicalGroup`
  is `rationalPoint_isTopologicalGroup`.
- **Stabilizer, `hS`.** `rationalTwistStabilizerFinite` (Renard V.2.7) applied to
  `a.irreducible`.
- **Coordinate algebra, `hFT`, `hD`.** `rationalUnramifiedRegularFunctions_finiteType` and
  `rationalUnramifiedRegularFunctions_isDomain`, with continuity from
  `continuous_rationalValuationImageProjection`.
- **Open kernel, `hK`.** `isOpen_rationalCommonNormKernel`.
- **Normalizer representatives, `hN`.**
  - `exists_isSplitComponent` gives a split component `a₀ : A ⟶ M`.
  - `standardCocharacter` gives a cocharacter `ζ` with
    `standardLevi = Dynamic.centralizer (ζ ≫ i)`. Rewriting `Standard.isRepresentedBy_leviHom`
    with this identity shows that `j` represents that centralizer.
  - Then `IsSplitComponent.torusCentralizer_comp_eq_of_dynamicCentralizer` gives
    `torusCentralizer (a₀ ≫ j) = range j`.
  - `IsSplitComponent.exists_finite_normalizer_representatives` gives the representatives;
    its second conjunct is `hN`.

The first two conjuncts of the goal are the two components of `weyl_and_variety`. For each
`a'`, restate the instances of its Levi and apply `component_transfer` with
`j' = Standard.leviHom i ν (rootSet i ν a'.roots)`.

The proof passes `H := bernsteinLeviScheme i ν a.roots` explicitly, and likewise `H'`. The
generic statements then mention the same Levi term as the target statement, which avoids
costly unfolding of `unramifiedRegularFunctions` during unification.

## Dependencies added with this proof

- `Langlands/Representation/CuspidalSupport/FiniteGroupInvariantFunctions.lean`
- `Langlands/Representation/Plancherel/UnramifiedRegularFunctionPoints.lean`
- `Langlands/Representation/CuspidalSupport/BernsteinComponentWeylGroup.lean`
