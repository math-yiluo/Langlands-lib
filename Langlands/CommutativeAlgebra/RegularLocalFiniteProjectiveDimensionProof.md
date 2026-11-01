# Proof: finite modules over regular local rings have finite projective dimension

This module proves the Library proposition
`Langlands.CommutativeAlgebra.RegularLocalFiniteProjectiveDimensionStatement.{u}`
from `Langlands.CommutativeAlgebra.RegularLocalFiniteProjectiveDimensionStatement`:

```lean
theorem regularLocalFiniteProjectiveDimension :
    RegularLocalFiniteProjectiveDimensionStatement.{u}
```

That is, for every commutative ring `R : Type u` with `IsRegularLocalRing R`
and every finite `R`-module `M : Type u`, there is `n : ℕ` with
`HasProjectiveDimensionLE (ModuleCat.of R M) n`. The proof gives an explicit
bound: `n` can be the number of generators of the maximal ideal,
`(maximalIdeal R).spanFinrank`, which equals the Krull dimension of `R`. No
hypotheses are used beyond those in the statement.

The module imports the statement module, the Library module
`Langlands.CommutativeAlgebra.RegularLocalDomainProof` (for `regularLocalDomain`
and one auxiliary lemma), `Mathlib.RingTheory.Regular.ProjectiveDimension` and
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.

## Provenance and route

The statement is the finite-module part of Stacks Project Proposition 10.110.1
(Tag 00O7). The Stacks proof cites Lemma 10.106.6 (Tag 00NT) and Lemma
10.104.9 (Tag 00NG). This proof does not follow that route. It takes a
different, standard route: induction
on the number of generators of the maximal ideal, passing to `R ⧸ (x)` for one
element `x ∈ m \ m²` and using a change-of-rings bound. The Lean arrangement was
written for this module. The ingredients are Mathlib results, plus two results
from the Library's `RegularLocalDomainProof`.

## Change of rings

The section `ChangeOfRings` (namespace
`Langlands.CommutativeAlgebra.RegularLocalFiniteProjectiveDimension`) works over
any commutative ring `R : Type u` and any `x : R`. It has no local or regular
hypothesis. Throughout, `res x` is restriction of scalars
`ModuleCat (R ⧸ Ideal.span {x}) ⥤ ModuleCat R` along the quotient map
(`ModuleCat.restrictScalars`).

- `shortExact_map_res`: `res x` sends short exact sequences to short exact
  sequences. Exactness, injectivity and surjectivity are statements about the
  underlying functions, and these do not change
  (`ModuleCat.shortComplex_shortExact`).
- `finsuppReduce x I`: the `R`-linear map `(I →₀ R) → res x (I →₀ R ⧸ (x))`
  that reduces each coordinate mod `x` (`Finsupp.mapRange` of the quotient map).
- `hasProjectiveDimensionLT_res_finsupp`: if `x` is `R`-regular
  (`IsSMulRegular R x`), then for every `I : Type u`, the restriction of the
  free module `I →₀ R ⧸ (x)` has projective dimension `< 2` over `R`. The proof
  checks that `0 → (I →₀ R) --x--> (I →₀ R) --finsuppReduce--> res x (I →₀ R ⧸ (x)) → 0`
  is short exact. Injectivity of multiplication by `x` is coordinatewise
  regularity. Exactness in the middle divides every coordinate in `(x)` by `x`;
  the chosen quotients form a finitely supported vector because the chosen
  quotient of `0` is `0`, which again uses regularity. Surjectivity is
  surjectivity of `Finsupp.mapRange`. Since the middle term is free, Mathlib's
  `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃` gives the bound.
- `hasProjectiveDimensionLT_res_of_projective`: if `x` is `R`-regular and `N`
  is a projective `R ⧸ (x)`-module, then `res x N` has projective dimension
  `< 2`. `N` is a retract of the free module `N →₀ R ⧸ (x)`: the retraction is
  `Finsupp.linearCombination`, and the section comes from
  `Projective.factorThru`. The retract is mapped along `res x` (`Retract.map`),
  and `Retract.hasProjectiveDimensionLT` transfers the bound from the previous
  lemma.
- `hasProjectiveDimensionLE_res`: if `x` is `R`-regular and an
  `R ⧸ (x)`-module `N` has projective dimension `≤ n`, then `res x N` has
  projective dimension `≤ n + 1`. This is induction on `n`, for all `N` at once.
  - `n = 0`: `N` is projective (`projective_iff_hasProjectiveDimensionLE_zero`),
    so the previous lemma applies.
  - `n + 1`: take the short exact sequence `0 → K → (N →₀ R ⧸ (x)) → N → 0`,
    where the map is `Finsupp.linearCombination` and `K` its kernel
    (`LinearMap.shortExact_shortComplexKer`). Then `K` has projective dimension
    `≤ n` (`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁`), so
    `res x K` has projective dimension `≤ n + 1` by induction. The free middle
    term restricts to dimension `< 2 ≤ n + 3`. Applying `res x` to the
    sequence (`shortExact_map_res`) and then
    `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃` gives
    `res x N` dimension `≤ n + 2`.

## Regular local rings

`hasProjectiveDimensionLE_of_spanFinrank_eq d` (same namespace): for every
regular local ring `R : Type u` with `(maximalIdeal R).spanFinrank = d` and every
finite `R`-module `M : Type u`, `HasProjectiveDimensionLE (ModuleCat.of R M) d`.
The proof is strong induction on `d`, for all such `R` and `M` at once. Write
`m = maximalIdeal R`.

- `d = 0`: then `m = ⊥` (`Submodule.spanFinrank_eq_zero_iff_eq_bot`, since `m`
  is finitely generated), so `R` is a field (`isField_iff_maximalIdeal_eq`).
  With this field structure as a local instance, instance search shows that
  `ModuleCat.of R M` is projective, and so its projective dimension is `≤ 0`.
- `d > 0`:
  1. `m ≠ m²`. Otherwise `m ≤ m • m`, and Nakayama's lemma
     (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) gives `m = ⊥`, hence
     `d = 0`. So there is `x ∈ m` with `x ∉ m²`.
  2. `R` is a domain (`regularLocalDomain`, from the Library), and `x ≠ 0`.
  3. `R ⧸ (x)` is a nontrivial local ring, because `x` is not a unit
     (`IsLocalRing.of_surjective'`). It is regular, and its maximal ideal has
     `m' < d` generators, where `m' = (maximalIdeal (R ⧸ (x))).spanFinrank`.
     The Library lemma
     `RegularLocalDomain.spanFinrank_maximalIdeal_quotient_add_one_le` gives
     `m' + 1 ≤ d`. Krull's height theorem
     (`Ideal.height_le_ringKrullDim_quotient_add_one` with
     `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`) gives
     `dim R ≤ dim (R ⧸ (x)) + 1`, and `dim R = d` by regularity of `R`
     (`IsRegularLocalRing.spanFinrank_maximalIdeal`). Together these give
     `m' ≤ dim (R ⧸ (x))` in `ℕ∞` (the dimension is not `⊥` since the ring is
     nontrivial). So `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` makes
     `R ⧸ (x)` regular.
  4. Choose a surjection `f : (Fin k → R) → M` (`Module.Finite.exists_fin'`)
     and let `K = ker f`. This gives the short exact sequence
     `0 → K → R^k → M → 0` (`LinearMap.shortExact_shortComplexKer`). `K` is
     finite over the Noetherian ring `R`. `x` is `K`-regular
     (`IsSMulRegular.of_ne_zero`), because `K` is a submodule of the
     torsion-free module `R^k` over the domain `R`.
  5. `QuotSMulTop x K = K ⧸ xK` is an `R ⧸ (x)`-module; its scalar tower over
     `R` holds by `rfl`. It is finite over `R ⧸ (x)`
     (`Module.Finite.of_restrictScalars_finite`). By the induction hypothesis
     at `m' < d`, its projective dimension over `R ⧸ (x)` is `≤ m'`.
  6. By `hasProjectiveDimensionLE_res` (`x` is `R`-regular because `R` is a
     domain and `x ≠ 0`), its restriction to `R` has projective dimension
     `≤ m' + 1`. This restriction is the `R`-module `QuotSMulTop x K` under the
     identity linear equivalence, and `ModuleCat.hasProjectiveDimensionLE_of_linearEquiv`
     transfers the bound.
  7. Mathlib's `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular`
     (for a finite module over a Noetherian local ring and a regular element in
     the maximal ideal) gives `pd (K ⧸ xK) = pd K + 1`. So `pd K + 1 ≤ m' + 1`
     in `WithBot ℕ∞`, hence `pd K ≤ m'` (`ENat.WithBot.add_le_add_one_right_iff`,
     with `projectiveDimension_le_iff` translating between `projectiveDimension`
     and `HasProjectiveDimensionLE`).
  8. `R^k` is projective, so its dimension is `< m' + 2`. The short exact
     sequence of step 4 and `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃`
     give `pd M ≤ m' + 1 ≤ d` (`hasProjectiveDimensionLT_of_ge`).

## Final theorem

`regularLocalFiniteProjectiveDimension` takes `R`, `M` and the instances from
the statement and returns
`⟨_, hasProjectiveDimensionLE_of_spanFinrank_eq _ R rfl M⟩`, with
`n = (maximalIdeal R).spanFinrank`.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.
