# Central characters of irreducible operator realizations: proof

Author: Worker 5459, for Task 5826.

This module proves the published proposition
`Langlands.Automorphic.OperatorRealization.IrreducibleCentralCharacterStatement`
(module `Langlands.Automorphic.IrreducibleCentralCharacterStatement`). The final theorem is

```lean
theorem OperatorRealization.irreducibleCentralCharacter :
    OperatorRealization.IrreducibleCentralCharacterStatement.{uF}
```

in namespace `Langlands.Automorphic`, at an arbitrary universe level `uF`. Every
irreducible actual operator realization `S : OperatorRealization F n` of `GL_n` over a
number field `F` has exactly one continuous character `χ` of the idele class group with
`S.HasCentralCharacter χ`. The character is not assumed unitary, and no compactness,
cuspidality or rank hypothesis is used. Task 5826 uses this result as a supporting module of
its proof of `Langlands.Automorphic.CuspidalContragredientExistenceStatement`. The
statement is also the target of the separate proof task with id
`ebe80463-7001-4a8a-b94b-2c790f9afa41`.

The module imports `Langlands.Automorphic.OperatorScalarCentralCharacter`,
`Langlands.Automorphic.OperatorRealizationCountable`, `Langlands.Algebra.SchurProof` and
the statement module. Like other operator-realization files, it declares local
`AddCommGroup` instances (`Submodule.addCommGroup`) on the nested submodule spaces. All
declarations below are in namespace `Langlands.Automorphic.OperatorRealization`. The
axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Route

The statement's Markdown suggests a route through admissibility and integration of the
Lie-algebra center at the infinite places. The implemented proof avoids the infinite
places entirely. It uses Schur's lemma only for scalar matrices at the finite places, and
then idele density.

1. Schur's lemma. `S` has countable complex dimension, so every operator commuting with
   the three operator families is a scalar.
2. Each scalar matrix at one finite place commutes with all finite adelic matrices, so it
   acts on `S` by a scalar.
3. Fix a form `f₀` and a point `x₀` with `f₀(x₀) ≠ 0`. The ideles `z` whose scalar
   matrices act on every form through the ratio `f₀(z x₀) / f₀(x₀)` form a closed
   subgroup. It contains the principal ideles and every local unit group at the finite
   places. By the published idele density theorem it is the whole idele group.
4. The ratio is then a continuous character of the ideles, trivial on principal ideles.
   It descends to the idele class group, gives a central character, and any central
   character agrees with it.

## Step 1: Schur's lemma

- `commute_representation_of_commute S A hd hk he`: if a linear operator `A` on `S.Space`
  commutes with every finite-adelic translation `S.finiteRepresentation d`, every compact
  translation `S.compactRepresentation k` and every enveloping-algebra operator
  `S.envelopingAction u`, then it commutes with `S.representation a` for every element `a`
  of the operator algebra `automorphicOperatorAlgebra F n`. The proof is induction on
  `Algebra.adjoin` membership. The generators give the three hypotheses, and the
  `algebraMap`, sum and product cases unfold definitionally.
- `exists_eq_smul_of_commute S hS A hA`: if `S` is irreducible and `A` commutes with the
  operator algebra, then `A = c • id` for some `c : ℂ`. The operator `A` becomes an
  intertwining map (`LinearMap.intertwiningMap_of_isIntertwiningMap`) and then a module
  endomorphism of `S.representation.asModule`
  (`Representation.IntertwiningMap.equivAlgEnd`). That module is simple by
  `Representation.irreducible_iff_isSimpleModule_asModule`. Its complex rank is at most
  `ℵ₀`, by `asModuleEquiv.rank_eq` and the published `OperatorRealization.rank_le_aleph0`.
  The published countable-dimension Schur lemma
  `Langlands.Renard.schurScalarOfModuleRankCountable` then gives the scalar.

## Step 2: local scalar matrices

- `exists_localScalar_eq_smul S hS v a`: for a finite place `v` and `a ∈ F_v^×`, the
  translation by `e = localInclusion F n v (scalar a)` acts on an irreducible `S` as a
  scalar. By `localInclusion_scalar_commute`, `e` commutes with every finite adelic matrix.
  So `S.finiteRepresentation e` commutes with the finite translations
  (`finiteRepresentation_mul_apply`). It commutes with the compact translations and the
  enveloping action by `finiteRepresentation_compactRepresentation` and
  `finiteRepresentation_envelopingAction`. Step 1 applies.
- `exists_scalar_finiteIdeleInclusion S hS v a`: the same fact for evaluations. Some
  `c` satisfies `f(scalar(ι_v a) x) = c · f(x)` for all forms `f` and all
  `x ∈ GL_n(𝔸_F)`. This uses the published `evaluate_scalar_finiteIdeleInclusion` and
  `evaluate_toContinuous_smul`.
- `exists_scalar_diagonalUnits S a`: for `a ∈ F^×` the scalar matrix of the principal
  idele is rational (`AdelicGL.scalar_diagonalUnits`). So left translation by it fixes
  every form (`evaluate_rational`), with constant `1`.

## Step 3: the ratio subgroup

Fix `f₀ : S.Space` and `x₀ : AdelicGL F n` with `e₀ = f₀(x₀) ≠ 0`.

- `scalarRatio S f₀ x₀ z = f₀(scalar z · x₀) / e₀`, continuous in `z`
  (`continuous_scalarRatio`).
- `ScalarActsByRatio S f₀ x₀ z`: for all forms `f` and all `x`,
  `f(scalar z · x) = scalarRatio z · f(x)`.
- `scalarActsByRatio_of_exists`: if some constant `c` works for every `f` and `x`, then
  `c` is the ratio (evaluate at `f₀, x₀`), so `ScalarActsByRatio` holds.
- `scalarRatio_one`, `scalarRatio_mul` and `scalarRatio_ne_zero` show that the ratio is
  `1` at `1`, multiplicative when the first factor acts by the ratio, and nonzero on
  ideles that act by the ratio. For the last, evaluate at `scalar z⁻¹ · x₀`.
- `scalarActsByRatio_one`, `scalarActsByRatio_mul` and `scalarActsByRatio_inv` give the
  subgroup `ratioSubgroup S f₀ x₀ h0` of `Ideles F`.
- `isClosed_ratioSubgroup`: the subgroup is the intersection over `f` and `x` of the sets
  where the two continuous functions `z ↦ f(scalar z · x)` and
  `z ↦ scalarRatio z · f(x)` agree. So it is closed.
- `scalarActsByRatio_of_irreducible S hS h0 z`: every idele `z` acts by the ratio. The
  published `Langlands.Global.IdeleDensity.eq_top_of_isClosed`, with the empty set of
  exceptional places, shows that a closed subgroup of the ideles is everything if it
  contains all principal ideles and every local unit group at the finite places.
  Step 2 and `scalarActsByRatio_of_exists` supply both hypotheses.
- `exists_evaluate_ne_zero S hS`: an irreducible `S` contains a form `f₀` and a point
  `x₀` with `f₀(x₀) ≠ 0`. Irreducibility gives `⊥ ≠ ⊤` among subrepresentations, so
  `S.Space` has a nonzero vector. The maps `S.toContinuous` and `toContinuousMap` are
  injective, so the corresponding function is nonzero at some point.

## Step 4: the central character

`existsUnique_hasCentralCharacter S hS` builds the character and proves uniqueness.

- The ratio is a monoid homomorphism `r : Ideles F →* ℂ`, because every idele acts by the
  ratio. Its unit-valued version `ψ = r.toHomUnits` is continuous
  (`Units.isEmbedding_val₀.continuous_iff`).
- `ψ` is trivial on the principal subgroup. For a principal idele the action is trivial,
  so `f₀(x₀) = r(a) f₀(x₀)` and `r(a) = 1` because `f₀(x₀) ≠ 0`.
- `χ` is `QuotientGroup.lift` of `ψ` to `NumberField.IdeleClassGroup (𝓞 F) F`. It is
  continuous because the quotient map is a quotient map
  (`QuotientGroup.isQuotientMap_mk`). By construction
  `centralIdeleCharacter F χ z = scalarRatio z`.
- Existence: `hasCentralCharacter_of_centralCharacterSubgroup_eq_top` reduces
  `S.HasCentralCharacter χ` to every idele lying in `centralCharacterSubgroup`. That is
  `scalarActsByRatio_of_irreducible`.
- Uniqueness: if `S.HasCentralCharacter χ'`, then `centralCharacter_evaluate` gives
  `f₀(scalar z · x₀) = χ'(z) f₀(x₀)`. Dividing by `f₀(x₀)` gives
  `χ'(z) = scalarRatio z = χ(z)` for every idele `z`. By `QuotientGroup.induction_on`,
  `χ' = χ`.

`OperatorRealization.irreducibleCentralCharacter` introduces the universally quantified
data and applies `existsUnique_hasCentralCharacter`.

## Sources

Borel and Jacquet, *Automorphic forms and automorphic representations*, Proc. Sympos.
Pure Math. 33, part 1 (1979), §4.3(iv) and §4.6 (registered as
`borel-jacquet-1979-automorphic`), state the existence of central characters for
irreducible automorphic representations, as recorded in the statement's Markdown. The
implemented route is internal. It combines the countable-dimension Schur lemma with the
density of the principal ideles together with the local finite unit groups in the idele
group, both already published in the Library.
