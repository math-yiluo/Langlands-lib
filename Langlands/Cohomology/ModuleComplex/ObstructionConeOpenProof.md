# Openness of first-cohomology vanishing for an obstruction cone: proof

Module `Langlands.Cohomology.ModuleComplex.ObstructionConeOpenProof`, namespace
`Langlands.Cohomology.ModuleComplex.ObstructionCone`. The theorem
`openStatement : OpenStatement.{u}` proves the proposition `OpenStatement` of
`ObstructionConeOpenStatement`. The Lean statement is unchanged.

## Auxiliary lemmas

- `exact_baseChange_of_exact_rTensor`: middle exactness of `a.rTensor k`, `b.rTensor k`
  implies middle exactness of `a.baseChange k`, `b.baseChange k`. The two are related by
  `TensorProduct.comm` through Mathlib's `Function.Exact.iff_of_ladder_linearEquiv`.
- `smul_bijective_of_isUnit`: if `algebraMap A S g` is a unit, then `m ↦ g • m` is bijective
  on every `S`-module `M` with compatible `A`-action.

## Proof of `openStatement`

Let `A`, `(C, d)`, `n`, `F`, `Q`, `δ`, `θ`, `z` and the field `k` be as in `OpenStatement`,
with `HOneVanishes C d δ θ z k`.

1. The published `boundedFlatComplexProjective` gives a bounded complex `(K, dK)` of finite
   projective modules. It also gives a chain map `φ : K → C`, which is a quasi-isomorphism
   in its elementwise sense. Each `K i` is flat.
2. `QuasiIsoModule.rTensor_quasiIso` gives `Transfer.CohIso K C dK d φ N` for every
   `A`-module `N`.
3. `Transfer.exists_transfer`, with `N = Q` and `N = F`, gives `zh`, `w`, `θh`, `v`.
   `Transfer.hOneVanishes_model`, with `N = k`, gives `HOneVanishes K dK δ θh zh k`.
4. Choose a surjection `p : A^{n₀} → Q`. The kernel of `p` is finite because `A` is
   noetherian, so choose a surjection onto it. This gives `g : A^{n₁} → A^{n₀}` with
   `Function.Exact g p`. Lift `zh` to `z₀ ∈ K 2 ⊗ A^{n₀}` by surjectivity of `p.lTensor`.
5. Form `Model.a dK δ p θh` and `Model.b dK g z₀`. Then:
   - `Model.b_comp_a` shows they form a complex;
   - `Model.exact_aM_bM_iff` and `Model.exact_rTensor_iff` turn the vanishing at `k` into
     middle exactness of their tensor products with `k`;
   - `exact_baseChange_of_exact_rTensor` makes this a statement about base change.
   The terms are `F^∨ × K⁰`, `(A^{n₀})^∨ × K¹` and `(A^{n₁})^∨ × K²`. The first is finite, and
   the other two are finite projective.
6. `ExactSpread.exists_exact_rTensor_spread` gives `g₀ : A` with `algebraMap A k g₀ ≠ 0`.
   For every module on which `g₀` acts bijectively, the tensored model is exact at the
   middle.
7. Let `S` be an `A`-algebra in which `g₀` is a unit, and let `M` be an `S`-module. Then `g₀`
   acts bijectively on `M`. The equivalences of step 5 give `HOneVanishes K dK δ θh zh M`, and
   `Transfer.hOneVanishes_of_model` gives `HOneVanishes C d δ θ z M`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance and inputs

Published Library inputs:
- `boundedFlatComplexProjective`;
- `boundedFlatQuasiIsoBaseChange`, through `QuasiIsoModule`;
- `FibreH0Spread.exists_split_of_baseChange`, through `ExactSpread`.

Everything else is Mathlib. The argument is a linear-algebra form of The Stacks Project,
Artin's Axioms, Lemma 98.23.4 (Tag 07YN), whose proof cites More on Algebra, Lemma 78.4.
The implementation follows the steps above, not the derived-category proof of the source.
