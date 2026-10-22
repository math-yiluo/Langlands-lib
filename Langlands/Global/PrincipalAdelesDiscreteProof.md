# Discreteness and closedness of the principal adeles

Author: Worker 230. Proof contribution to task
`8bec8bd7-bf8c-49ab-b2c7-1c044cd95b76`, revision 1.

The theorem `Langlands.Global.principalAdelesDiscrete` proves the published
statement `Langlands.Global.PrincipalAdelesDiscreteStatement K` for every
universe `u` and every number field `K : Type u`. It uses only the `Field K` and
`NumberField K` assumptions of the statement. Both conjuncts are proved:

- `DiscreteTopology (principalAdeles K)`, for the subspace topology that the
  additive subgroup inherits from `Adeles K`;
- `IsClosed (principalAdeles K : Set (Adeles K))`.

`principalAdeles K` is the published abbreviation for Mathlib's
`AdeleRing.principalSubgroup (𝓞 K) K`, the range of the diagonal embedding
`algebraMap K (Adeles K)`. `Adeles K` keeps Mathlib's topology: the product of
the infinite adele ring, itself the finite product of the archimedean
completions, and the finite adele ring with its restricted-product topology.
Neither the topology nor the diagonal range is replaced.

## Implemented proof

1. `eq_zero_of_forall_mem_adicCompletionIntegers_of_forall_lt_one` is the
   arithmetic core. Let `x : K` be such that its image lies in
   `v.adicCompletionIntegers K` at every finite place `v`, and `w x < 1` at
   every infinite place `w`. Then `x = 0`. Proof: membership in the completed
   integers means `Valued.v x ≤ 1`, by `mem_adicCompletionIntegers`.
   `valuedAdicCompletion_eq_valuation'` identifies this with
   `v.valuation K x ≤ 1`. Mathlib's `mem_integers_of_valuation_le_one` then
   writes `x` as the image of an algebraic integer `a : 𝓞 K`. A number field
   has an infinite place `w`. If `a ≠ 0`, Mathlib's
   `NumberField.InfinitePlace.one_le_of_lt_one` gives `1 ≤ w a`, because
   `z a < 1` for every other place `z`. This contradicts `w a < 1`. That
   Mathlib lemma rests on the product formula
   `∏_w w(a)^{mult w} = |N_{K/ℚ}(a)|` and on the fact that a nonzero algebraic
   integer has norm a nonzero integer.

2. `principalAdelesIsolatingSet K` is a derived auxiliary set. It consists of
   the adeles `a` with `‖a.1 w‖ < 1` for every infinite place `w` and
   `a.2 v ∈ v.adicCompletionIntegers K` for every finite place `v`. It is the
   product of two sets:
   - the set of infinite adeles with every component of norm `< 1`. This is
     `Set.pi univ` of open unit balls over the finite index type of infinite
     places, so it is open by `isOpen_set_pi`;
   - the set of integral finite adeles. It is open by Mathlib's
     `RestrictedProduct.isOpen_forall_mem`, because each
     `v.adicCompletionIntegers K` is open (`Valued.isOpen_valuationSubring`).

   `isOpen_principalAdelesIsolatingSet` records that the product is open.
   `zero_mem_principalAdelesIsolatingSet` records that it contains `0`.

3. `principalAdelesIsolatingSet_inter_principalAdeles` shows that the
   intersection of this set with the principal adeles is `{0}`. Let `x : K`
   with `algebraMap K (Adeles K) x` in the set. Its infinite component at `w`
   is the image of `x` in `w.Completion`. That image has norm `w x`, by
   `WithAbs.norm_toAbs_eq` after simplification. Its finite component at `v`
   is the image of `x` in `v.adicCompletion K`. Step 1 gives `x = 0`.

4. `principalAdeles_discreteTopology`: the principal adeles form a
   topological additive group. By Mathlib's
   `discreteTopology_of_isOpen_singleton_zero`, it suffices that `{0}` is open
   in the subspace topology. By `isOpen_induced_iff`, it suffices that `{0}` is
   the preimage of an open subset of `Adeles K` under the inclusion. Step 3
   shows that `principalAdelesIsolatingSet K` is such a set.

5. `adeles_t2Space`: `Adeles K` is Hausdorff. The infinite adele ring is a
   product of normed fields. The finite adele ring is a restricted product of
   Hausdorff valued fields, which is Hausdorff by Mathlib's restricted-product
   instance. The adele ring is their product. The abbreviation `Adeles`
   unfolds to `NumberField.AdeleRing`. That underlying definition and the
   definitions `InfiniteAdeleRing` and `FiniteAdeleRing` require transporting
   the instances with `inferInstanceAs`.

6. `principalAdeles_isClosed`: a discrete subgroup of a `T1` topological group
   is closed, by Mathlib's `AddSubgroup.isClosed_of_discreteTopology`. This
   uses steps 4 and 5.

7. `principalAdelesDiscrete` pairs steps 4 and 6. Its type is exactly
   `PrincipalAdelesDiscreteStatement K`.

The public theorems `principalAdeles_discreteTopology`,
`principalAdeles_isClosed` and `adeles_t2Space` are named so that downstream
proofs can install them as local instances, for example to use the Hausdorff
quotient `AdeleQuotient K`.

## Scope and provenance

The target statement and its correspondence with Cassels, *Global fields*,
§14, Theorem (p.64), and Weil, *Basic Number Theory*, IV §2, Theorem 2, are
documented in the published `Langlands/Global/AdeleQuotientStatement.md`.
Closedness is the derived conjunct described there.

The proof route differs from Cassels's, who reduces to `ℚ`. Here a single open
neighbourhood of `0` meets `K` only in `0`. This uses global integrality and the
norm bound at the infinite places. `principalAdelesIsolatingSet` is an internal
auxiliary set for this argument, not a definition from the literature. The
proof introduces no new mathematical definition of adeles, of their topology or
of the principal subgroup. It does not prove local compactness of `𝔸_K` or
compactness of `𝔸_K / K`.
