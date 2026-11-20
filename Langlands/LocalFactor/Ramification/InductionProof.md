# Proof of the conductor formula for induced finite-Galois representations

This module proves the published proposition
`Langlands.Ramification.Padic.FiniteGaloisConductorInductionStatement.{uK, uK', uL, uV}`
from `Langlands.LocalFactor.Ramification.InductionStatement`. The final theorem is

```lean
theorem Langlands.Ramification.Padic.finiteGaloisConductorInduction :
    FiniteGaloisConductorInductionStatement.{uK, uK', uL, uV}
```

The four universe levels are arbitrary and independent. The proof adds no hypothesis
beyond those of the statement. In the statement's notation, for `G = Gal(F/K)`,
`H = Gal(F/K')`, `φ = AlgEquiv.restrictScalarsHom K : H →* G` and a finite-dimensional
complex representation `ψ` of `H`, it proves

```
a_K(Ind_H^G ψ) = dim ψ · a_K(Ind_H^G 1_H) + ([G : G_0] / [H : H_0]) · a_K'(ψ).
```

This is Serre, *Local Fields* (1979), VI §2, Proposition 4 and its Corollary, printed
pp. 101–102, in the derived form explained in `InductionStatement.md`.

## Route

Serre proves the result with characters: he restricts the Artin character to `H` and
applies Frobenius reciprocity. This proof does not use characters. It works directly with
the Library's definition of the conductor as a weighted sum of codimensions of fixed
spaces (Serre VI §2, Proposition 2 and Corollary 1'). It needs three facts:

1. For a normal subgroup `N` of `G`,
   `dim (Ind_H^G ψ)^N = [G : φ(H) N] · dim ψ^(φ⁻¹ N)`.
   This is general representation theory (namespace `Langlands.InducedFixedVectors`).
2. The lower ramification groups of `H` are the preimages of those of `G`, that is
   `H_i = φ⁻¹(G_i)`. This is Serre IV §1, Proposition 2, proved here directly from the
   Library's definition.
3. A rational identity among group orders and indices proves the formula one summand at
   a time.

The hypothesis `IsGalois K F.Carrier` in the statement is introduced but not used.

## Imports

- `Langlands.LocalFactor.Ramification.InductionStatement`: the target, and through it
  the Library modules `Langlands.LocalFactor.Ramification.Galois` (p-adic conductors and
  lower ramification groups), `Langlands.LocalFactor.Ramification.Conductor` (the finite
  conductor sums) and `Mathlib.RepresentationTheory.Induced` (`Representation.ind`).
- `Mathlib.RepresentationTheory.FiniteIndex`: Mathlib's isomorphism
  `Rep.indCoindIso : ind S.subtype A ≅ coind S.subtype A` for a finite-index subgroup `S`.
- `Mathlib.Tactic.Group` and `Mathlib.Tactic.LinearCombination`: proof tactics only.

## Fixed vectors (section `Fixed`)

`Langlands.fixedVectors ρ K` (Library, `Langlands.Representation.Smooth.Definitions`) is
the subspace of vectors fixed by every element of the subgroup `K`.

- `mem_fixedVectors_iff`: `v ∈ fixedVectors ρ K ↔ ∀ g ∈ K, ρ g v = v`. This unfolds the
  definition through Mathlib's `Representation.mem_invariants`.
- `fixedVectors_bot`: every vector is fixed by the trivial subgroup.
- `fixedVectors_trivial`: every vector of a trivial representation is fixed by every
  subgroup.

## Fixed vectors of a coinduced representation (section `Coind`)

Let `φ : H →* G` be any group homomorphism, `ψ` a representation of `H` on `V` over a
field `k`, and `N` a normal subgroup of `G`. Mathlib's `Representation.coind φ ψ` acts on
the space `coindV φ ψ` of functions `f : G → V` with `f (φ h * g) = ψ h (f g)`, by
`(g • f) x = f (x * g)`.

- `Cosets φ N` is the quotient of `G` by `QuotientGroup.rightRel (φ.range ⊔ N)`. Its
  classes are the right cosets `(φ(H) N) g`. `coset φ N g` is the class of `g`, and
  `Quotient.out` chooses a representative of each class. `coset_out`, `mul_out_inv_mem`
  and `coset_eq_of_mul_inv_mem` restate `Quotient.out_eq`, `Quotient.exact` and
  `Quotient.sound` through `QuotientGroup.rightRel_apply`.
- `exists_factor`: since `N` is normal, every element `x` of `φ.range ⊔ N` has the form
  `φ h * n` with `n ∈ N` (Mathlib's `Subgroup.mem_sup_of_normal_right`). `factor φ N g`
  chooses such an `h` for `x = g * (out of the coset of g)⁻¹`. `factor_spec` records
  `(φ (factor g))⁻¹ * (g * out⁻¹) ∈ N`.
- `apply_eq_of_mem`: if `v` is fixed by `φ⁻¹ N` and `(φ h₁)⁻¹ * φ h₂ ∈ N`, then
  `ψ h₁ v = ψ h₂ v`, because `h₁⁻¹ h₂ ∈ φ⁻¹ N`.
- `fixedCoindToCosets` sends an `N`-fixed `f` to its values `q ↦ f (q.out)` at the
  chosen representatives. Each value is fixed by `φ⁻¹ N`: for `h ∈ φ⁻¹ N`,
  `ψ h (f r) = f (φ h * r) = f (r * (r⁻¹ (φ h) r)) = f r`, using normality of `N` (Mathlib's
  `Subgroup.Normal.conj_mem'`) and that `f` is `N`-fixed.
- `cosetsToFixedCoind` sends a family `v` of `φ⁻¹ N`-fixed vectors to the function
  `g ↦ ψ (factor g) (v (coset g))`. The proof checks that this function lies in `coindV`
  and is `N`-fixed. Both checks reduce, through `apply_eq_of_mem`, to membership in `N` of
  explicit products of the elements given by `factor_spec`.
- `fixedCoindEquiv`: these two linear maps are mutually inverse, so
  `fixedVectors (coind φ ψ) N ≃ₗ[k] (Cosets φ N → fixedVectors ψ (N.comap φ))`.
- `finrank_fixedVectors_coind`: for finite `G` and finite-dimensional `V`,
  `finrank (fixedVectors (coind φ ψ) N) = (φ.range ⊔ N).index * finrank (fixedVectors ψ (N.comap φ))`.
  The proof uses Mathlib's `Module.finrank_pi_fintype`, and it uses
  `QuotientGroup.quotientRightRelEquivQuotientLeftRel` to count the right cosets by the
  index.

## From induction to coinduction (section `Ind`)

Here the field `k : Type` lives in universe `0` (the application uses `k = ℂ`), while
`V : Type uV` keeps an arbitrary universe. Mathlib
(`Mathlib/RepresentationTheory/FiniteIndex.lean`) states `Rep.indCoindIso` for
`A : Rep.{max w u} k S` with `k : Type u`. The first universe parameter of `Rep` is the
universe of the carrier of `A`, so the carrier may lie in any universe of the form
`max w u`. For `k : Type` this is `max w 0 = w`, which is arbitrary. So the isomorphism
applies to `Rep.of (rangeRep hφ ψ)`, whose carrier is `V`, with `w = uV`. A coefficient
field in an arbitrary universe `u` would force the carrier universe to be at least `u`;
fixing `k : Type` removes that constraint. Assume also that `φ` is injective (`hφ`).

- `rangeRep hφ ψ` is `ψ` transported to the subgroup `φ.range` along Mathlib's
  `MonoidHom.ofInjective hφ : H ≃* φ.range`. `rangeRep_ofInjective` evaluates it.
- `indRangeEquiv`: `Representation.ind φ ψ` is equivalent to
  `Representation.ind φ.range.subtype (rangeRep hφ ψ)`. Both spaces are coinvariants of
  the same space `k[G] ⊗ V`. The two `H`- and `φ.range`-actions on it correspond under
  `MonoidHom.ofInjective`, so `Representation.Coinvariants.lift` gives inverse maps in both
  directions. The `G`-actions agree on generators.
- `indCoindEquiv` composes three equivalences:
  - `indRangeEquiv`;
  - Mathlib's `Rep.indCoindIso (Rep.of (rangeRep hφ ψ))`, turned into an equivalence of
    representations by `Representation.equivOfIso`. This needs `φ.range.FiniteIndex`,
    which holds for finite `G`;
  - `LinearEquiv.ofEq`, because the coinduced spaces `coindV φ.range.subtype (rangeRep hφ ψ)`
    and `coindV φ ψ` are equal submodules of `G → V`.
- `finrank_fixedVectors_ind`: for finite `G`, finite-dimensional `V` and normal `N`,
  `finrank (fixedVectors (ind φ ψ) N) = (φ.range ⊔ N).index * finrank (fixedVectors ψ (N.comap φ))`.
  The Library's `Langlands.fixedVectorsEquiv` transports fixed vectors along
  `indCoindEquiv`, and then `finrank_fixedVectors_coind` applies.
- `finrank_ind`: `finrank (IndV φ ψ) = φ.range.index * finrank V`. This is the case
  `N = ⊥`, using `fixedVectors_bot`, `MonoidHom.comap_bot` and the injectivity of `φ`.

## The p-adic part (namespace `Langlands.Ramification.Padic`)

### Conductor as a finite sum

`artinConductor_eq_sum`: for a finite-dimensional complex representation `ρ` of
`G = F.Carrier ≃ₐ[K] F.Carrier` (in any universe) and any `b` with
`lowerRamificationGroup T K i = ⊥` for all `i ≥ b`,

```
artinConductor T K ρ = Σ_(i < b) |G_i| / |G_0| · (dim W - dim W^(G_i)).
```

`Padic.artinConductor` is defined (in `Galois`) as `Ramification.artinConductor T.Integers G ρ`
for the action `integerAction T K`, with three instances whose proofs are private there:
faithfulness of the action, `IsNoetherianRing T.Integers` and `Finite G`. The proof
re-proves these three propositions by the same arguments as the Library module
`InertiaConductorProfile`: faithfulness through `IsFractionRing.ringHom_ext`, the
Noetherian property from the local-field structure `T.localField`, and finiteness from
`Module.Finite.of_restrictScalars_finite`. By proof irrelevance they agree with the
private ones, so `change` exposes `Ramification.artinConductor`. The Library's
`Ramification.artinConductor_eq_sum_range` (module `Conductor`) then gives the sum of
`conductorTerm`s. `Nat.cast_sub` with `Submodule.finrank_le` turns the natural-number
codimension `fixedCodimension` into a difference of rationals.

### Lower ramification groups of the subgroup

`lowerRamificationGroup_comap`: the preimage of `lowerRamificationGroup T K i` under
`AlgEquiv.restrictScalarsHom K` is `lowerRamificationGroup T K' i`. By the Library's
`mem_lowerRamificationGroup`, membership says that `integerAutomorphism σ x - x` lies in
the `(i+1)`-st power of the maximal ideal for every integer `x`. The automorphisms
`integerAutomorphism T K (φ σ)` and `integerAutomorphism T K' σ` of `T.Integers` both send
`x` to `σ x`, so the two conditions coincide.

### The arithmetic identity

`induction_term_identity` is an identity of rational numbers. Write `g_i = |G_i|`,
`h_i = |H_i|`, `d = dim V`, `n = dim V^(H_i)`, `r = [G : φ(H)]`, `I = [G : φ(H) G_i]`,
`J = [H : H_i]`, `a = [G : G_0]` and `b = [H : H_0]`. Assume `g_0 ≠ 0`, `b h_0 ≠ 0`,
`J I = [G : G_i]`, `[G : G_i] g_i = |G|`, `J h_i = |H|`, `a g_0 = |G|` and `b h_0 = |H|`.
Then

```
g_i/g_0 · (r d - I n) = d · (g_i/g_0 · (r·1 - I·1)) + a/b · (h_i/h_0 · (d - n)).
```

The hypotheses give `g_i I / g_0 = a h_i / (b h_0)`; this is the `key` step, proved by
`div_eq_div_iff` and `linear_combination`. The identity is then `(d - n)` times `key`.

### Assembly

`finiteGaloisInducedConductor` proves `FiniteGaloisInducedConductorStatement T K K'` for
fixed data:

1. `φ` is injective (Mathlib's `AlgEquiv.restrictScalarsHom_injective`). `G` is finite
   by instance search from `FiniteDimensional K F.Carrier`, and `H` is finite because it
   injects into `G` (`Finite.of_injective`).
2. The Library's `exists_lowerRamificationGroup_eq_bot` gives `b` with `G_i = ⊥` for
   `i ≥ b`. The same `b` works for `H`, since `H_i = φ⁻¹(⊥) = ker φ = ⊥`.
3. The Library's `lowerRamificationGroup_zero` replaces `inertia T K` and
   `inertia T K'` by `G_0` and `H_0`. The three conductors are expanded by
   `artinConductor_eq_sum`, and the formula is compared summand by summand
   (`Finset.mul_sum`, `Finset.sum_add_distrib`, `Finset.sum_congr`).
4. In each summand, `finrank_ind` and `finrank_fixedVectors_ind` (with `N = G_i`, normal
   by the Library instance `lowerRamificationGroup_normal`) compute all four dimensions.
   `lowerRamificationGroup_comap` identifies `φ⁻¹(G_i)` with `H_i`. `fixedVectors_trivial`
   and `Module.finrank_self` handle the trivial one-dimensional representation.
5. The hypotheses of `induction_term_identity` come from Mathlib's index lemmas.
   `J I = [G : G_i]` uses `Subgroup.index_comap` (`J = [φ(H) : G_i ∩ φ(H)]`, the relative
   index `G_i.relIndex φ.range`), `Subgroup.relIndex_sup_right` (for normal `G_i` this
   equals `[φ(H) G_i : G_i]`) and `Subgroup.relIndex_mul_index`
   (`[φ(H) G_i : G_i] · [G : φ(H) G_i] = [G : G_i]`). The order relations come from `Subgroup.index_mul_card`.
   Nonvanishing comes from `Nat.card_pos` for finite groups.

`finiteGaloisConductorInduction` applies `finiteGaloisInducedConductor` to all data
quantified by the target, which proves
`FiniteGaloisConductorInductionStatement.{uK, uK', uL, uV}`.
