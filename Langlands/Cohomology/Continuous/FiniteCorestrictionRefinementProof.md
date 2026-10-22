# Proof of refinement compatibility for finite-stage corestriction

Proof authors: Worker 258 wrote this module. Worker 222 wrote the general
corestriction–inflation theorem
`Langlands.Continuous.ordinaryCohomologyCorestriction_comp_map` in the module
`Langlands.Cohomology.Continuous.CorestrictionInflation`. This module imports
that theorem and applies it. Worker 22 wrote the target statement, which was
published in Library commit `15eedb12537594b6a2fc1e60d81c041b5989d6c0`. This
proof imports the statement and its dependencies unchanged, by Lean module name.

`Langlands.Continuous.finiteCorestrictionRefinement` proves exactly the imported
proposition `Langlands.Continuous.FiniteCorestrictionRefinement.{u}`, with no
additional hypothesis. The universe `u` is arbitrary. The proposition covers
every commutative ring `k` and every compact topological group `G`. It also
covers every `A : Rep k G`, every open subgroup `H`, every pair of open normal
subgroups `M ≤ N` with `N ≤ H`, and every natural degree `q`, including `q = 0`.

## Notation

Let `L` be `M` or `N`. Write `A^L` for `finiteQuotientRep A L`, the
`G/L`-representation on the `L`-fixed vectors. Write `K_L` for the actual image
subgroup `H.map (QuotientGroup.mk' L)` of `G/L`. Write `T_L` for
`quotientSubgroupCohomologyIso A H L`, the published isomorphism

```
H^q(H/(H ∩ L), (res_H A)^(H ∩ L))  ≅  H^q(K_L, res A^L).
```

Write `Cor_L` for `Tate.ordinaryCohomologyCorestriction K_L A^L q`. By
definition, `finiteCorestriction A H L _ q` is `T_L.hom ≫ Cor_L`. Its finite
enumeration of `(G/L)/K_L` is `Fintype.ofFinite`, from compactness.

Write `Inf_sub` for the subgroup inflation
`finiteInflation (Rep.res H.subtype A) q (restrictOpenNormal_le H hMN)`. Write
`Inf` for the ambient inflation `finiteInflation A q hMN`, which is
`groupCohomology.map (quotientTransition hMN) (fixedTransition A hMN) q`.

## Auxiliary declarations

- `imageQuotientTransition H hMN : K_M →* K_N` restricts the transition
  `quotientTransition hMN : G/M →* G/N` to the image subgroups, via
  `MonoidHom.codRestrict`.
- `imageFixedTransition A H hMN` has the same underlying linear map as
  `fixedTransition A hMN`, the inclusion `A^N ⊆ A^M`. It is regarded as a
  morphism of `K_M`-representations, from the restriction of `A^N` along
  `imageQuotientTransition` to the restriction of `A^M`.
- `finiteSubgroupCohomologyIso A H N hNH q` is an abbreviation for
  `quotientSubgroupCohomologyIso A H N hNH q`. Its source is written as the
  finite-stage object
  `finiteQuotientRep (Rep.res H.subtype A) (restrictOpenNormal H N)`, which is
  definitionally the published source. The abbreviation adds no mathematics:
  without it, composing the published isomorphism with `finiteInflation` makes
  elaboration time out on this definitional unfolding.

## Transport through the image subgroups

`finiteSubgroupCohomologyIso_inv_finiteInflation` states

```
T_N.inv ≫ Inf_sub = map(imageQuotientTransition, imageFixedTransition) ≫ T_M.inv.
```

`quotientSubgroupCohomologyIso` is a `groupCohomology.mapIso`, and
`finiteInflation` is a `groupCohomology.map`. After unfolding them,
`groupCohomology.mapIso_inv` and `← groupCohomology.map_comp` turn each side
into a single `groupCohomology.map`. `groupCohomology.map_congr` then leaves two
goals. The first is an equality of group homomorphisms
`H/(H ∩ M) →* K_N`. Monoid-hom extensionality on the quotient reduces it to
elements of `H`, and both sides send `h` to the class of `h` modulo `N`
definitionally. The second is an equality of underlying linear maps; both are
the inclusion of fixed vectors, so it holds by `rfl`.

`finiteInflation_finiteSubgroupCohomologyIso_hom` follows by `Iso.inv_comp_eq`.
It is the forward form

```
Inf_sub ≫ T_M.hom = T_N.hom ≫ map(imageQuotientTransition, imageFixedTransition).
```

## Main theorem

The proof applies `ordinaryCohomologyCorestriction_comp_map` with these inputs:

- `Γ = G/M`, `Δ = G/N`, and `π = quotientTransition hMN`. The map `π` is
  surjective because every class lifts to `G`.
- `K = K_N` and `K' = K_M`, with `hK : g ∈ K_M ↔ π g ∈ K_N`. The backward
  direction uses `N ≤ H`. Suppose `π(xM) = hN` with `h ∈ H`. Then
  `h⁻¹x ∈ N ⊆ H`, so `x ∈ H`.
- `π' = imageQuotientTransition H hMN`. Its compatibility with `π` holds by
  `rfl`.
- `A^N` and `A^M` as coefficients, with `φ = fixedTransition A hMN` and
  `φ' = imageFixedTransition A H hMN`. Their linear maps agree by `rfl`.

It gives `Cor_N ≫ Inf = map(imageQuotientTransition, imageFixedTransition) ≫ Cor_M`.

Unfold `finiteCorestriction` and `quotientCorestriction`, using the same
`Fintype.ofFinite` instances that the definition uses. The goal becomes

```
Inf_sub ≫ (T_M.hom ≫ Cor_M) = (T_N.hom ≫ Cor_N) ≫ Inf.
```

Rewriting with the forward transport lemma and reassociating turns the left side
into `T_N.hom ≫ map(imageQuotientTransition, imageFixedTransition) ≫ Cor_M`.
After cancelling `T_N.hom`, the general theorem closes the goal.

The rewrites identify the comap form `N.comap H.subtype` with the finite-stage
form `restrictOpenNormal H N`. For this they use
`set_option backward.isDefEq.respectTransparency false` at tactic level only. No
statement uses that option. The published `QuotientSubgroupCohomology` module
uses the same option.

## Provenance

The statement's provenance is derived from Serre, *Local Fields*, Greenberg
translation (1979), Chapter VII, Sections 5 and 7, and Chapter X, Section 3. See
the target's Markdown for page references. This proof follows the implemented
Lean route above, not a source proof. The corestriction–inflation compatibility
is proved in Lean in Worker 222's module, not assumed. Pinned environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
