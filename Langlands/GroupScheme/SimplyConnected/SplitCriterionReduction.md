# Reduction of the coroot criterion to torus lifting and root-datum morphisms

This module is a derived, conditional assembly step toward the published
`SplitCorootSpanSimplyConnectedStatement`
(`Langlands.GroupScheme.SimplyConnected.SplitCriterionStatement`), the sufficiency half
of the coroot criterion for simple connectedness. Its main declaration,
`splitCorootSpanSimplyConnected_of_rootDatumHom`, is a `def` whose value is a proof (the
`linter.defProp` linter is switched off for it, as in other conditional assemblies of the
Library). It proves

```
RootDatumExistenceStatement.{u} → CentralIsogenySplitMaximalTorusLiftStatement.{u} →
  CentralIsogenyRootDatumHomStatement.{u} → SplitCorootSpanSimplyConnectedStatement.{u}
```

It does **not** prove any premise. All three are published Library statements whose
proofs are separate obligations:

* `RootDatumExistenceStatement`
  (`Langlands.GroupScheme.Reductive.RootDatumStatement`): a connected reductive group
  over a field with a split maximal torus `i` has a finite, reduced Mathlib root datum
  `P` with `IsRootDatumOf i P`;
* `CentralIsogenySplitMaximalTorusLiftStatement`
  (`Langlands.GroupScheme.CentralIsogeny.SplitTorusLiftStatement`): for a central
  isogeny `π : G ⟶ H` of connected reductive groups and a split maximal torus
  `i : S ⟶ H`, there are a split maximal torus `j : T ⟶ G` and `f : T ⟶ S` with
  `j ≫ π = groupHom f ≫ i`;
* `CentralIsogenyRootDatumHomStatement`
  (`Langlands.GroupScheme.CentralIsogeny.SplitRootDatumStatement`): for a central
  isogeny `φ : G ⟶ G'` of connected reductive groups compatible with split maximal tori
  through `t : T ⟶ T'`, and root data `P`, `P'` of the two tori, there is a morphism of
  root pairings `P' ⟶ P` with weight map `χ ↦ t ≫ χ` and coweight map `ν ↦ ν ≫ t`,
  both injective, and `IsIso φ` holds exactly when the weight map is bijective.

No premise mentions simply connected covers, and the proof uses none. This respects the
requirement, recorded in the Markdown of `SplitCorootSpanSimplyConnectedStatement`, that
a proof of the criterion must not use the existence of simply connected covers. The
target statement and every file it imports are unchanged.

## Mathematical model

Milne, *Algebraic Groups* (2017), Proposition 23.29 and its proof, printed p. 493
(PDF p. 509). Let `(G, T)` be split semisimple with diagram `(V, Φ, X)`. A central
isogeny `φ : G' → G` gives a central isogeny of root data
`f : (X, Φ, Φ^∨) → (X', Φ', Φ'^∨)` (Proposition 23.5). Then `f_ℚ` is an isomorphism and
`Q(Φ') = f(Q(Φ)) ⊂ f(X) ⊂ X' ⊂ P(Φ') = f_ℚ(P(Φ))`. If `X = P(Φ)`, then `f(X) = X'`,
so `f` is an isomorphism of root data, and `φ` is an isomorphism by 23.5.
Proposition 23.5 is on printed pp. 485–486 (PDF pp. 501–502). The retained errata
snapshot (`milne-2017-algebraic-groups-errata-2026-11-02`) has no entries for printed
pp. 485, 486 or 493.

The implemented proof follows the same steps with two changes.

* Milne's isogeny of *split* groups includes a split maximal torus `T'` of `G'` mapped
  into `T`. Here `G'` is an arbitrary semisimple group with a central isogeny to `G`,
  so the torus comes from the premise `CentralIsogenySplitMaximalTorusLiftStatement`,
  and its root datum from `RootDatumExistenceStatement`.
* The hypothesis is the coroot form `P.corootSpan ℤ = ⊤` of the statement, not
  `X = P(Φ)`. So the argument runs on cocharacters: the coweight map sends coroots onto
  coroots, the coroots span, and hence the coweight map is onto. Weights are reached by
  transposition. Milne's chain of lattices on the character side is not used.

## Setting

The universe is an arbitrary `u`. In the namespace `SplitCorootCriterion`, `R` is a
commutative ring, `P : RootPairing ι R M N` and `Q : RootPairing ι₂ R M₂ N₂` are
Mathlib root pairings, and `f : RootPairing.Hom P Q` is a Mathlib morphism of root
pairings: a linear `f.weightMap : M →ₗ[R] M₂`, a linear `f.coweightMap : N₂ →ₗ[R] N`
and a bijection `f.indexEquiv : ι ≃ ι₂`. The two maps are transposes for the perfect
pairings of `P` and `Q` (`weight_coweight_transpose`), the weight map sends roots to
roots, and the coweight map sends coroots to coroots (`coroot_coweightMap`).
`P.corootSpan R` is the `R`-span of the coroots of `P`.

## Linear-algebra lemmas (namespace `SplitCorootCriterion`)

* `surjective_coweightMap (f : RootPairing.Hom P Q) (h : P.corootSpan R = ⊤)`: the
  coweight map is surjective. By `coroot_coweightMap_apply`, the coroot `Q.coroot
  (f.indexEquiv j)` is sent to `P.coroot j`. So every coroot of `P` is in the range,
  and the range, a submodule, contains their span, which is everything.
* `surjective_weightMap (f : RootPairing.Hom P Q) (h : Function.Bijective
  f.coweightMap)`: the weight map is surjective. Let `e : N₂ ≃ₗ[R] N` be the coweight
  map as a linear equivalence. For `y : M₂`, the functional `Q.toPerfPair y ∘ₗ e.symm` on
  `N` comes from a unique `m : M` under the perfect pairing `P.toPerfPair`. For every
  `x : N₂`, transposition gives `⟨f.weightMap m, x⟩_Q = ⟨m, f.coweightMap x⟩_P`, and this
  equals `⟨y, e.symm (e x)⟩_Q = ⟨y, x⟩_Q`. Since `Q.toPerfPair` is injective,
  `f.weightMap m = y`.

## Main declaration

`splitCorootSpanSimplyConnected_of_rootDatumHom
(hex : RootDatumExistenceStatement.{u})
(hlift : CentralIsogenySplitMaximalTorusLiftStatement.{u})
(hhom : CentralIsogenyRootDatumHomStatement.{u}) :
SplitCorootSpanSimplyConnectedStatement.{u}`.

Let `G` be semisimple over a field `k`, `i : T ⟶ G` a maximal torus with `T` split,
and `P` a root datum of `i` with `P.corootSpan ℤ = ⊤`. Semisimplicity of `G` is the
first field of `IsSimplyConnected G`. For the second, let `π : H ⟶ G` be a central
isogeny from a semisimple group `H`.

1. `hlift`, applied to `π` and `i` (both groups are connected reductive, as semisimple
   groups), gives a split torus `S`, a maximal torus `j : S ⟶ H` and `t : S ⟶ T` with
   `j ≫ π = groupHom t ≫ i`.
2. `hex`, applied to `H` and `j`, gives a root datum `P'` of `j`. Its finiteness and
   reducedness are not used.
3. `hhom`, applied with source `H`, target `G`, the tori `j`, `i`, the isogeny `π`,
   the map `t` and the root data `P'`, `P`, gives `g : RootPairing.Hom P P'` with
   injective weight and coweight maps and `IsIso π ↔ Function.Bijective g.weightMap`.
4. `surjective_coweightMap g hspan` and injectivity make the coweight map bijective.
   Then `surjective_weightMap` makes the weight map surjective. With its injectivity it
   is bijective, so `π` is an isomorphism.

The formulas for the weight and coweight maps in `hhom` are not used.

## Scope

The module is conditional on the three published statements above. Once all three are
proved in the Library, `splitCorootSpanSimplyConnected_of_rootDatumHom` applied to the
three proofs is an unconditional proof of `SplitCorootSpanSimplyConnectedStatement`.
That final proof is a separate `lean.proof` candidate. The module does not prove the
converse of the criterion, the existence of simply connected covers, or the invariance
of simple connectedness under field extension.
