# Central-torus exactness of algebraic fundamental groups

Author: Worker 149 (Task 6713).

## Statement proved

`Langlands.GroupScheme.AlgebraicFundamentalGroup.centralTorusFundamentalExactness` proves
`Langlands.GroupScheme.AlgebraicFundamentalGroup.CentralTorusFundamentalExactnessStatement`
(module `Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusStatement`) at universe `u`.

Let `k` be a field and `E` a separable closure of `k`. Let `Z` be a `k`-torus, `H` and `G`
connected reductive `k`-groups, `i : Z → H` a closed central subgroup and `p : H → G` the
fppf quotient by the full subgroup functor of `Z`. Then, for the selected maps
`fundamentalGroupMap`, the map `π₁(Z) → π₁(H)` is injective, `π₁(H) → π₁(G)` is
surjective, and the range of the first is the kernel of the second. So
`0 → π₁(Z) → π₁(H) → π₁(G) → 0` is exact. The statement's Markdown gives the precise
hypotheses and their provenance.

## Source

Kaletha–Prasad (2023), §11.5 (printed p. 429, PDF p. 460) and the proof of
Lemma 11.5.1 (printed p. 430, PDF p. 461). They state the sequence for z-extensions.
The Library statement is the derived generalization to an arbitrary closed central
torus described in its Markdown. The Lean proof follows the same lattice argument:
exactness of cocharacters of maximal tori, plus the identification of coroot lattices
through the simply connected covers.

## Proof

Write `aZ`, `aH` and `aG` for the chosen presentations `chosenChoice` of `Z`, `H` and
`G`, and `B` for base change to `E`.

1. **Factorizing choices over `k`.** By `Choice.exists_torusFactorization`
   (`Langlands.GroupScheme.AlgebraicFundamentalGroupMapConstruction`) there are
   presentations `b` of `H` and `c` of `G` and torus homomorphisms
   `e : T_Z → T_b` and `e' : T_b → T_c`. They satisfy
   `aZ.inclusion ≫ i = e ≫ b.inclusion` and `b.inclusion ≫ p = e' ≫ c.inclusion`.
   Base change gives geometric torus factorizations `B.map e` and `B.map e'` in the
   sense of `Choice.IsTorusFactorization`.
2. **Maps on representatives.** The published `algebraicFundamentalGroupMap`
   gives `aZ.mapTo E b i [ν] = b.comparison E b [ν ≫ B.map e]`, and similarly for
   `b.mapTo E c p`. The published `algebraicFundamentalGroupComparison` gives
   `b.comparison E b = id` and `c.comparison E c = id`. So these maps are induced by
   the cocharacter maps `α = ν ↦ ν ≫ B.map e` and `β = ν ↦ ν ≫ B.map e'`.
3. **Geometric inputs** (module
   `Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusGeometry`).
   `aZ.inclusion` is an isomorphism because `Z` is a torus
   (`IsMaximalTorus.isIso_of_torus`).
   - `CentralTorus.torusLatticeMap_exact`: `α` is injective with range `ker β`.
   - `CentralTorus.torusLatticeMap_surjective`: `β` is surjective.
   - `CentralTorus.exists_coverIso` and `CentralTorus.exists_scTorusIso`: there is an
     isomorphism `φ : b.scTorus ≅ c.scTorus` with
     `φ.hom ≫ c.scToTorus = b.scToTorus ≫ e'`.

   Let `σ = ν ↦ ν ≫ B.map φ.hom`, a bijection `X_*(T_b,sc) → X_*(T_c,sc)`. Then
   `c.corootMap E ∘ σ = β ∘ b.corootMap E`.
4. **Exactness at `b`, `c`.** `quotient_exact_of_lattice_exact` (module
   `Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusLattice`) applies with
   these inputs:
   - `ρB = b.corootMap E` and `ρC = c.corootMap E`, whose ranges are by definition the
     coroot images;
   - `ρC` is injective (`Choice.corootMap_injective`);
   - the bijection `σ` and its compatibility from step 3;
   - the representative formulas from step 2.

   It shows that `aZ.mapTo E b i` is injective, `b.mapTo E c p` is surjective, and the
   range of the first is the kernel of the second.
5. **Transport to the chosen presentations.** The naturality clause of
   `algebraicFundamentalGroupMap` gives two identities:
   - `aH.comparison E b ∘ aZ.mapTo E aH i = aZ.mapTo E b i ∘ aZ.comparison E aZ`, and
     `aZ.comparison E aZ = id`;
   - `aG.comparison E c ∘ aH.mapTo E aG p = b.mapTo E c p ∘ aH.comparison E b`.

   `aH.comparison E b` and `aG.comparison E c` are bijective by
   `algebraicFundamentalGroupComparison`. `exact_of_comparison` then transfers
   exactness from step 4 to `fundamentalGroupMap k E Z.toGrp H _ hH i = aZ.mapTo E aH i`
   and `fundamentalGroupMap k E H G hH hG p = aH.mapTo E aG p`.

The development check (`lean_check` with Lake build) reports only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
