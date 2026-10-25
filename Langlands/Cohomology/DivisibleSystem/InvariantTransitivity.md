# Transitivity of the transition maps between Harris's `C_m^{•,H}`

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.InvariantTransition`
(`quotientProjection`, `surjective_quotientProjection`,
`quotientInvariantsComplexesChange`, `quotientInvariantsTransition`) and
`Langlands.Cohomology.DivisibleSystem.StandardMap` (`StandardMap`, its
fields `θ` and `θ_comp_η`, `powApp`, `totalMapF`, `totalMap`,
`map_ιTotal_totalMapF`, `totalMap_naturality`, `fiberAverage`,
`fiberAverage_app_mk`, `card_filter_eq_nat_card_ker`, `groupStandardMap`),
and through them on `…InvariantComparison` (`Rep.quotientInflation`),
`…Invariants` (`smoothQuotientInvariants`, `quotientInvariantsComplexes`),
`…TotalExact` (`standardRows`, `totalMap_hom_ext`), `…Total`
(`upFinEmbedding`, `upFinTotalFunctor`), `…StandardResolution`
(`standardPow`, `standardResolution`, `indResBot`, `indResBotCounit`) and
the base module `DivisibleSystem` (`hom_ext`, `comp_tower`, `id_tower`).
From Mathlib it uses `Rep.resFunctor`, `Representation.IndV`,
`HomologicalComplex₂.total` and `NatTrans.mapHomologicalComplex`.

Everything is in the namespace `Langlands.Cohomology`; the declarations of
the first section are in `Langlands.Cohomology.StandardMap`, those of the
last section in `Langlands.Cohomology.DivisibleSystem`.

Notation: composition `f ≫ g` is `f` followed by `g`. A `StandardMap Φ P ε
Q η` (StandardMap module) is a map of augmented endofunctors along
`Φ : A ⥤ B`: a natural transformation `θ : P ⋙ Φ ⟶ Φ ⋙ Q` with
`θ ≫ η Φ = Φ ε`. For a complex `L` of `A` in degrees `ℕ` and `N : ℕ`,
`totalMap N L` is the induced morphism from `Φ` of the total complex (rows
`q < N`) of the standard resolutions along `P` of `L` to the total complex of
the standard resolutions along `Q` of `Φ L`; `totalMapF N L n` is its degree
`n`, and `powApp r X : Φ (P^r X) ⟶ Q^r (Φ X)` are the iterated
comparisons. `Tot(c)` below abbreviates the morphism of total complexes
(rows `q < N`) of the standard resolutions induced by a morphism of
complexes `c` (`upFinTotalFunctor` applied to `standardResolution` applied
degreewise).

## Maps of augmented endofunctors

`A`, `B`, `C` are categories (abelian, with the functors additive and
preserving finite colimits, where total complexes occur).

- `comp t₁ t₂`: for `t₁ : StandardMap Φ₁ P ε Q η` and
  `t₂ : StandardMap Φ₂ Q η S σ`, the map along `Φ₁ ⋙ Φ₂` with comparison
  `Φ₂ (θ₁ X) ≫ θ₂ (Φ₁ X)`. The axiom follows from those of `t₁` and `t₂`.
- `powApp_comp t₁ t₂ t₃ hθ n X`: if the comparison of
  `t₃ : StandardMap (Φ₁ ⋙ Φ₂) P ε S σ` is `Φ₂ (θ₁ X) ≫ θ₂ (Φ₁ X)` (`hθ`), then
  `Φ₂ (t₁.powApp n X) ≫ t₂.powApp n (Φ₁ X) = t₃.powApp n X`. Induction on
  `n`, using the naturality of `θ₂`.
- `powApp_comp_map t t' e hθ n X`: for `t`, `t'` along `Φ` and `Φ'` and a
  natural transformation `e : Φ ⟶ Φ'` with
  `θ X ≫ Q (e X) = e (P X) ≫ θ' X` (`hθ`),
  `t.powApp n X ≫ Q^n (e X) = e (P^n X) ≫ t'.powApp n X`. Induction on `n`.
- `totalMapF_comp_map t t' e N L hθ n` and `totalMap_comp_map t t' e N L hθ`:
  under the same hypothesis, `t.totalMap N L ≫ Tot(e_L) =
  e ≫ t'.totalMap N L`, where `e_L` is `e` applied degreewise to `L` and the
  `e` on the right is applied degreewise to the total complex. Proof: on each
  summand `(q, r)` of the total complex this is `powApp_comp_map` in
  resolution degree `r + 1`, together with the naturality of `e`.
- `powApp_comp_map_id t e hθ n X` and `totalMapF_comp_map_id t e N L hθ n`:
  the variant for `t : StandardMap Φ P ε P ε` with `Φ : A ⥤ A` and
  `e : Φ ⟶ 𝟭 A` satisfying `θ X ≫ P (e X) = e (P X)`:
  `t.powApp n X ≫ P^n (e X) = e (P^n X)`, and in each degree
  `t.totalMapF N L n ≫ Tot(e_L) = e`. The same proofs.
- `totalMapF_comp t₁ t₂ N L n` and `totalMap_comp t₁ t₂ N L`: `totalMap`
  for `comp t₁ t₂` is `Φ₂` of `totalMap` for `t₁` followed by `totalMap`
  for `t₂` (at `Φ₁ L`). Proof: on each summand, `powApp_comp` for
  `t₃ = comp t₁ t₂`.
- `map_totalMap_comp_totalMap t₁ t₂ N L t₃ e hθ c₁ c₂ c₃ hc`: the abstract
  form of the transitivity below. Given `t₃` along a third functor `Φ₃`,
  `e : Φ₁ ⋙ Φ₂ ⟶ Φ₃` with
  `(Φ₂ (θ₁ X) ≫ θ₂ (Φ₁ X)) ≫ S (e X) = e (P X) ≫ θ₃ X` (`hθ`), and
  morphisms of complexes `c₁ : Φ₁ L ⟶ L'`, `c₂ : Φ₂ L' ⟶ L''`,
  `c₃ : Φ₃ L ⟶ L''` with `Φ₂ c₁ ≫ c₂ = e_L ≫ c₃` (`hc`):
  `Φ₂ (t₁.totalMap N L ≫ Tot(c₁)) ≫ t₂.totalMap N L' ≫ Tot(c₂) =
  e ≫ t₃.totalMap N L ≫ Tot(c₃)`. Proof: `totalMap_naturality` for `t₂`
  and `c₁`, `totalMap_comp`, `totalMap_comp_map` for `comp t₁ t₂`, `t₃`,
  `e`, and `hc` mapped by `Tot`.

## Composing normalized fiber sums

`k` is a commutative ring, `π₁ : Γ' →* Γ`, `π₂ : Γ'' →* Γ'` and
`π₃ : Γ'' →* Γ` are group homomorphisms with `π₁ (π₂ g) = π₃ g` for all `g`
(`h`). `Res_π` is restriction along `π` (`Rep.resFunctor π`), and
`fiberAverage k π` is the normalized fiber sum of the StandardMap module,
`⟦γ ⊗ v⟧ ↦ |ker π|⁻¹ ∑_{π γ' = γ} ⟦γ' ⊗ v⟧` from `Ind_1^Γ Res_1^Γ V` to
`Ind_1^{Γ'} Res_1^{Γ'} (Res_π V)` (`|ker π|⁻¹` is `Ring.inverse`).

- `resCompHom k π₁ π₂ π₃ h`: the natural transformation
  `Res_π₁ ⋙ Res_π₂ ⟶ Res_π₃` with identity linear maps (equivariant by `h`);
  `resCompHom_app_hom_apply` (`rfl`).
- `sum_filter_comp π₁ π₂ π₃ h f γ` (`Γ'`, `Γ''` finite): summing `f` over
  the fibers of `π₂` above the points of the fiber of `π₁` over `γ` is
  summing `f` over the fiber of `π₃` over `γ` (Mathlib's
  `Finset.sum_fiberwise_of_maps_to`).
- `nat_card_ker_comp π₁ π₂ π₃ h hπ₁ hπ₂`: for `π₁`, `π₂` surjective,
  `|ker π₃| = |ker π₁| · |ker π₂|`: count the fiber over `1` with
  `sum_filter_comp`, all fibers of a surjection having `|ker|` elements
  (`card_filter_eq_nat_card_ker`).
- `fiberAverage_comp k π₁ π₂ π₃ h hπ₁ hπ₂ V`: for `π₁`, `π₂` surjective, the
  fiber sum along `π₁` followed by the fiber sum along `π₂` (precisely
  `Res_π₂` of the first followed by the second at `Res_π₁ V`), followed by
  `Ind_1^{Γ''} Res_1^{Γ''}` of `resCompHom`, is `resCompHom` followed by the
  fiber sum along `π₃`. On `⟦γ ⊗ v⟧` both sides are
  `|ker π₁|⁻¹ |ker π₂|⁻¹ ∑_{π₃ γ'' = γ} ⟦γ'' ⊗ v⟧`, by `sum_filter_comp`,
  `nat_card_ker_comp` and `Ring.mul_inverse_rev`. This is the hypothesis
  `hθ` of `map_totalMap_comp_totalMap` for the three `groupStandardMap`s.
- `resIdHom k π h` (`π : Γ →* Γ` with `π g = g` for all `g`): the natural
  transformation `Res_π ⟶ 𝟭` with identity linear maps.
- `fiberAverage_comp_resIdHom k π h V` (`Γ` finite): for such `π`, the fiber
  sum along `π` followed by `Ind_1^Γ Res_1^Γ` of `resIdHom` is `resIdHom`:
  each fiber is a single point and `|ker π| = 1`. This is the hypothesis of
  `totalMapF_comp_map_id`.

## Transitivity of the transition morphisms

`R` is a commutative ring, `G` a topological group, `K` an `ℓ`-divisible
system of `ℕ`-graded complexes of smooth representations of `G`, and
`N : ℕ`. For normal subgroups `H' ≤ H` (hypothesis `hHH'`) of finite index,
`π : G ⧸ H' →* G ⧸ H` is `quotientProjection hHH'`, `K^H` is
`K.quotientInvariantsComplexes H hK`, `Inf_H` is inflation along
`G ⟶ G ⧸ H` (`Rep.quotientInflation R H`), and `τ_{H,H'}` is
`quotientInvariantsTransition K hHH' N hK hK' hk`: the InvariantTransition
module's transition morphism from `Inf_H C^{•,H}` to `Inf_{H'} C^{•,H'}`.
The hypotheses `hK`, `hK'`, `hK''` say that the projections of `K` stay
epimorphisms on `H`-, `H'`- and `H''`-invariants, and `hk`, `hk'`, `hk''`
that the orders of the kernels of the projections are units in `R`. Each
transition needs its target quotient to be a `Fintype` and its source
quotient to have decidable equality.

- `quotientInvariantsTransition_tower_app_f K N hHH' hK hK' hk m n`: at
  level `m` and degree `n`, `τ_{H,H'}` is
  `Inf_{H'}` of degree `n` of `t.totalMap N L ≫ Tot(c)`, where
  `t = groupStandardMap R π …`, `L` is level `m` of `K^H` and `c` is level
  `m` of `quotientInvariantsComplexesChange K hHH' hK hK'` (the inclusion
  `Res_π K^H ⟶ K^{H'}`). The first factor of `τ_{H,H'}`, `mapCompHom` of
  `quotientInflationResIso`, has identity components; the proof is
  `Category.id_comp`.
- `isUnit_card_ker_quotientProjection_trans hHH' hH'H'' hk hk'`: for
  normal subgroups `H'' ≤ H' ≤ H` with `G ⧸ H'` and `G ⧸ H''` finite, if
  the orders of the kernels of `G ⧸ H' → G ⧸ H` and `G ⧸ H'' → G ⧸ H'` are
  units in `R`, so is the order of the kernel of `G ⧸ H'' → G ⧸ H`, their
  product by `nat_card_ker_comp`.
- `quotientInvariantsTransition_comp K N hHH' hH'H'' hK hK' hK'' hk hk'`:
  for normal subgroups `H'' ≤ H' ≤ H` of finite index,
  `τ_{H,H'} ≫ τ_{H',H''} = τ_{H,H''}` (the last along
  `hH'H''.trans hHH'`, with the unit hypothesis given by the previous
  lemma). Proof, at each level `m` and degree `n`: rewrite the
  three transitions with the previous lemma. Apply
  `map_totalMap_comp_totalMap` with `Φ₁ = Res_{π₁}`, `Φ₂ = Res_{π₂}`,
  `Φ₃ = Res_{π₃}` for the projections `π₁ : G ⧸ H' → G ⧸ H`,
  `π₂ : G ⧸ H'' → G ⧸ H'`, `π₃ : G ⧸ H'' → G ⧸ H` and
  `e = resCompHom R π₁ π₂ π₃`. Here `π₁ (π₂ g) = π₃ g` holds by computation
  on representatives, `hθ` is `fiberAverage_comp`, and `hc` (the inclusions
  of invariants compose) holds elementwise. Then apply `Inf_{H''}`.
  `Inf_{H'}` of a morphism is definitionally `Inf_{H''}` of its restriction
  along `π₂`. `Inf_{H''}` of `e` is the identity elementwise.
- `quotientInvariantsTransition_refl K N hK hk`: `τ_{H,H}` (along
  `le_refl H`) is the identity. Proof, at each level and degree: the
  inclusion of `H`-invariants into themselves is `resIdHom` applied
  degreewise (elementwise), so by `totalMapF_comp_map_id` and
  `fiberAverage_comp_resIdHom` the composite is `Inf_H` of `resIdHom`, the
  identity elementwise.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.306, after forming
`C_m^{•,H}`: "When we replace H by a subgroup H' which is normal in S(e), we
obtain a natural isomorphism C_m^{•,H} = [C_m^{•,H'}]^H. Taking the direct
limit as H shrinks to the identity, we obtain ... (2.6)". Worker 61 read
this passage in the scanned original.

Harris does not state transitivity. A direct limit over the subgroups `H`
needs transition maps that compose and are the identity for `H' = H`; this
module proves both for the transition morphisms of the InvariantTransition
module. The statements and proofs, and all the generic lemmas, are ours. As
explained in the InvariantTransition module, we do not formalize Harris's
isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H`, and our transition morphisms are not
identified with it.

The hypotheses are those of the transition morphisms: finite index of the
subgroups, invertibility of the orders of the kernels of the projections in
`R` (`hk`, `hk'`; in Harris's setting these are powers of `p ≠ ℓ` for `H`
pro-`p` and `H'`, `H''` open, which is not formalized) and surjectivity on
invariants (`hK`, `hK'`, `hK''`).

## Scope

The module proves the two laws, composition and identity, that make the
transition morphisms of the InvariantTransition module a direct system over
the normal subgroups of finite index ordered by reverse inclusion, under the
hypotheses above. It does not package them as a functor, form
the direct limit over `H`, compare it with the underlying complexes, or
construct Harris's (2.6), (2.7) or Lemma 2.8.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
