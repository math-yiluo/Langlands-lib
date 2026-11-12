# Uniform finite-field charts of a quasi-separated algebraic space of finite type over ℤ

Author: Worker 3694. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`; the final
assembly (Worker 75) uses its main theorem to pass from points of the algebraic space `B` to
points of affine schemes.

Provenance: internal. The single-point version is the Library theorem
`FieldPointEtaleLift.exists_affine_etale_point`: every field-valued point of an algebraic
space lifts to an affine scheme with an étale map to it. That theorem is the field-valued
form of the lifting result that Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), cites as Knutson II.6.4 on printed page 15. This module makes the
construction uniform over all finite fields, using the same argument: the Galois group acts
on a fibre power of an étale chart by permuting the index. Uniformity comes from two
finiteness facts. The fibres of an étale affine chart of a quasi-separated space are
uniformly bounded (Library `EtaleChartFibreCount.exists_fibre_card_le`). The relevant fibre
powers are Noetherian, so finitely many affine opens cover them. The module introduces no
mathematical objects beyond the auxiliary constructions listed below.

Notation (from `FieldPoints.lean`): `S0 = Spec (ULift ℤ)`, the terminal scheme of the
universe. `toOver T` is a scheme `T` regarded over `S0`, and `toOverHom` is a morphism of
schemes regarded over `S0`. `h_Z = (schemeYoneda S).obj Z` is the functor of points of a
scheme `Z` over `S`. A point of an algebraic space `X` with values in a field `κ` is a
morphism `h_{Spec κ} → X`. `OverAction G Z` is an action of a group `G` on a scheme `Z` over
`S` by morphisms over `S` (Library `OverActionQuotientChart`). `resOver U` is an open `U` of
`Z` regarded over `S`, with inclusion `resOverι U`. `τ.orbitInf U = ⋂_g τ_g⁻¹(U)` is the
largest `τ`-stable open contained in `U`.

All names below are in the namespace
`Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.FiniteFieldCharts`.

## Main theorem

`exists_finiteField_charts`: let `B` be an algebraic space over `S0` that is quasi-separated
and of finite type over `ULift ℤ` (`FiniteTypeOverRing`: it has a surjective étale atlas from
a scheme that is locally of finite type and quasi-compact over `S0`). Then there are
`n : ℕ`, schemes `M i` (`i : Fin n`) and maps `t i : h_{M i} → B` such that

- every `M i` is affine and locally of finite type over `S0`;
- every `t i` is étale;
- for every finite field `κ` (in the universe of the schemes) and every `κ`-point `x` of `B`,
  there are an `i` and a morphism of schemes `m : Spec κ → M i` with `h(m) ≫ t i = x`.

Proof.

1. `ULift ℤ` is Noetherian. Let `a₀ : h_{U₀} → B` be the atlas. `U₀` is quasi-compact over
   the affine `S0`, so it is a compact space. Hence finitely many affine opens `O` cover it
   (`exists_finset_affineOpens_cover`). Each `O` is locally of finite type over `S0`, and
   `h_O → h_{U₀} → B` is étale.
2. For every `O` there is a fibre bound `D_O` (`exists_fibre_card_le`); let `D'` be the sum
   of the `D_O`.
3. For every `O` and every `k < D'`, `exists_orbit_charts`, applied to the chart `O` and the
   cyclic group of order `k + 1` (`CyclicGroup`), gives finitely many charts. All of them
   together are indexed by a finite type `I`, which is reindexed by `Fin (card I)`. A chart
   `M` over `S0` is turned into a plain scheme through `isoToOver`. Its structure morphism
   to `S0` is the unique one, so it is locally of finite type.
4. Let `x` be a `κ`-point of `B`. `exists_separable_point` gives a finite separable
   extension `L/κ` and an `L`-point `ℓ` of `U₀` with image the restriction of `x` to `L`,
   whose conjugates under `Aut(L/κ)` are pairwise distinct. `L` is a finite field. Its
   single point lands in some `O`, so `ℓ` factors through `O` (`exists_factor_resOver`).
   The conjugates `v_γ` of this factorization are pairwise distinct, and all of them map to
   the restriction of `x` to `L`.
5. `L/κ` is a Galois extension of finite fields, so `|Aut(L/κ)| = [L : κ] = r`
   (`IsGalois.card_aut_eq_finrank`). The fibre bound gives `r ≤ D_O ≤ D'`. `Aut(L/κ)` is
   cyclic, so there is an isomorphism `ψ : ℤ/r ≃ Aut(L/κ)` (`mulEquivOfCyclicCardEq`).
   Through `ψ`, `ℤ/r` acts on `Spec L` (`specAction`), and `v_g = v_{ψ g}` satisfies
   `σ_g ∘ v_e = v_{g e}`.
6. `exists_orbit_charts` for `(O, r - 1)` gives a chart `M_i` and a `σ`-invariant point
   `w : Spec L → M_i` with image the restriction of `x` to `L`. `ψ` is surjective, so `w`
   is invariant under all of `Aut(L/κ)`. Since `M_i` is affine, `w` descends to a point
   `m : Spec κ → M_i` (`exists_desc_of_aut_invariant`, `FieldPoints.lean`).
7. `h(m) ≫ t_i` and `x` agree after composing with `Spec L → Spec κ`. That map is flat,
   locally of finite presentation and surjective, so they agree (`eq_of_comp_eq`).

## Auxiliary results

- `exists_quotient_chart_lft`: a variant of the Library `OverAction.exists_quotient_chart`
  that also records that the quotient is locally of finite type over the base when `Z` is.
  Let a finite group act freely on `Z` over `S`, and let `U` be a stable open with
  `resOver U` affine. Let `t : h_Z → X` be étale and invariant. Then there are an affine
  quotient `M` of `U`, an invariant quotient map `q : U → M` and an étale `tM : h_M → X`
  with `h(q) ≫ tM = h(ι_U) ≫ t`. The proof uses the Library `FiniteActionChart` API. It
  restricts the action to `U` (`τ.restrict`), takes its quotient, and descends the
  invariant map `h(ι_U) ≫ t` to the quotient (`FiniteActionChart.exists_desc`). The
  quotient map is surjective, flat and locally of finite presentation, so `M` is locally of
  finite type over `S` because `U` is
  (`locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`). `tM` is étale
  by `isEtale_of_finiteEtale_comp`, since `X` has a representable diagonal.
- `eq_of_comp_eq`: two maps `h_M → X` to an algebraic space agree if they agree after
  composing with `h(q)` for an fppf cover `q : A → M` (flat, locally of finite
  presentation, surjective). `h(q)` is locally surjective as a map of sheaves
  (`isLocallySurjective_schemeYoneda_map`), hence an epimorphism, and `X` is a sheaf.
- `compactSpace_succ`, `compactSpace_fin`, `exists_compact_fibrePower`: let `S` be affine,
  `X` quasi-separated and `a : h_V → X` étale with `V` affine. Then every nonempty finite
  fibre power `V ×_X ⋯ ×_X V` (Library `ChartFibrePower`) is separated over `S`, has étale
  projections, and is compact. Separatedness and étale projections are
  `ChartFibrePower.fin_properties`. Compactness is by induction on the number of factors.
  The `(n + 1)`-fold power maps quasi-compactly to `V ×_S P_n`
  (`relative_diagonal_property_chart_pairing`, using quasi-separatedness of `X`), and
  `V ×_S P_n` is compact.
- `exists_finset_affineOpens_cover`: a compact scheme is covered by finitely many affine
  opens.
- `exists_invariant_point`: let `q : U → M` be invariant on a stable open `U`. An
  equivariant point `z : Λ → Z` from a one-point scheme `Λ` whose point lies in `U`
  factors through `U`, and its composite with `q` is invariant.
- `exists_uniform_charts` (**uniform quotient charts**): let a finite group `G` act freely
  on a compact separated scheme `Z` locally of finite type over `S`, and let `t : h_Z → X`
  be étale and invariant. There are finitely many affine `M_i`, locally of finite type over
  `S`, with étale maps `h_{M_i} → X`, such that every equivariant point `z : Λ → Z` from a
  nonempty one-point scheme `Λ` with a `G`-action `σ` gives a `σ`-invariant point
  `w : Λ → M_i` of some `M_i` with `h(w) ≫ tM_i = h(z) ≫ t`. Proof: cover `Z` by finitely
  many affine opens `W_j`. The opens `orbitInf W_j` are stable, and they are affine because
  `Z` is separated (`isAffineOpen_orbitInf`). Their quotient charts
  (`exists_quotient_chart_lft`) are the `M_j`. The point of `Λ` maps to a point of `Z`
  fixed by every `τ_g`, because `Λ` has only one point. That point lies in some `W_j`,
  hence in `orbitInf W_j`, and `exists_invariant_point` concludes.
- `exists_orbit_charts` (**charts for orbits of points**): let `S` be affine and locally
  Noetherian, `X` quasi-separated, `a : h_V → X` étale with `V` affine and locally of
  finite type over `S`, and `G` a finite group. There are finitely many affine `M_i`,
  locally of finite type over `S`, with étale maps `h_{M_i} → X`, with the following
  property. Let `Λ` be a nonempty one-point scheme over `S` with a `G`-action `σ`. Let
  `v : G → (Λ → V)` be injective, equivariant (`σ_g ∘ v_e = v_{g e}`), with all `v_e` having
  the same image in `X`. Then the image of `v_1` in `X` is the image of a `σ`-invariant
  point of some `M_i`. Proof:
  - Let `Y` be the `G`-indexed fibre power of `V` over `X` (`exists_compact_fibrePower`),
    with the action `ρ` of `G` permuting the index (`ChartFibrePower.act`).
  - `W = orbitInf (distinctLocus Y)` is the largest stable open on which the coordinates
    are pairwise distinct (Library `FieldPointEtaleLift.distinctLocus`). The action
    restricted to `W` (`FieldPointEtaleLift.resAction`) is free. If `g ≠ h` act equally on
    a point `b` of `W`, then the coordinates `1` of `ρ_g b` and `ρ_h b` are the coordinates
    `g` and `h` of `b`. They are equal, contradicting `ne_of_mem_distinctLocus`.
  - `W` is separated and locally of finite type over `S`. `Y` is Noetherian (locally
    Noetherian and compact), so `W` is compact. The map
    `t = h(W → Y → V) ≫ a` (first coordinate) is étale and invariant, since all coordinates
    have the same image in `X`. `exists_uniform_charts` gives the charts.
  - Given `v`, the point `y : Λ → Y` with coordinates `v` (`ChartFibrePower.lift`) is
    equivariant. Every translate `ρ_g ∘ y` has pairwise distinct coordinates because `v` is
    injective. So it lies in `distinctLocus Y` (`mem_distinctLocus_of_ne`), and `y` lies in
    `W`. Its factorization through `W` is equivariant, and `exists_uniform_charts` gives
    the invariant point.
- `exists_factor_resOver`: a morphism from a one-point scheme whose point lies in an open
  factors through the open.
- `specAction ψ`: for `ψ : G →* Aut(L/κ)`, the action of `G` on `Spec L` over `S0` by
  `Spec(ψ g)`. The order of multiplication matches because `Spec` is contravariant.
- `exists_fibre_card_le`: the Library `EtaleChartFibreCount.exists_fibre_card_le` (base
  ring `ULift ℤ`), restated for points `Spec L → V` over `S0` with `L` a field. It gives
  `D` such that any injective finite family of `L`-points of `V` with a common image in
  `X` has at most `D` members.
- `exists_separable_point`: let `a : h_U → X` be étale and surjective. For every `κ`-point
  `x` of `X`, there are a finite separable extension `L/κ` and an `L`-point `ℓ` of `U`
  whose image is the restriction of `x` to `L`, and whose conjugates `γ* ℓ`
  (`γ ∈ Aut(L/κ)`) are pairwise distinct. The fibre product `P = U ×_X Spec κ` is a
  nonempty scheme étale over `Spec κ`. The Library
  `FieldPointEtaleLift.exists_separable_point_mono` gives a monomorphism
  `Spec L → P` over `Spec κ`. Two conjugates with equal image in `U` also have equal image
  in `Spec κ`, so they are equal as maps to `P`. Cancelling the monomorphism and using
  injectivity of `Spec` on morphisms gives `γ = γ'`.
- `CyclicGroup r = ULift (Multiplicative (ZMod r))`, the cyclic group of order `r` in the
  universe of the schemes; it is cyclic, and `card_cyclicGroup` gives `|CyclicGroup r| = r`.
