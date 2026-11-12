# Finitely many affine étale charts carrying all field-valued points

Authors: Worker 80 (proof draft), Worker 197 (check, revision and submission).

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.UniformFieldPointChartsStatement.{u}`. The
entry theorem is `uniformFieldPointCharts`.

The target: for a commutative ring `C : Type u` and a separated (`IsSeparated X`),
quasi-compact (`IsQuasiCompact X`) algebraic space `X` over `Spec C`, there are `n`, schemes
`U i` over `Spec C` (`i : Fin n`) with `(U i).left` affine, and morphisms `f i : U i → X` with
`hom (f i)` étale, such that for every field `k : Type u` with a `C`-algebra structure and every
`x : RingPoints C X k` some `f i` maps a `k`-point of `U i` to `x`.

## Route

The Lean proof follows the construction in the first paragraph of the proof of Stacks Project
Lemma 68.8.3 (Tag 0BBN), using the Library's tuple modules
(`EtaleEquivalenceRelationTuple*`). Choose an affine étale surjective atlas `a : U → X` and let
`E` be the étale equivalence relation `R = U ×_X U ⇉ U`. Since `X` is separated, `R` is affine.
For each `n`, the symmetric group acts freely on the affine scheme of distinct related
`(n + 1)`-tuples, with affine quotient `V_n`, and the first coordinate descends to an étale map
`V_n → X`. A `k`-point of `X` lifts to a `k`-point of some `V_n` with `n` below the uniform
bound `E.tupleLengthBound` by a Galois-descent argument adapted from the Library proof
`FieldPointEtaleLift.exists_affine_etale_point`. The charts are `V_0, …, V_{N-1}` with
`N = E.tupleLengthBound`. As in the Library tuple modules, index `n` means `n + 1`
coordinates, so the Lean `V_n` is the Stacks quotient `V_{n+1} = W_{n+1}/S_{n+1}`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.UniformFieldPointCharts`. Throughout,
`h` is a pullback square exhibiting `(t, s) : R ⇉ U` as the kernel pair of
`a : h_U → X.presheaf` in presheaves on schemes over `Spec C`, with `t.left`, `s.left` étale.
The file sets `backward.isDefEq.respectTransparency false`: the fields of the relation
`EtaleEquivalenceRelation.ofKernelPair` are `U.left`, `R.left`, `t.left`, `s.left` only after
unfolding that definition.

- `rel h ht hs`: the relation `EtaleEquivalenceRelation.ofKernelPair t s a h ht hs`.
- `tupleProjection_hom`, `tupleDistinctProjection_hom`: all coordinates of a related tuple have
  the same structure map to `Spec C` (they are related through `R`, which lies over `Spec C`).
- Assuming `R.left` affine: instances `IsAffine (rel h ht hs).R` and `IsSeparated (rel h ht hs).s`.
- `tupleOver n`: the distinct-tuple scheme over `Spec C` through its first coordinate;
  `projOver n i`: the `i`-th coordinate as a morphism over `Spec C`.
- `map_projOver`: all coordinates have the same image in `X`. A relation arrow `r` between
  coordinates `i` and `j` (`tupleProjection_related`) lifts to a morphism `r'` over `Spec C`
  with `projOver i = r' ≫ t` and `projOver j = r' ≫ s`; then use `h.w`.
- `act_hom`, `actOver_projOver`: the permutation action `tuplePermutationAction` is an action over
  `Spec C`, and after acting by `g` the `i`-th coordinate is the `g i`-th coordinate.
- Assuming also `U.left` affine: `quot n` and `quotMap n`, the affine quotient
  `FiniteActionChart.quotientOver` of `tupleSymmetricQuotient n` and its quotient map, and
  `actOver_quotMap` (invariance, `AffineQuotient.invariant`).
- `exists_chart`: an étale `tM : h_{V_n} → X.presheaf` with `h(quotMap n) ≫ tM = h(projOver n 0) ≫ a`.
  Descent is `FiniteActionChart.exists_desc` (invariance from `actOver_projOver` and
  `map_projOver`); étaleness is `isEtale_of_finiteEtale_comp`, since `quotMap n` is finite, étale
  and surjective and `h(projOver n 0) ≫ a` is étale.
- `exists_point`: given such `tM n` for all `n`, and `a` étale and surjective, every `k`-point
  `x` is `RingPoints.map (homMk (tM n))` of a `k`-point of `V_n` for some
  `n < (rel h ht hs).tupleLengthBound`.

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`:

- `uniformFieldPointCharts : UniformFieldPointChartsStatement.{u}`.

## Proof of `exists_point`

1. As in `FieldPointEtaleLift.exists_affine_etale_point`: the pullback `P` of `a` along
   `x̂ : h_{Spec k} → X` is a nonempty scheme étale over `Spec k`; it has a point
   `w₀ : Spec L → P` that is a monomorphism, `L/k` finite separable
   (`exists_separable_point_mono`); `exists_faithful_galois` gives a finite Galois `K/k` with the
   set `Emb = (L →ₐ[k] K)` finite and nonempty.
2. For `e ∈ Emb`, `vE e : Spec K → U` is `Spec e` followed by `w₀` and the projection to `U`. All
   `vE e` have image `x̂ ∘ (Spec K → Spec k)` in `X` (`hvE`), and `vE` is injective (`hvinj`, by
   the monomorphism `w₀`). The Galois action satisfies `σ ∘ vE e = vE (σ ∘ e)` (`hγv`).
3. Enumerate `Emb` by `e₀ : Fin (m + 1) ≃ Emb` (`Finite.equivFinOfCardEq`). The coordinates
   `c i = (vE (e₀ i)).left` are pairwise related (`EtaleEquivalenceRelation.exists_lift_of_isPullback`)
   and injective, so `tupleDistinctFieldLift` gives a `K`-point `z` of the distinct-tuple scheme
   with these coordinates. By `tupleDistinct_fieldPoint_length_le`, `m < tupleLengthBound`.
4. For `σ ∈ Gal(K/k)`, let `π σ = e₀⁻¹ ∘ (σ ∘ -) ∘ e₀`. Comparing coordinates
   (`tupleDistinct_hom_ext`), `σ ∘ z = (action of π σ) ∘ z`. Hence `w = quotMap m ∘ z` is Galois
   invariant (`actOver_quotMap`), and `exists_desc_of_galois_invariant` descends it to a
   `k`-point `u` of `V_m`.
5. `h(w) ≫ tM m = h(z) ≫ h(projOver m 0) ≫ a = h(vE (e₀ 0)) ≫ a = h(Spec K → Spec k) ≫ x̂`.
   By `FieldPointEtaleLift.changeRing_injective` and Yoneda naturality, the image of `u` in
   `X(k)` is `x`. This last step is copied from `exists_affine_etale_point`.

## Proof of `uniformFieldPointCharts`

1. From `IsQuasiCompact X` take an étale surjective atlas `W → X` with `W.left` compact. A finite
   subcover of the affine cover of `W.left` (`affineCover.finiteSubcover`) gives
   `J : ∐ Uᵢ → W.left`, étale (`IsZariskiLocalAtSource.sigmaDesc`) and surjective, with affine
   source. The composite `a : U → X` is étale (`isEtale_map`, `IsEtale.comp`) and surjective
   (`SpaceProductPoints.isSurjective_map`, `SpaceProductPoints.IsSurjective.comp`). This is the
   construction of the Library theorem `SpaceProductPoints.exists_affine_atlas`, which assumes
   finite type; here quasi-compactness suffices.
2. `exists_kernelPair` gives the kernel pair `(t, s) : R ⇉ U` with étale projections, and `R` is
   affine because the diagonal of `X` is a closed immersion
   (`isAffine_of_isPullback_of_closedDiagonal`).
3. `exists_chart` gives `tM n` for every `n`. Take `N = (rel …).tupleLengthBound`, the charts
   `quot (i : ℕ)` with the morphisms `homMk (tM i)` for `i : Fin N`, and apply `exists_point`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Stacks Project, Lemma 68.8.3 (Tag 0BBN), proof, first paragraph, and Lemma 68.8.4 (Tag 07S9),
  proof: registered source `stacks-stratification-2026-11-02`. The Lean proof uses the
  quotients `V_p = W_p/S_p` and the étaleness of `V_p → X` described there; the lifting of
  `k`-points for arbitrary fields `k` is the author's Galois-descent argument.
