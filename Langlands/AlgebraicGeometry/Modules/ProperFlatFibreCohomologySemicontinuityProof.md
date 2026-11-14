# Semicontinuity of fibre cohomology for proper flat morphisms (proof)

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityProof`
proves

```lean
theorem properFlatFibreCohomologySemicontinuity :
    ProperFlatFibreCohomologySemicontinuityStatement.{u}
```

Let `g : Y ⟶ T` be proper and flat, with `T` locally noetherian, and let `F` be an invertible
module on `Y`. For a point `t`, the fibre is `Y_t = Y ×_T Spec κ(t)` (Mathlib's chosen pullback
along `T.fromSpecResidueField t`), and `Hᵖ(Y_t, F_t)` is the Library's `relativeCohomology` over
`κ(t)`. The theorem proves the four clauses of the statement:

1. `Hᵖ(Y_t, F_t)` is finite-dimensional;
2. locally on `T`, these spaces vanish in all degrees above one bound;
3. `{t | dim Hᵖ(Y_t, F_t) < r}` is open;
4. `t ↦ χ(F_t)` is locally constant.

The route is Mumford's (D. Mumford, *Abelian Varieties*, Chapter II, §5, Theorem p.46 and
Corollary p.50; literature id `mumford-abelian-varieties-chapter-ii-scan`). Over an affine open
`V` of `T`, one bounded complex `K` of finite projective `Γ(T, V)`-modules computes the cohomology
of every fibre over `V` after base change to the residue field. The four clauses then follow from
commutative algebra for `K`, in the helper module `Langlands.Cohomology.FibreDimension` (its
Markdown describes those lemmas). Auxiliary declarations are in the namespace
`Langlands.AlgebraicGeometry.Modules.FibreSemicontinuity`.

## Step 1: a perfect model over a noetherian affine base

`exists_perfectModel`: let `R` be a noetherian ring, `f : X ⟶ Spec R` proper and flat, and `M`
invertible on `X`. There is a strictly perfect complex `K` (Library `ModuleComplex.IsStrictlyPerfect`:
bounded, with finite projective terms) such that for every ring map `φ : R ⟶ S`, the degreewise
scalar extension `K ⊗_R S` (Library `ModuleComplex.baseChange`) is isomorphic in the derived
category to the derived `S`-module sections of the pullback of `M` to `X ×_{Spec R} Spec S`.

The proof follows the Library proof `noetherianUniversalPerfectSections`, which assumes `f` smooth
but uses only flatness. Take the finite ordered affine cover
`Scheme.OrderedAffineCover.ofCompactSpace X`. The Library theorem
`noetherianCechPerfectRepresentative` (for proper flat `f` and `M` locally isomorphic to the unit)
gives `K` with `K ⊗_R S` isomorphic to the Čech complex of the pulled-back module for every `S`.
The Library theorem `CechResolution.nonempty_cechCochainComplex_iso` identifies that Čech complex
with the derived sections. Its hypotheses are separatedness (from properness) and
quasi-coherence of the pullback (`IsLocallyFreeRankOne.isQuasicoherent_pullback`). The local
trivialisations of `M` come from `Scheme.Modules.IsInvertible`.

## Step 2: the fibre model

`SpecMap_evaluation_fromSpec`: for an affine open `V ∋ t`, the point `Spec κ(t) ⟶ T` is
`Spec(ev_t) ≫ hV.fromSpec`, where `ev_t = T.evaluation V t : Γ(T, V) → κ(t)` is evaluation at `t`
(germ followed by residue, `IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`).

`exists_fibreModel`: let `V` be an affine open with `Γ(T, V)` noetherian. Apply Step 1 to the
restriction `affineRestrict g hV = (g ∣_ V) ≫ hV.isoSpec.hom : g⁻¹(V) ⟶ Spec Γ(T, V)` (Library;
proper by the Library instance, flat as a restriction of `g` followed by an isomorphism) and to the
restriction of `F` (invertible by `IsInvertible.pullback`). This
gives `K` such that for every `t ∈ V`:

- `Hⁿ(Y_t, F_t) ≅ Hⁿ(K ⊗ κ(t))` for `n ≥ 0`, with `K ⊗ κ(t)` formed along `ev_t`;
- `Hⁿ(K ⊗ κ(t)) = 0` for `n < 0`.

For the first item, pasting the chosen pullback square of `affineRestrict g hV` along `Spec(ev_t)`
with the Library square `isPullback_affineRestrict` gives a pullback square of `g` along
`T.fromSpecResidueField t`. The Library theorem `nonempty_relativeCohomology_iso_chosenPullback`
compares its cohomology with that of the chosen fibre `Y_t`. `Scheme.Modules.pullbackComp`
matches the modules. `DerivedPlus.homologyIsoOfIsoDerivedComplex` turns the derived isomorphism
of Step 1 into isomorphisms of homology in degrees `n ≥ 0`. The second item is
`DerivedPlus.isZero_homology_of_neg`, transported along the same derived isomorphism.

`exists_localFibreModel`: every point of a locally noetherian `T` has an affine neighbourhood `V`
(`exists_isAffineOpen_mem_and_subset`) with `Γ(T, V)` noetherian
(`IsLocallyNoetherian.component_noetherian`), hence such a model.

`kerPrime_evaluation`: for a point `q` of `Spec Γ(T, V)` with image `t = hV.fromSpec q`, the
kernel of `ev_t` is `q`. The image of the closed point of `Spec κ(t)` under `Spec(ev_t)` is
`ker(ev_t)`, and `hV.fromSpec` maps it to `t`. Since `hV.fromSpec` is injective, `ker(ev_t) = q`.

## Step 3: the four clauses

Fix `t₀`, a neighbourhood `V` and a model `K` as above, with `K` vanishing outside `[a, b]`.

1. **Finiteness** (`finite_homology_baseChange`). `Hⁿ(K ⊗ κ(t))` is a quotient of a subspace of
   the finite-dimensional `κ(t) ⊗ Kⁿ`.
2. **Bounded vanishing.** For `p ≥ b + 1` the term `Kᵖ` is zero, so `Hᵖ(K ⊗ κ(t)) = 0`
   (`isZero_homology_baseChange_of_isZero`) for every `t ∈ V`.
3. **Upper semicontinuity.** For `t ∈ V`, `dim Hᵖ(Y_t, F_t) = homologyDim K p (ker ev_t)` (dimension
   formula of the helper module). By `kerPrime_evaluation`,
   `{t | dim Hᵖ(Y_t, F_t) < r} ∩ V = hV.fromSpec '' {q | homologyDim K p q < r}`. The latter set
   is open in `Spec Γ(T, V)` (`isOpen_setOf_homologyDim_lt`), and `hV.fromSpec` is an open
   embedding. So every point of `{t | dim Hᵖ(Y_t, F_t) < r}` has an open neighbourhood inside it.
4. **Euler characteristic.** Let `m = max(-a, 0)` and `N = m + b⁺ + 1`, where `b⁺ = max(b, 0)`.
   `negOnePow_mul_finsum_eq` shows
   `(-1)ᵐ χ(F_t) = E(ker ev_t)`, with `E(q) = ∑_{i < N} (-1)ⁱ fibreDim K^{i-m} q`. The finite sum
   `χ(F_t) = ∑ᶠ_{p ≥ 0} (-1)ᵖ dim Hᵖ(Y_t, F_t)` runs over `p ≤ b⁺`. The negative degrees in the
   window `[-m, b⁺]` contribute nothing, because `K ⊗ κ(t)` has no negative homology. The
   helper's Euler identity `sum_negOnePow_finrank_homology_baseChange` then applies, because
   `K` vanishes in degrees `-m - 1` and `b⁺ + 1`. The function `E` is locally constant on
   `Spec Γ(T, V)` (`isLocallyConstant_sum_fibreDim`, using that the terms of `K` are finite
   projective). Write `t₀ = hV.fromSpec q₀`. Then `hV.fromSpec '' {q | E q = E q₀}` is an open
   neighbourhood of `t₀`, and `χ` is constant on it.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
