# Temperedness of unitary untwists from the opposite exponent criterion

Lean module: `Langlands.Representation.LanglandsClassification.OppositeUntwistTemperedCriterion`.

This module proves the theorem

```
theorem Langlands.Aubert.General.RepresentedParabolic.oppositeUntwistTemperedCriterion :
    OppositeUntwistTemperedCriterionStatement.{u, v}
```

The target statement `OppositeUntwistTemperedCriterionStatement` is in the
Library module `OppositeJacquetUntwistSelectionReduction`. It is the
temperedness input of Renard VII.4.2 (iii), the step that uses Casselman's
criterion (Renard VII.2.1) on a standard Levi.

## The statement

Let `x` be an exponent of the opposite Jacquet modules of `π`, with label
`K ⊆ Δ(ν)`, and let `W` be a unitary untwist of `x`. Then `W.untwist` is an
irreducible admissible representation of `M_K`. Assume the following
hypothesis `hH`. Take any exponent `y` with label contained in `K` such that
`v_y - v_x` lies in `span_ℝ K`, where `v` is the full real parameter
`fullRealPart`. Then `-(v_y - v_x)` lies in the nonnegative cone of the simple
roots `Δ(ν)`. The conclusion is that `W.untwist` is tempered (in the sense of
`IsNormalizedExponentTempered`) on the standard Levi `M_K`.

## Helper lemmas in this module

- `neg_restrict_mem_nonnegCone_of_mem_hull`: this is the cone step. Let `r` be a
  parabolic root presentation, `S` a set of characters, and `K ⊆ S`. Take a
  cocharacter `ζ` that vanishes on `K` and is positive on `S \ K`. Let `u` be a
  nonnegative combination of `S` that lies in `span_ℝ K`. Assume that `-α` is a
  positive root of `r` for every `α ∈ S ∩ K`. Then `-r.f^*(u)` is in the
  nonnegative cone of `r`. The proof is by induction on the cone hull. It
  tracks `⟨w, ζ⟩ ≥ 0`, and also that `⟨w, ζ⟩ = 0` implies `-r.f^*(w)` lies in
  the cone. It uses `one_tmul_restrict_mem_nonnegCone` for single roots.
- `isNormalizedJacquetExponent_of_nested_injective`: this is the nested exponent
  lemma. Take parabolics `P ⊆ Q` of `G`, with Levi subgroups `M` and `L`
  respectively, where `P = (P ∩ L)N` and `M` is also a Levi of `P ∩ L`. Let `σ` be a subrepresentation of the
  normalized Jacquet module `r_Q π`. Then every normalized exponent of `r_{P∩L} σ`
  is a normalized exponent of `r_P π`. The proof uses transitivity of Jacquet
  modules (`leviParabolicTransitivity`) and exactness of the Levi Jacquet
  functor on injections (`leviJacquetFunctor_map_injective`). A generalized
  eigenvector maps to a nonzero generalized eigenvector
  (`isGeneralizedEigencharacter_of_map_ne_zero`).
- `isNormalizedJacquetExponent_congr_component`: exponents along equal
  split-component maps agree.

## Proof of `oppositeUntwistTemperedCriterion`

1. **Standard reduction on `M_K` with `-ν`.** By `OppositeUntwistLeviRoots`, the
   torus `leviTorus K` is a maximal split torus of `M_K`, and `-ν` is generic
   for it with simple roots `-K`. `genericMinimalParabolic` supplies the
   minimality hypothesis. The Library theorem `normalizedTemperedStandardReduction`
   then reduces temperedness of `W.untwist` to two facts. The first is
   admissibility, which is `W.untwist_admissible`. The second is the
   normalized-exponent cone condition for every standard parabolic test datum
   `(J', ζ', p', l', a')` of `M_K` for `-ν`, where `J' ⊆ -K`.
2. **Test datum.** Fix such a datum. `testLeviIso` identifies the test Levi `M'`
   with the standard Levi `M_J` of the label `J = -J'` (`negIndex`), and
   `J ⊆ K`. `IsSplitComponent.exists_iso_comp` gives an isomorphism `e` from
   the chosen split component `A_J` of `M_J` to `A'`. Together these give a
   factor `f' : A' → T` with `f' ≫ leviTorus K = a' ≫ l' ≫ p'`. This defines an
   explicit parabolic root presentation `pres0` of the test datum, with torus
   `leviTorus K`, cocharacter `-ν`, index `J'` and factor `f'`. By
   `parabolicRootPresentationIndependence`, the cone condition of an arbitrary
   presentation reduces to the cone condition of `pres0`.
3. **An ambient exponent `y`.** Let `χ` be a normalized exponent of `W.untwist`
   along `(p', l', r)` on `A'`. Let `ψ` be the positive unramified character of
   `x` and `ψa` its restriction to `A'`. Then `χs = χ · ψa` is an exponent of
   the twist of `W.untwist` by `ψ` (`isNormalizedJacquetExponent_unramifiedTwist_iff`).
   It is therefore an exponent of `W.source`, via the recovery isomorphism and
   `isNormalizedJacquetExponent_iff_of_equiv`. `W.source` embeds in the opposite
   Jacquet module of `π` at `K`. So by the nested exponent lemma, applied to the
   opposite parabolics of `K` and of `J` (`pointImage_opposite_p_le`,
   `pointImage_comp_leviHom_of_standardParabolic`), `χs` is an exponent of `π`
   along the opposite parabolic of `J` with Levi `M'`. Next the exponent is
   transported along `M' ≅ M_J` (`isNormalizedJacquetExponent_iso_comp_iff`)
   and along `e` (`isNormalizedJacquetExponent_comp_splitPointsEquiv_iff`).
   This gives an opposite standard exponent `y` with label `J ⊆ K` and
   character `χs ∘ e`.
4. **Real parts.** Write `Re` for `normalizedRealPart`. We show
   `Re χ = f'^*(v_y - v_x)`.
   - `normalizedRealPart_mul` gives `Re χs = Re χ + Re ψa`.
   - `ψa` factors through `T` along `f'`, because the torus factor of
     `rootPresentation K` is `leviTorus K`. So
     `normalizedRealPart_comp_points` and `fullRealPart_positiveUnramifiedCharacter`
     give `Re ψa = f'^*(v_x)`.
   - `χs = (χs ∘ e) ∘ e⁻¹`, and `f' = e⁻¹ ≫ g_J`. So
     `normalizedRealPart_comp_points`, `restrict_fullRealPart` and
     `rationalCharacterRestrictReal_comp_apply` give `Re χs = f'^*(v_y)`.
5. **Span condition.** We show `v_y - v_x ∈ span_ℝ K`.
   - The split component `A_K` of `M_K` maps centrally into `M_J`, through
     `g_K ≫ leviTorus J`. By `IsSplitComponent.exists_factor` it factors
     through `A_J`. Composing with `e` gives `h_K : A_K → A'` with
     `h_K ≫ f' = g_K` and `h_K ≫ a' ≫ l' ≫ p' = a_K`.
   - `normalizedJacquetExponent_restrict` shows that `χ ∘ h_K` is an exponent
     of `W.untwist` on `A_K`. `W.scalar` says that `A_K` acts on `W.untwist` by
     the unitary character `unitaryComponentCharacter x`, so
     `eq_of_isGeneralizedEigencharacter_of_scalar` gives
     `χ ∘ h_K = unitaryComponentCharacter x`.
   - This character has norm 1 (`norm_unitaryComponentCharacter`), so
     `Re(χ ∘ h_K) = 0`.
   - By step 4 and `normalizedRealPart_comp_points`,
     `g_K^*(v_y - v_x) = h_K^*(Re χ) = Re(χ ∘ h_K) = 0`.
   - `mem_selectedRootSpan_of_restrict_eq_zero` for `rootPresentation K` then
     gives `v_y - v_x ∈ span_ℝ K`.
6. **Cone.** Put `u = -(v_y - v_x)`. By the hypothesis `hH`, `u` is a
   nonnegative combination of `Δ(ν)`. By step 5 and `Submodule.neg_mem`, `u`
   lies in `span_ℝ K`. Choose a standard cocharacter `ζ_K` of `K`. It vanishes
   on `K` and is positive on `Δ(ν) \ K`. For `α ∈ K`, the root `-α` is simple,
   hence positive, for `pres0`, because the simple roots of `leviTorus K` for
   `-ν` are `-K`. The cone lemma, applied to this `u`, gives
   `-f'^*(u) = -f'^*(-(v_y - v_x)) = f'^*(v_y - v_x) ∈ pres0.nonnegCone`. By
   step 4 this is `Re χ`. So `Re χ ∈ pres0.nonnegCone`, which is the cone
   condition `SatisfiesNormalizedExponentConeCondition` for `pres0`. This
   matches Renard VII.4.2 (iii): the real part lies in the positive cone for the
   opposite parabolic, which is the standard positive system of `M_K` for `-ν`.

## Notes

- The main theorem has `set_option maxHeartbeats 4000000`, because it is one
  long elaboration with many instance arguments on Levi points.
- Helper module: `OppositeUntwistLeviRoots` (root negation and the standard
  data of `M_K` for `-ν`).
