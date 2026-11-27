# Proof: quotients of quasi-projective schemes over a field by free finite group actions

The module `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientProof` proves the
proposition `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` as the
theorem

- `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient :
  FiniteFreeQuasiProjectiveQuotientStatement`,

with exactly the stated hypotheses. Given a field `K`, a scheme `X` over `Spec K` (structure
map `s`) with an immersion `j : X ⟶ ProjectiveSpace K N` over `Spec K`, and a free action
`A : FiniteFreeSchemeAction G X` of a finite group `G` by automorphisms over `Spec K`, it
produces an effective quotient `Q : A.EffectiveQuotient`, a structure map
`t : Q.scheme ⟶ Spec K` with `Q.map ≫ t = s`, and an immersion of `Q.scheme` into some
`ProjectiveSpace K M` over `Spec K`.

## Sources

The mathematics is that of the sources cited by the statement page: D. Mumford, *Abelian
Varieties* (1970), II.7, Theorem p.66 and Remark p.69, and SGA 1, Exposé V, 1.8, 2.3 and 2.6.
The construction of the quotient is the Library's (see below). Quasi-projectivity of the
quotient follows the proof of the theorem
`AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj`
of the Anthropic Lean formalisation of Fermat's Last Theorem (source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; Apache License 2.0, Copyright 2026 Anthropic,
PBC; licence files in `licenses/Anthropic-FLT/`). That theorem is not used itself: the proof
applies the three FLT theorems from which it is built, ported to the Library with the modules
they need. Each ported module's Markdown file lists its source file, its SHA-256 hash and every
change:

- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`
  (an invariant finite affine open cover with an invariant cocycle), with
  `…Thm_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`,
  `…Thm_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`,
  `…Thm_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`
  and `…Thm_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite`;
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`
  (descent of the cover and the cocycle to a quotient);
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`
  (an immersion into projective space from a cocycle on a finite affine cover), with
  `…Thm_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`,
  `…Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`
  and `…Thm_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`;

each with its proof module in `Langlands.AnthropicFLT.P2M.Sol` (`…` stands for
`Langlands.AnthropicFLT.Theorems.`).

The FLT theorem lists separatedness of the quotient over the base as a hypothesis. Here the
three component theorems construct the immersion directly, without that hypothesis. The
resulting immersion `j'` over `Spec K` implies that the descended structure morphism `t`, an
immersion followed by the proper `projectiveSpaceToSpec K M`, and hence the quotient scheme
`Q.scheme` are separated; the theorem does not state this consequence.

## Auxiliary results of the module

- `appTop_ext_of_openCover`: two global sections of a scheme that agree on every member of an
  open cover are equal. Global sections are morphisms to the affine line
  (`AffineSpace.toSpecMvPolyIntEquiv`), and morphisms agreeing on an open cover are equal.
- `FiniteFreeSchemeAction.autHom`: the action as a group homomorphism `Gᵐᵒᵖ →* Aut X`,
  `op g ↦ act g`. In `Aut X` the product `f * g` is "`g`, then `f`", while
  `FiniteFreeSchemeAction` writes `act g ≫ act h = act (g * h)`; the opposite group matches the
  two. `autHom_asIso_hom` records that `(A.autHom g).asIso.hom = (A.act g.unop).hom`, which
  holds by definition, so statements about all `γ : Gᵐᵒᵖ` and about all `g : G` convert into
  each other through `MulOpposite.op` and `MulOpposite.unop`.
- `FiniteFreeSchemeAction.nonempty_effectiveQuotient_of_invariant_affine`: for a finite group
  acting on a separated scheme, if every point has an affine open neighbourhood invariant under
  the action, then `A.EffectiveQuotient` is nonempty. The proof is that of the Library theorem
  `FiniteFreeSchemeAction.nonempty_effectiveQuotient` (module
  `Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineQuotient`), with its orbit step replaced: the
  relation `A.target, A.source : A.relationScheme ⟶ X` is finite
  (`source_isFinite_of_finite`, `target_isFinite_of_finite`), jointly monic (since
  `prod.lift A.target A.source` is a monomorphism for separated `X`, Library instance
  `relation_mono`) and an equivalence relation (`reflexive`, `symmetric`, `transitive`), and
  the points related to a point `x` are its translates, which lie in the invariant affine
  neighbourhood of `x`. The ported theorem
  `AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation` gives a
  finite, flat, locally finitely presented, surjective quotient map with the pullback and
  coequalizer properties; étaleness descends from the étale projection `A.target` along the
  pullback square (`MorphismProperty.of_isPullback_of_descendsAlong`).
- For an effective quotient `Q` (namespace `FiniteFreeSchemeAction.EffectiveQuotient`):
  - `exists_act_eq_of_map_eq`: two points with the same image under `Q.map` are in one orbit.
    A point of `X ×_{Q.scheme} X` over the pair (`Scheme.Pullback.exists_preimage_pullback`)
    corresponds, through `Q.isPullback`, to a point of the relation scheme `∐_g X`, which lies
    in one summand `g`.
  - `preimage_image_eq`: `Q.map` is an open map (flat and locally of finite presentation,
    Mathlib's `UniversallyOpen.of_flat`), and for an invariant open `U` the preimage of the open
    `Q.map '' U` is `U`, by `exists_act_eq_of_map_eq`.
  - `exists_isAffineOpen_preimage_eq`: an invariant affine open `U` of `X` is `Q.map ⁻¹ᵁ V` for
    an affine open `V` of `Q.scheme`, namely `V = Q.map '' U`. `V` is affine by the Library
    theorem `FiniteLocallyFreeQuotient.isAffine_of_finite_flat_surjective` applied to the
    finite, flat, locally finitely presented, surjective restriction `Q.map ∣_ V` with affine
    source.
  - `appLE_top_eq_of_comp_map_eq` and `isPairInvariant`: a section `f` over an invariant open
    `O`, invariant under every `act g`, has equal pullbacks along any two morphisms
    `a b : T ⟶ X` with `a ≫ Q.map = b ≫ Q.map` (over any open of `T` mapped into `O` by both).
    The Library theorem `EffectiveQuotient.eq_iff_locally_act` (module
    `Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineQuotientOver`) gives an open cover of `T`
    on whose members `a = b ≫ act g` for some `g`; there the two pullbacks agree by invariance
    of `f`, and `appTop_ext_of_openCover` concludes. The second form is the hypothesis
    `IsPairInvariant` of the Library module
    `Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent`, reduced to the
    first through the isomorphism of sections over an open `W` with global sections of `W`.
  - `app_injective`: `Q.map.app V` is injective for every open `V` of `Q.scheme`; this is the
    Library theorem `Langlands.Scheme.UnitCocycleDescent.app_injective` for the quasi-compact,
    flat, surjective `Q.map`.
  - `range_app_eq`: the image of `Q.map.app V` is the set of sections over `Q.map ⁻¹ᵁ V`
    invariant under every `act g`. Sections in the image are invariant because
    `act g ≫ Q.map = Q.map` (`EffectiveQuotient.invariant`); invariant sections descend by the
    Library theorem `Langlands.Scheme.UnitCocycleDescent.exists_app_eq_of_isPairInvariant`
    (descent of pair-invariant sections along a quasi-compact flat surjection, which is an
    effective epimorphism) and `isPairInvariant`.

## Proof of the theorem

1. `X` is quasi-compact and separated. `projectiveSpaceToSpec K N` is proper
   (`projectiveSpaceToSpec_isProper`), so `ProjectiveSpace K N` is quasi-compact, and it is
   locally Noetherian, being locally of finite type over the Noetherian `Spec K`
   (`LocallyOfFiniteType.isLocallyNoetherian`). The immersion `j` is the closed immersion
   `j.liftCoborder` followed by the open immersion of `j.coborderRange`, which is
   quasi-compact because projective space is locally Noetherian; so `j` is quasi-compact and
   `X` is quasi-compact. The morphism from `X` to the terminal scheme is `s` followed by the
   morphism from the affine `Spec K`, and `s = j ≫ projectiveSpaceToSpec K N` is separated (an
   immersion followed by a proper morphism), so `X` is separated.
2. Invariant affine cover. The ported FLT theorem
   `AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`,
   applied with `B = K`, the group `Gᵐᵒᵖ` acting through `A.autHom` and the immersion `j`
   (`ProjectiveSpace K N` is by definition the `Proj` of the polynomial ring with the grading
   used by FLT, and `projectiveSpaceToSpec K N` is by definition `ProjSpace.π K N`), gives a
   finite cover of `X` by invariant affine opens `U i` with an invariant cocycle `w`
   (`w i i = 1`, the cocycle identity, `X.basicOpen (w i j) = U i ⊓ U j`). Its hypothesis that
   the action is over `Spec K` is the statement's hypothesis on `A`.
3. The quotient. Every point lies in some `U i`, an invariant affine open, so
   `nonempty_effectiveQuotient_of_invariant_affine` gives `Q : A.EffectiveQuotient`.
4. The structure map. `s` is invariant, so it descends: `t = Q.desc s hA` with
   `Q.map ≫ t = s` (`EffectiveQuotient.map_desc`). Since `s = j ≫ projectiveSpaceToSpec K N` is
   locally of finite type and `Q.map` is finite, flat and surjective, `t` is locally of finite
   type by the Library theorem
   `FiniteFlatSourceDescent.locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective`
   (`Spec K` is Noetherian).
5. Descent of the cover. The ported FLT theorem
   `AlgebraicGeometry.Scheme.exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`
   applies to `q = Q.map`: `q` is invariant (`EffectiveQuotient.invariant`) and surjective,
   `app_injective` and `range_app_eq` give its hypotheses on sections (converted from `G` to
   `Gᵐᵒᵖ` as described above), and `exists_isAffineOpen_preimage_eq` gives the descent of
   invariant affine opens. It yields a finite affine open cover `V i` of `Q.scheme` with a
   cocycle `v` (`v i i = 1`, the cocycle identity, `Q.scheme.basicOpen (v i j) = V i ⊓ V j`).
6. The immersion. The ported FLT theorem
   `AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`,
   applied to `t`, which is locally of finite type, and to the cover `V` with the cocycle `v`,
   gives `M` and an immersion `j' : Q.scheme ⟶ ProjectiveSpace K M` with
   `j' ≫ projectiveSpaceToSpec K M = t`.

The theorem returns `Q`, `t`, `M`, `j'`, the immersion property of `j'`,
`j' ≫ projectiveSpaceToSpec K M = t` and `Q.map ≫ t = s`.
