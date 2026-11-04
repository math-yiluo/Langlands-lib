# Conditional surviving graded transitions

Module: `Langlands.Representation.Aubert.General.CorrectedGradedReduction`.

This module is a conditional (helper) result. It proves the generic target
`Langlands.Aubert.General.CorrectedFiltration.CorrectedGradedTransitionTarget`
(`CorrectedFiltrationStatements.lean`) from three explicit inputs, which are
hypotheses of the final theorem:

1. the support hypotheses `SurvivingSupportHypotheses P T cs I s i m` at every
   grade `i`, every lift `m` of `w⁻¹` and every `s` with `w` minimal in
   `W_J w W_I` (`hsupp`);
2. orbit Jacquet data `OrbitJacquetData P M U h hclosed hU T cs I E w m K hK`
   for every `E` in the support category, every grade, every lift and every `K`
   with `M K = m⁻¹ (M I) m` (`hD`);
3. for every `I`, the subgroup `U_I` of `P_I` is a limit of compact subgroups,
   `Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I))`
   (`hNc`);

together with the topological assumptions `[SigmaCompactSpace G]`,
`[T2Space G]`, compactness of every `P_J \ G` and closedness of every `P_J`
(`hPc`). Both structures are defined, with their fields, in the interface module
`CorrectedGradedInterface`. This module does not prove the task target
`RationalPointFamily.RationalCorrectedGradedTransitionStatement`: for actual
rational points, inputs 1–3 are not premises of that target, and nothing here
derives them. The support-category hypothesis of the target is not used by the
construction; it is only passed to `hD`.

Provenance: the declarations are internal. They implement the proof of the
graded transitions in Aubert's erratum (Trans. AMS 348 (1996), pp. 4688–4690,
with the Ban–Jantzen double-coset correction), as cited in the Markdown of
`CorrectedFiltrationStatements`: restrict to the new double coset, apply the
orbit Jacquet integral `Θ_s` (here an input), and pass to the Jacquet module.

## Conventions

As in the interface: `J = S \ s` is `Finset.univ \ s`; `w` is the `i`-th
length-ordered Weyl element `Support.rankOrderedElement cs.length i hi`; `m`
lifts `w⁻¹`; the new cell is `P_J m⁻¹ P_I`; the orbit piece is
`Geometric.orbitPiece (P J) (P I) m`; `K` satisfies
`hK : ∀ x, x ∈ M I ↔ m⁻¹ x m ∈ M K`. `R_s` denotes the restriction to the new
cell and `β_s` the graded map.

## Part A: restriction to the new cell

* `quotientMap_mem_image_iff`: for a left `Q`-invariant `X ⊆ G`, the coset of
  `g` lies in the image of `X` in `Q \ G` iff `g ∈ X`.
* `SurvivingSupportHypotheses.groupSupport_subset`: `G_{θ_i'} ⊆ G_{θ_{i+1}'}`
  (from `modifiedSupport_monotone` and `cellSupport_mono`).
* `SurvivingSupportHypotheses.left_lower`: `G_{θ_i'}` is also left
  `P_J`-invariant. If `p g ∉ G_{θ_i'}` for some `g ∈ G_{θ_i'}`, then `p g` lies
  in the difference `P_J m⁻¹ P_I`, hence so does `g = p⁻¹ (p g)`, a
  contradiction.
* `SurvivingSupportHypotheses.supportPair`: the images of `G_{θ_i'}` and
  `G_{θ_{i+1}'}` in `P_J \ G` form a `Geometric.OpenOrbitSupportPair` with new
  orbit `P_J m⁻¹ P_I` (right `P_I`-invariance from `cellSupport_mul_right`;
  openness from the openness of the quotient map; the difference from
  `sdiff_eq` and `quotientMap_mem_image_iff`).
* Generic orbit restriction, for any open orbit support pair `S` of
  `Q₁, Q₂, w` with `Q₁, Q₂` closed, `Q₁ \ G` compact and a smooth
  `Q₁`-representation `A`: `orbitRestriction S hQ₁ hQ₂ A` is the support
  quotient projection followed by `S.smoothQuotientIso`, from the sections
  supported in `S.upper` to the orbit piece. `orbitRestriction_eval`: it is
  `f ↦ (q ↦ f(w⁻¹ q))` (from `smoothQuotientIso_hom_projection_eval`).
  `orbitRestriction_eq_zero_iff`: it vanishes exactly on the sections supported
  in `S.lower` (from `restriction_zero_iff_lower`). `orbitRestriction_surjective`
  (from `RepSubfunctor.quotientProjection_surjective` and the inverse of the
  isomorphism). `orbitPiece_ext`: two elements of an orbit piece with the same
  values on `Q₂` are equal.
* `coefficientRepresentation_eq` (uses `hδ`): the coefficient representation of
  the term `E_J` equals the representation of `inducingObject P M U h E J`, by
  `inducingRepresentation_jacquet_eq`.
* `stepSubrepresentation … E I s i`: the functions of `E_J` supported in
  `G_{θ_i'}` (`inductionStep`) as a `P_I`-subrepresentation.
* `supportInclusion`: a function supported in `G_{θ_{i+1}'}`, transported along
  `coefficientRepresentation_eq` (the identity on values), as a section of
  `inducingObject` supported in the upper set of `supportPair`.
* `stepRestriction … hPc H E` (`R_s`): `orbitRestriction` composed with
  `supportInclusion`; a `P_I`-intertwining map from step `i + 1` of the
  functions to the orbit piece of `inducingObject P M U h E J`.
  `stepRestriction_eval`: `R_s f (q) = f(m⁻¹ q)`.
  `stepRestriction_eq_zero_iff`: `R_s f = 0` iff `f` is supported in
  `G_{θ_i'}` (via `left_lower`). `stepRestriction_surjective`: every element of
  the orbit piece is `R_s` of a function supported in `G_{θ_{i+1}'}` (via
  `left_upper`).

## Part C: descent to the Jacquet module

Generic linear algebra and Jacquet exactness:

* `imageDescent π S L hL`: a linear map `L` on a submodule `S` that vanishes on
  `S ∩ ker π` descends to `π(S)`; `imageDescent_apply`,
  `imageDescent_surjective`, and `imageDescent_eq_zero_iff` (the kernel is
  `π(S')` when `L` vanishes on `S' ≤ S` and each zero of `L` agrees with an
  element of `S'` modulo `ker π`).
* `relations_le_subgroupOf`, `relations_subrepresentation_le`: relations along
  `N` of a `G`-representation are relations of its restriction to `Q ⊇ N`, and
  relations of a `Q`-subrepresentation are relations of the ambient
  representation.
* `mem_relations_subrepresentation`: if `N ∩ Q` is a limit of compact subgroups
  and the ambient representation is smooth, a vector of a `Q`-subrepresentation
  that is an `N`-relation of the ambient representation is an `N`-relation of
  the subrepresentation. Proof: the inclusion is injective, so its map on
  coinvariants is injective (`Jacquet.Localization.map_injective_of_smooth`).

Generic graded map, for `Q = L ⋉ N` (`IsSemidirectDecomposition Q L N`), `N`
closed, `N ∩ Q` a limit of compact subgroups, a smooth `G`-representation `A`,
a `Q`-subrepresentation `Sr`, an intertwining map `R : Sr → X` and a linear map
`Θ : X → B` to a smooth `L`-representation, with `Θ (u x) = Θ x` for `u ∈ N`
(`hΘu`) and `δ_N^{-1/2}(l) Θ (l x) = l · Θ x` for `l ∈ L` (`hΘl`):

* `graded_wellDefined`: `Θ ∘ R` kills `Sr ∩ ker(A → A_N)`, by
  `mem_relations_subrepresentation` and `hΘu`.
* `gradedSource`: the image of `Sr` in the normalized Jacquet module
  `(jacquetFunctor hQ hN).obj A`, as a smooth `L`-subrepresentation
  (`jacquetImage`); `gradedSource_apply`: `l · [v] = δ_N^{-1/2}(l) [l v]`.
* `gradedMap` (`β`): the morphism of smooth `L`-representations
  `gradedSource → B`, `[v] ↦ Θ (R v)` (`imageDescent`, equivariant by `hΘl`).
  `gradedMap_mk`; `gradedMap_surjective` when `R` and `Θ` are surjective;
  `gradedMap_eq_zero_iff`: when `R` is surjective with kernel `S' ≤ Sr` and
  every zero of `Θ` is an `N`-relation of `X`, `β x = 0` iff `x ∈ [S']`. The
  last step lifts a relation of `X` along `R`
  (`Jacquet.Localization.relations_map_of_surjective`).

Specialization to a surviving grade, with `hNc` for `I`, `D : OrbitJacquetData
… I E w m K hK`, `hKs : K ⊆ J` and `hs` (minimality of `w`):

* `stepGradedMap … hPc H E hNc hU hK D hKs hs` (`β_s`): `gradedMap` for
  `Q = P_I`, `A = E_J`, `Sr` = step `i + 1` of the functions, `R = R_s`,
  `Θ = D.Θ s hKs hs`. Its source is exactly the target's
  `SmoothRep.subrepresentation (r_I(E_J)) (step … E I s (i + 1))` and its
  codomain `(conjugationFunctor m hK).obj (r_K E)`.
* `stepGradedMap_mk`: `β_s [f] = D.Θ s (R_s f)`.
* `stepGradedMap_surjective`: from `stepRestriction_surjective` and
  `D.surjective`.
* `stepGradedMap_eq_zero_iff`: `β_s x = 0` iff `x ∈ step … E I s i`, from
  `stepRestriction_eq_zero_iff` and `D.ker_le`.
* `stepGradedMap_transition` (uses `hP`): for surviving `s ⊆ t`,
  `β_t (r_I(φ^J_{J'}) x) = β_s x` on step `i + 1`. Write `x = [f]`; the
  transition maps `f` into step `i + 1` of `E_{J'}`
  (`transition_mem_inductionStep`); by `stepRestriction_eval` and the pointwise
  formula of the transition, `R_t(φ f)(q)` is the coinvariant transition of
  `R_s f (q)`; then `D.transition` gives the equality.

## Assembly

`correctedGradedTransitionTarget_of_orbitData` states

```
CorrectedGradedTransitionTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL
  IsAssociate T cs
```

under `hsupp`, `hNc` and `hD` above (and the topology). Proof: given `I`, `E`,
`hE`, `i`, `hi`, `m`, `hm`, `K`, `hK`, take
`β s hKs hs := stepGradedMap … (hsupp I s i hi m hm hs) E (hNc I) hU hK
(hD I E hE i hi m hm K hK) hKs hs`; its three laws are
`stepGradedMap_surjective`, `stepGradedMap_eq_zero_iff` and
`stepGradedMap_transition` (with `hsupp I t i hi m hm ht` for `t`).

## Status

The module compiles with no errors or warnings, and has no proof holes or new
axioms. It sets `maxHeartbeats 800000` and
`backward.isDefEq.respectTransparency.types false` for elaboration of the
subrepresentation and coinvariant types. Inputs 1–3 remain open: Part B (a
construction of `OrbitJacquetData`) is separate work, and the support
hypotheses for actual rational points need the Bruhat cell facts and the
openness of length-ordered cell unions, which are not in the Library.
