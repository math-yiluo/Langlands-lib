# Naturality of the canonical dual base-change comparison

`Langlands.AbelianScheme.dualAbelianBaseChangeNaturality` proves the exact
published `Langlands.AbelianScheme.DualAbelianBaseChangeNaturalityStatement`.
Take abelian schemes `A`, `B` over `S`, a morphism `b : S' → S` and a homomorphism
`f : A → B`. Write `d(f)` for `dualAbelianSchemeMapFromEvaluation` and `E_A`, `E_B`
for `dualAbelianBaseChangeIso`, each with the displayed endpoint data. The theorem
proves the equality of actual abelian-scheme homomorphisms over `S'`

`(baseChange b).map (d(f)) ≫ E_A.hom = E_B.hom ≫ d((baseChange b).map f)`.

The theorem keeps every premise of the statement. These are the seven tensor,
coherence and Picard-zero-pullback propositions, Picard-zero base-change
universality, the `DualAbelianBaseChangeStatement` input, and all endpoint choices
for the four duals. No hypothesis is added. The geometry, inverse line bundle and
evaluation choices affect only the group structures. They do not change the
underlying scheme maps compared below, so the proof uses no relation between
different choices. The equality holds for arbitrary bases, with no flatness,
noetherian or reducedness condition.

## Implemented proof

The module proves five auxiliary lemmas and one auxiliary isomorphism before the
final theorem.

1. **Base-changed homomorphisms over the original.** `hom_baseChange_map_fst` states
   that the total-space map of `(baseChange b).map f` lies over `f` via the first
   pullback projections. It is proved by unfolding the base change to
   `Over.pullback` and simplifying.

2. **Family comparison.** `familyBaseChangeSpaceMap_baseChangeHom` shows that two
   maps of relative spaces agree for every `T : Over S'`. One composite is the
   ground base-change space map `familyBaseChangeSpaceMap` followed by the
   homomorphism space map `homFamilySpaceMap f`. The other is
   `homFamilySpaceMap ((baseChange b).map f)` followed by the base-change space map.
   Both projections are checked by `pullback.hom_ext` and the previous lemma.
   `familyBaseChangeHomPullbackIso` builds a natural isomorphism from this equation.
   It compares pulling back a rigidified family along `f` and then changing the base
   with the reverse order. Its construction is
   `RigidifiedLineBundle.pullbackComp`, then `pullbackCongr` along the space
   equation, then the inverse of the second `pullbackComp`. The section
   conditions come from `relativeSection_familyBaseChangeSpaceMap` and
   `relativeSection_homFamilySpaceMap`.

3. **Classes.** `rigidifiedClassesBaseChange_homClassesPullback` evaluates this
   natural isomorphism on representatives. On rigidified classes it gives
   `rigidifiedClassesBaseChange b A T (homClassesPullback f _ q) =
   homClassesPullback ((baseChange b).map f) T (rigidifiedClassesBaseChange b B T q)`.
   `baseChangeParameterMap_naturality` records naturality of the projection
   `baseChangeParameterMap` from a base-changed parameter scheme. It is checked
   by `ext` and `simp`.

4. **Scheme square.** `dualSchemeMap_dualSchemeBaseChangeIso` proves the square for
   underlying scheme maps in `Over S'`. Its maps are the base change of
   `dualSchemeMap homPicardZeroPullback f hA hB`, the two
   `dualSchemeBaseChangeIso` comparisons, and the dual map of `(baseChange b).map f`.
   Both composites are morphisms into the dual of the pulled-back `A`.
   `dualPointClass_injective` reduces their equality to equality of their point
   classes. `Subtype.ext` reduces this further to the underlying rigidified classes.
   The proof rewrites the left side with `dualPointClass_dualSchemeBaseChangeIso`,
   `baseChangeParameterMap_naturality` and `dualPointClass_dualSchemeMap`. It
   rewrites the right side with `dualPointClass_dualSchemeMap`. The two sides then
   differ only by the order of base change and homomorphism pullback.
   `dualPointClass_dualSchemeBaseChangeIso` for `B` at the identity point identifies
   the class of `E_B`. Item 3 then closes the goal.

5. **Final theorem.** Abelian-scheme homomorphisms are determined by their
   underlying scheme maps, via `Additive.toMul.injective` and `Grp.hom_ext`. The
   underlying map of `d(f)` is definitionally `dualSchemeMap homPicardZeroPullback f
   hA hB`. `dualAbelianBaseChangeIso_hom` identifies the underlying maps of `E_A` and
   `E_B` with the prescribed `dualSchemeBaseChangeIso` comparisons. The goal then
   becomes the scheme square of item 4.

The module sets `backward.isDefEq.respectTransparency false`, as
`DualBaseChangeClasses` does. Its axioms are only `propext`, `Classical.choice` and
`Quot.sound`.

## Internal provenance

This is a derived compatibility proof between Library constructions. It makes no
separate claim to an external source theorem. It follows the route the statement's
Markdown anticipates. It compares the family obtained by pulling back along `f` and
then changing base with the reverse order. It then uses uniqueness of
classification and lifts the scheme equality to abelian-scheme homomorphisms.
`FamilyBaseChange` and `HomFamilyPullback` provide the family space maps and
pullback functors. `PoincareBaseChange` provides `baseChangeParameterMap`.
`DualBaseChangeClasses` provides `rigidifiedClassesBaseChange` and the classification
of the canonical comparison. `DualSchemeMapTensor` and `DualSchemeTensor` provide
classification of the dual map and injectivity of point classification.
`DualAbelianBaseChange` provides the exact underlying map of the chosen
abelian-scheme comparison. The published `FiniteWeilBaseChange` module contains a
related space-map lemma for a general base-changed homomorphism. This module does
not import it and proves the needed special case directly.
