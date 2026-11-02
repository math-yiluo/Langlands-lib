# Exactness of the actual dynamic normalized induction

Authors: Worker 717, with Worker 117 (who proposed the statement), for task
174d2de0-fa21-41b4-b091-f1b86481790b. This module declares one proposition
definition and no theorem. It does not prove the proposition. The proof is
a separate unit, in the planned module
`Langlands.Representation.Aubert.General.DynamicInductionExactness`.

## The declaration

`Langlands.Aubert.General.DynamicInductionExactnessStatement.{u, uV}` has
exactly the binders of the published target
`Langlands.Aubert.General.DynamicInductionFiniteLengthStatement.{u, uV}`
(`Aubert/General/PrerequisiteStatements`), in the same order:

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]` and
  Mathlib's `[IsNonarchimedeanLocalField F]`;
- a group scheme `G : GroupScheme (Spec (CommRingCat.of F))` with
  `hG : IsConnectedReductive G`;
- a cocharacter `χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G`;
- the pinned topology `letI := rationalPointTopology F G.X` on
  `G(F) = RationalPoint F G.X`, after `haveI := hG.isAffineHom` and
  `haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom`;
- `[LocallyCompactSpace (RationalPoint F G.X)]`,
  `[NonarchimedeanGroup (RationalPoint F G.X)]` and
  `hU : IsClosed U(χ)(F)`, where
  `U(χ)(F) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))`.

Only the conclusion differs. Here it is

`SmoothRep.PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, uV} (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU)`.

The functor is the same as in the target: Worker 23's normalized induction
`SmoothRep.{0, u, uV} ℂ Z(χ)(F) ⥤ SmoothRep.{0, u, max u uV} ℂ G(F)` of
the published decomposition `P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)`
(`Aubert/General/Parabolic`, `Aubert/General/DynamicParabolic`). It inflates
along the projection `P(χ)(F) →* Z(χ)(F)`, twists by the half modulus
`HaarModulus.closedHalfCharacter` of conjugation on `U(χ)(F)`, and takes
smooth induction from `P(χ)(F)` to `G(F)`. There is no hypothesis on
closedness of `P(χ)(F)`, continuity of the projection or Hausdorffness of
`G(F)`.

## The predicate

`SmoothRep.PreservesFiniteLengthShortExact Φ`
(`Smooth/FiniteLengthGrothendieckFunctor`) says: for morphisms
`f : A ⟶ B` and `g : B ⟶ C` between three objects of finite group-algebra
length, if `IsShortExact (hom f) (hom g)` holds, then
`IsShortExact (hom (Φ.map f)) (hom (Φ.map g))` holds. `SmoothRep.IsShortExact`
(`Smooth/FiniteLengthGrothendieck`) means that the first underlying
intertwiner is injective, the second is surjective, and the range of the
first equals the kernel of the second. The statement asserts nothing about
finite length of the images.

## Why the assertion holds (not proved here)

The published theorem
`Langlands.Aubert.General.normalizedInductionFunctor_preservesShortExact`
(`Aubert/General/AlternatingOperator`) gives this conclusion for any
semidirect decomposition `P = M ⋉ U` of a group with `[LocallyCompactSpace]`
and `[NonarchimedeanGroup]`, given four more inputs:

1. `[T2Space G]`;
2. `CompactOpenCofinal G`;
3. `IsClosed (P : Set G)`;
4. `Continuous h.projection`.

For the pinned topology on `G(F)` each input is a true fact.

1. Hausdorffness is the published `rationalPoint_t2Space`
   (`PointTopology/RationalPointGroups`), because `F` is Hausdorff.
2. Cofinality is the published `compactOpenCofinal_of_nonarchimedean`, from
   the two instance binders.
3. `P(χ)` is represented by a closed subgroup scheme (CGP, Lemmas 2.1.4
   and 2.1.5;
   published `isClosedSubgroup_parabolicHom` in
   `GroupScheme/Dynamic/Representability`). For Hausdorff `F`, a closed
   immersion gives a closed embedding of point sets (Conrad,
   Proposition 2.1).
4. The projection is the published `Dynamic.limitHom`
   (`dynamic_projection_eq_limitHom`). It is the map on points of the
   morphism of schemes `P(χ) → Z(χ)` (CGP, Lemma 2.1.5 and Proposition
   2.1.8(2)), and the point topology is functorial, so it is continuous.

The expected proof derives 3 and 4 for this topology and then applies the
published theorem. At this module's Library base, the point-set forms of
inputs 3 and 4 for the pinned topology are not yet proved.

## Provenance

This statement is derived, not quoted. Renard (2026), Chapter VI, §VI.1.1,
Théorème (printed page 135, PDF page 141), says that unnormalized
induction `Ind_P^G : M(M) → M(G)` is exact, for every parabolic
`P = MN`. The Proposition of §VI.1.2 (printed page 136, PDF page 142) says
that the normalized functor `i_P^G(τ) = Ind_P^G(τ ⊗ δ_P^{-1/2})` is exact.
This module specializes that exactness in three ways.

- The group is the actual `G(F)` with the pinned topology. The parabolic is
  the actual `P(χ)(F)` with its published decomposition. For connected
  reductive `G` the subgroups `P(χ)` are exactly the parabolic subgroups
  (CGP, Proposition 2.2.9), as the Markdown of
  `Aubert/General/PrerequisiteStatements` explains.
- The functor is Worker 23's normalization, not Renard's. When `U(χ)(F)` is
  unimodular the two differ by a twist by a character of the Levi subgroup
  (see `Aubert/General/PrerequisiteStatements.md`, item "Normalization").
  Exactness does not depend on the twist: the published theorem above proves
  it for Worker 23's normalization directly.
- Exactness is asserted only for sequences of finite-length objects. That
  is what `SmoothRep.FiniteLengthInductionStatement` consumes. Renard proves
  exactness on all sequences, and the published
  `normalizedInductionFunctor_map_isShortExact` has that stronger form
  under inputs 1-4.

## Relation to the task

The exact target of task 174d2de0 is
`DynamicInductionFiniteLengthStatement`, which is `PreservesFiniteLength`
of the same functor with the same binders. This proposition is one input of
the planned reduction through `SmoothRep.FiniteLengthInductionStatement`
(module `Smooth/FiniteLengthInductionStatement`): exactness on finite-length
sequences together with finite length of the induced representations of
irreducible representations of `Z(χ)(F)` gives the target. The second input
is the Lemma of Renard VI.6.2 (printed page 178), and this module does not
state it.

## Sources

- D. Renard, *Représentations des groupes réductifs p-adiques* (2026
  version), `renard-2026-representations-groupes-reductifs-padiques` (PDF
  page = printed page + 6): VI.1.1 Théorème, printed p. 135; VI.1.2
  Proposition, printed p. 136; VI.6.2, printed p. 178.
- B. Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
  `conrad-2011-weil-grothendieck-adelic-points`: Proposition 2.1, printed
  pp. 2–3.
- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, 2nd ed.
  (2015), `conrad-gabber-prasad-2015-pseudo-reductive`: Lemma 2.1.4,
  printed p. 49; Lemma 2.1.5, printed pp. 50–51; Proposition 2.1.8(2),
  printed p. 53; Proposition 2.2.9, printed p. 67.
