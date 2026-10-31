# Proof: the Mumford classifier on a universal rigidified parameter

Authors: Worker 1028 (Lean construction, proof and first Markdown, shared as
the draft of task `12a52ae7-6c49-446c-be25-f54347329f59`) and Worker 1138
(independent check of the draft and revision of this Markdown).

`Langlands.AbelianScheme.universalMumfordClassifier` proves exactly the
published proposition
`Langlands.AbelianScheme.UniversalMumfordClassifierStatement.{u}`. Let `S` be
an arbitrary scheme in universe `u`, `A : AbelianScheme S`, `P : Over S`, and
`L : RigidifiedFamily A P`, and let

```text
hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L.
```

Write `A_P = (baseChange P.hom).obj A` (total space `A ×_S P`) and
`e = (RigidifiedLineBundle.trivialParameter … L hL).left : S ⟶ P.left`. The
theorem gives a scheme morphism `Ψ : A_P.X.left ⟶ P.left` with

1. `Ψ ≫ P.hom = A_P.X.hom ≫ P.hom`;
2. `unitSection A_P ≫ Ψ = P.hom ≫ e`;
3. for every `T : Over S` and `p : T ⟶ P`, the actual relative rigidified
   pullback of `L` along `p` satisfies `IsPicardZeroFamily A` if and only if,
   for every algebraically closed `K : Type u`, every
   `t : Spec K ⟶ T.left` and every `y : Spec K ⟶ A_P.X.left` with
   `y ≫ A_P.X.hom = t ≫ p.left`, one has `y ≫ Ψ = t ≫ T.hom ≫ e`.

The theorem keeps the arbitrary universe and every quantifier of the statement
and adds no hypothesis.

## Provenance

The morphism constructed here is the classifying morphism of the rigidified
Mumford family of `A_P`. Edixhoven, van der Geer and Moonen, *Abelian
Varieties* (preliminary draft, source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Chapter VI §3,
printed p.95 (PDF p.99), define, for one line bundle `L` on an abelian variety
over a field, the morphism `ϕ_L` classifying the Mumford bundle `Λ(L)`, given
on points by `x ↦ [t_x^*L ⊗ L⁻¹]`; the universal rigidified pair is the one of
(6.2), printed p.88 (PDF p.92). The classifier here is the family version
`(x, q) ↦ ϕ_{L_q}(x)` over the parameter of a universal pair on an abelian
scheme over an arbitrary base. This family version, its Lean construction and
the proof below are internal to the project and use only published Library
declarations; no further literature statement is used.

## Construction (namespace `Langlands.AbelianScheme.UniversalMumfordClassifier`)

- `unitSection_comp_symmetry_inv` and `baseChangeBundle`: the universal family,
  pulled back along `(relativeSpaceSymmetry A.X.hom P).inv`, is a rigidified
  line bundle `L'` on `A_P` along its unit section. Its underlying line bundle
  is definitionally `familyLineBundle A L`.
- `baseMumford`: the published rigidified Mumford family `mumfordBundle` of
  `A_P` (over the base `P.left`) for `L'`, an ordinary line bundle `M` and an
  evaluation `L' ⊗ M ≅ 𝒪`.
- `mumfordFamily`: the same family transported to a family of `A` over
  `(Over.map P.hom).obj A_P.X` with `familyBaseChangeInverse`.
- `classifierOver`: `RigidifiedLineBundle.classifyFamily` of `mumfordFamily`
  with respect to the universal pair, a morphism `(Over.map P.hom).obj A_P.X ⟶ P`
  over `S`; `Ψ` is its underlying morphism (`classifier_comp_hom` gives 1).

## Proof

- `nonempty_relativePullback_iso_trivial_iff`: for `a : T ⟶ A_P.X` over
  `P.left`, the pullback of `mumfordFamily` along `(Over.map P.hom).map a` is
  isomorphic to the trivial family exactly when the pullback of `baseMumford`
  along `a` is. The functor `familyBaseChange` is the functor of the published
  equivalence `familyBaseChangeEquivalence` (so it reflects isomorphisms via
  `preimageIso`); `familyBaseChangeNaturality`, `familyBaseChangeCounitIso` and
  `RigidifiedLineBundle.pullbackTrivialIso` compute the two images.
- `comp_classifier_eq_iff`: `a.left ≫ Ψ = T.hom ≫ P.hom ≫ e` exactly when
  that pullback of `baseMumford` is trivial. This uses
  `classifyFamily_pullback`, `classifyFamily_trivial`,
  `classifyFamily_eq_of_iso` and `isoOfClassifyFamilyEq`.
- `unitSection_comp_classifier` (gives 2): apply the previous lemma to the unit
  point `1 : Over.mk (𝟙 P.left) ⟶ A_P.X` (`unitPoint_left`) and the published
  `mumfordZeroParameterIso`.
- `nonempty_mumford_iso_trivial_iff`: for any abelian scheme `B` over any
  scheme, a field-valued point `a : Over.mk b ⟶ B.X` and the section `x` of
  `B_K` over it, the pullback of the Mumford family along `a` is trivial
  exactly when `t_x^*(i^*L) ≅ i^*L` as modules, where `i` is the projection
  `B_K ⟶ B`. Both directions use the published
  `FieldMumfordPoint.carrierIso` (stated for an arbitrary base), the triviality
  of line bundles on a field spectrum (`fieldLineBundleTriviality`) and the
  pulled-back evaluation (`pullbackTensorEvaluation`). For the forward
  direction the auxiliary module is the pullback of `t_x^*(i^*L) ⊗ i^*M`
  along the fibre-product symmetry, and uniqueness of tensor inverses
  (`tensorInverseComparisonIso`) cancels `M`; for the converse,
  `trivialIsoOfCarrierIso` restores the rigidification.
- `nonempty_translate_pullback_iso` and `nonempty_translate_pullback_iso_iff`:
  translation invariance at one section is transported along a homomorphism,
  respectively an isomorphism, of group schemes, using the published
  `GroupScheme.translation_hom`. `nonempty_pullback_iso_self_iff` transports
  it along an isomorphism of modules.
- `comp_classifier_eq_iff_translate`: for a field-valued point
  `s : Spec K ⟶ P.left`, a point `y` of `A_P` over `s` and the section `x` of
  `A_{s ≫ P.hom}` with the same image in `A`, `y ≫ Ψ = s ≫ P.hom ≫ e` holds
  exactly when the translate by `x` of the bundle of the actual pullback
  `(relativePullback (Over.homMk s rfl)).obj L` is isomorphic to it. The
  iterated base change `(A_P)_s` is compared with `A_{s ≫ P.hom}` by
  `GroupScheme.baseChangeCompIso` and the published
  `geometricPointPullbackLineBundleIso`; the two sections correspond by
  `baseChangeCompIso_inv_fst`.
- `isTranslationInvariant_iff_classifier`: translation invariance of that
  bundle over `K` is equivalent to `Ψ` sending every `K`-point of `A_P` over
  `s` to the trivial parameter. `isTranslationInvariant_iff_classifier_of_eq`
  allows a structure morphism `c` equal to `s ≫ P.hom` (by `subst`), and
  `isTranslationInvariant_iff_classifier'` applies it to an arbitrary slice
  morphism `q : Over.mk c ⟶ P`.
- `classifier_forward`: if the pullback along `p` is Picard zero, so is its
  pullback along every geometric point `t` of `T` (`picardZeroPullback`,
  `relativePullbackComp`, `isPicardZeroFamily_iff_of_iso`); over an
  algebraically closed field this gives translation invariance
  (`isTranslationInvariant_of_isGeometricallyPicardZero`), hence the equation
  for `Ψ` by `isTranslationInvariant_iff_classifier'`.
- `classifier_backward`: conversely, for each geometric point `t` of `T`, the
  equations for `Ψ` and `isTranslationInvariant_iff_classifier'` give
  translation invariance of the bundle of the pullback of `L` along
  `Over.homMk t rfl ≫ p`, hence (by `relativePullbackComp`) of the pullback
  along `t` of the pullback along `p`. As in the published geometric-point
  detection, `GroupScheme.isTranslationInvariant_pullback` along
  `GroupScheme.baseChangeCompIso` and `geometricPointPullbackLineBundleIso`
  turn this into translation invariance of the geometric fibre at `t`, which
  is the definition of `IsPicardZeroFamily`.
- `universalMumfordClassifier` chooses `M` and the evaluation from the
  published `locallyFreeRankOneIffTensorInvertible`, the same choice as in
  `picardZeroClasses_isUnit`, and assembles 1–3.

## Scope

The base scheme `S`, the abelian scheme and the universal pair are arbitrary;
no Noetherian, separatedness, field or finiteness hypothesis is used, and
universality is used only through the published classification API. The
module asserts nothing about uniqueness of `Ψ`, openness, closedness or
connected components, and it imports none of the field Picard-zero
component-constancy, component-comparison or open-locus statements.
