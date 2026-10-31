# Valuative extension of rigidified Picard-zero classes, assuming four focused propositions

Authors: Worker 1031 and Worker 150 (`exists_algClosed_valuation_domination`).

This module reduces the target proposition
`Langlands.AbelianScheme.PicardZeroValuativeExtensionStatement` to four published
propositions that are not yet proved:

- `Langlands.AbelianScheme.AlgClosedFieldTranslationDifferenceLiftingStatement`
  (`h1`): over an algebraically closed field, a translation-invariant line bundle
  is `t_x^*L ⊗ N` for an ample `L` with tensor inverse `N` and some point `x`;
- `Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`
  (`h2`): a commutative smooth proper geometrically connected group scheme over an
  algebraically closed field has an ample line bundle;
- `Langlands.AbelianScheme.MumfordBundlePicardZeroStatement` (`h3`): the actual
  rigidified Mumford family `mumfordBundle` satisfies `IsPicardZeroFamily`;
- `Langlands.AbelianScheme.ValuationRingAmpleExtensionStatement` (`h4`): if the
  generic fibre of an abelian scheme over a valuation domain has an ample line
  bundle, then some line bundle on the total space has ample generic restriction.

The main result is the explicitly conditional theorem

`Langlands.AbelianScheme.picardZeroValuativeExtension_of_prerequisites
  (h1 : AlgClosedFieldTranslationDifferenceLiftingStatement)
  (h2 : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement)
  (h3 : MumfordBundlePicardZeroStatement)
  (h4 : ValuationRingAmpleExtensionStatement) :
  PicardZeroValuativeExtensionStatement`.

Its curried form is
`Langlands.AbelianScheme.picardZeroValuativeExtensionReduction :
  PicardZeroValuativeExtensionReductionStatement`, the implication stated in
module `Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionReductionStatement`.
None of the four hypotheses is proved or assumed anywhere else in the module.
Once all four are proved, applying this theorem to the four proofs proves the
target. The other inputs are proved Library results:
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`,
`Langlands.SchemeModule.RigidifiedModule.pullbackCoherence`,
`fieldLineBundleTriviality`, `picardZeroPullback`, `picardZeroFamilyBaseChange`,
`IsAmple.of_iso` and Mathlib's valuative criterion.
All declarations are in the namespace `Langlands.AbelianScheme`.

## Route and provenance

The target is a derived formulation about the Library's `PicardZeroClasses`,
not a verbatim source theorem; see the Markdown of
`PicardZeroValuativeExtensionStatement`. The proof follows the Mumford route
from the context of task `322a2874-8b1c-4e61-b7cc-e0d154742640`. Pass to an
algebraic closure `K'` of `K` and a valuation ring `R'` of `K'` dominating `R`.
Over `K'` the class is a translation difference `t_x^*L ⊗ N` (Mumford,
*Abelian varieties*, §8 Theorem 1; here the hypothesis `h1`). The ample line
bundle `L` comes from the generic restriction of a line bundle `M` over `R'`
(Raynaud, LNM 119, Théorème XI 1.4; here `h4`). The point `x` extends over `R'`
by properness. The required class over `R'` is the rigidified Mumford family of
the normalized `M`, pulled back along the extended point. It is Picard zero by `h3`.
Its pullback to `K'` agrees with that of the given class by a direct computation.

## Declarations

- `mumfordPointComparison preservation A L M evaluation K b a x hx Q premise`.
  This generalizes the Library theorem `fieldMumfordPointComparison` from abelian
  schemes over a field to an abelian scheme `A` over an arbitrary base `S`. The
  point `a : Over.mk b ⟶ A.X` is still defined on `Spec K` for a field `K`. If
  `t_x^*(i^*L) ⊗ i^*M` is isomorphic to `familyLineBundle A Q`, then the
  relative pullback of `mumfordBundle A preservation L M evaluation` along `a` is
  isomorphic to `Q` as a rigidified family. The proof is the Library's proof
  verbatim: `FieldMumfordPoint.carrierIso` (stated for arbitrary bases),
  `fieldLineBundleTriviality K` for `a^*M`, and
  `RigidifiedLineBundle.isoOfCarrierIso` with the relative projection as
  retraction.
- `isAmple_fibre_normalize`. Let `η : Spec K → S` with `K` a field. If the
  restriction of `M` along `pullback.fst A.X.hom η` is ample, so is the
  restriction of the underlying bundle of
  `LineBundle.normalize preservation A.X.hom (unitSection A) _ M B evaluation`,
  namely `M ⊗ π^*B`. The restriction of `π^*B` factors through `η^*B` on
  `Spec K`, which is trivial by `fieldLineBundleTriviality`. The explicit
  module isomorphism is fed to `IsAmple.of_iso`.
- `exists_section_extending A t ht x`. Let `A` be an abelian scheme over a
  valuation domain `R` with fraction field `K`, and `t` the morphism
  `Spec K ⟶ Spec R` (supplied with `ht : Spec.map (algebraMap R K) = t`). A section
  `x` of the base change of `A` along `t` gives a section `x'` of `A` with
  `t ≫ x'.left = x.left ≫ pullback.fst A.X.hom t`. The structure map is proper,
  so `UniversallyClosed.eq_valuativeCriterion` gives the existence part of the
  valuative criterion, which is applied to the valuative square with bottom map
  `𝟙 (Spec R)`.
- `exists_ample_generic h2 h4 R K A t ht`, for `K` algebraically closed:
  some line bundle on `A` has ample restriction to the generic fibre. Apply `h2` to
  the generic fibre (a `Grp` object with the smoothness, properness and geometric
  connectedness fields of the base-changed abelian scheme), then `h4`.
- `exists_picardZero_extension_of_isAlgClosed h1 h2 h3 h4 A R K b t ht p` is
  the main step. Here `K` is algebraically closed, `b : Spec R ⟶ S`, and `p` is a
  class in `PicardZeroClasses A (Over.mk (t ≫ b))`. It produces
  `q' : PicardZeroClasses A (Over.mk b)` whose `classesPullback` along
  `Over.homMk t rfl` is `p`. With `A' = (baseChange b).obj A`:
  1. `exists_ample_generic` gives `M` on `A'` with ample generic restriction.
     `LineBundle.exists_tensorObj_iso_structureSheaf` gives an inverse `B` of
     `e^*M` on `Spec R` and then an inverse `M₀` of the normalized bundle
     `Lr = LineBundle.normalize … M B evB`. `isAmple_fibre_normalize` shows that
     the generic restriction of `Lr` is ample.
  2. Choose a representative `Q` of `p` and transport it with
     `familyBaseChange b A (Over.mk t)` to `Q'`, a family for `A'`. It is Picard zero
     by `picardZeroFamilyBaseChange`. By
     `isTranslationInvariant_of_isGeometricallyPicardZero`, its line bundle
     `familyLineBundle A' Q'` is translation invariant on the generic fibre.
  3. `h1` gives a point `x` of the generic fibre with
     `t_x^*(i^*Lr) ⊗ i^*M₀ ≅ familyLineBundle A' Q'`, where `i` is the projection
     of the generic fibre and the evaluation is the pulled-back one
     (`pullbackTensorEvaluation`). `exists_section_extending` gives `x'` over `R`.
  4. `mumfordPointComparison`, applied to `a = g ≫ x'` with
     `g = Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 _)`, gives
     `relativePullback a Φ ≅ Q'` for the Mumford family
     `Φ = mumfordBundle A' preservation Lr M₀ ev₀`.
  5. `Ψ' = relativePullback x' Φ` is Picard zero by `h3` and `picardZeroPullback`.
     `Ψ₀ = familyBaseChangeInverse b A (Over.mk (𝟙 _)) Ψ'` is Picard zero by
     `picardZeroFamilyBaseChange` and the counit isomorphism. `Ψ` is its pullback
     along `Over.homMk (𝟙 _) : Over.mk b ⟶ (Over.map b).obj (Over.mk (𝟙 _))`, again
     Picard zero by `picardZeroPullback`. Then `q'` is the class of `Ψ`.
  6. For the equality of classes it suffices, by `Quotient.sound`, to give a
     rigidified isomorphism from the pullback of `Ψ` along `Over.homMk t rfl` to `Q`.
     After applying `familyBaseChange b A (Over.mk t)`, the isomorphism is the
     composite of the following: `relativePullbackComp` (with `pullbackCoherence`),
     the equation `h₁ ≫ k = (Over.map b).map g`, `familyBaseChangeNaturality`,
     `familyBaseChangeCounitIso`, `relativePullbackComp` again, and step 4. The
     unit isomorphism `familyBaseChangeUnitIso` of the equivalence brings it back.
- `exists_picardZero_extension_of_isAlgClosed'` is the same statement for an
  arbitrary `c` with `hc : Spec.map (algebraMap R K) ≫ b = c`. It is proved by
  `subst`.
- `exists_algClosed_valuation_domination R K` (Worker 150) produces
  `K' = AlgebraicClosure K`, which lies in universe `u`, and a valuation subring
  `R'` of `K'` dominating the image of `R`. It uses Mathlib's
  `IsLocalRing.exists_factor_valuationRing` applied to `R → K → K'`. It returns a
  local `φ : R →+* R'`, `ψ = algebraMap K K'` and the commuting square, which
  holds by `rfl`.
- `isPicardZeroClass_classesPullback A h r` shows that `classesPullback` preserves
  `IsPicardZeroClass`, via a representative and `picardZeroPullback`.
- `picardZeroValuativeExtension_of_prerequisites` proves the target. Given
  `S`, `A`, `R`, `K`, `i₂` and `q`, it takes the data of
  `exists_algClosed_valuation_domination`. It pulls `q` back to `Spec K'` along
  `Over.homMk (Spec.map ψ) rfl`, where it is still Picard zero, and applies
  `exists_picardZero_extension_of_isAlgClosed'` with `b = Spec.map φ ≫ i₂`.
  The required equation `hc` follows from the ring square `hφψ` by
  `Spec.map_comp`. The resulting `q'` and its equation are exactly the witness
  and the equation of the target. The two `Over.homMk` morphisms agree up to
  proof irrelevance.
- `picardZeroValuativeExtensionReduction` proves
  `PicardZeroValuativeExtensionReductionStatement` by
  `fun h1 h2 h3 h4 => picardZeroValuativeExtension_of_prerequisites h1 h2 h3 h4`.

## Technical notes

The module uses the transparency options
`backward.isDefEq.respectTransparency false` (also for types), as in the
Library's `FamilyBaseChange` and `FieldMumfordPointComparisonProof`. The
morphism `Spec K ⟶ Spec R` is passed as a variable `t` with an equation `ht`.
`familyLineBundle` is always applied with its parameter object `T` named
explicitly. Both choices avoid expensive unfolding of `Spec.map` and of the
base-change functor during unification.
