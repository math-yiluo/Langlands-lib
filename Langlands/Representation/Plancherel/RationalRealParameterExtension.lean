import Langlands.Representation.Plancherel.SplitTorusPositiveCharacter
import Langlands.Representation.Plancherel.RationalRestrictionSurjectivity

/-! # Real parameters realized by actual valuation-image characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M : GroupScheme (Spec (CommRingCat.of F))}

namespace SplitTorus

/-- The real pairing with the actual positive valuation, as a point homomorphism. -/
def pointRealFunctional (hA : IsSplitTorus A.toGrp) (phi : RealTorusSpace.Vstar A) :
    rationalPoints A.toGrp →* Multiplicative ℝ :=
  (RealTorusSpace.pair A phi).toAddMonoidHom.toMultiplicative.comp (valuation hA)

@[simp] theorem pointRealFunctional_apply (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) (a : rationalPoints A.toGrp) :
    (pointRealFunctional hA phi a).toAdd =
      RealTorusSpace.pair A phi (valuation hA a).toAdd := rfl

theorem pointRealFunctional_trivial (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) :
    rationalCommonNormKernel A.toGrp ≤ (pointRealFunctional hA phi).ker := by
  intro a ha
  have hv : valuation hA a = 1 := by
    exact (show a ∈ (valuation hA).ker from
      (BruhatTits.Cartan.centralizerValuation_ker (𝟙 A.toGrp)
        (BruhatTits.Cartan.restrictionEvaluation_id_bijective hA)).symm ▸ ha)
  change Multiplicative.ofAdd (RealTorusSpace.pair A phi (valuation hA a).toAdd) = 1
  rw [hv]
  simp

/-- The real parameter descended to the actual integer valuation image. -/
def positiveImageFunctional (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) : rationalImageRealFunctionals A.toGrp :=
  ((QuotientGroup.lift (rationalCommonNormKernel A.toGrp)
    (pointRealFunctional hA phi) (pointRealFunctional_trivial hA phi)).comp
      (rationalNormKernelQuotientEquiv A.toGrp).symm.toMonoidHom).toAdditive

@[simp] theorem positiveImageFunctional_projection (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) (a : rationalPoints A.toGrp) :
    positiveImageFunctional hA phi
      (Additive.ofMul (rationalValuationImageProjection A.toGrp a)) =
        RealTorusSpace.pair A phi (valuation hA a).toAdd := by
  have he : (rationalNormKernelQuotientEquiv A.toGrp).symm
      (rationalValuationImageProjection A.toGrp a) = QuotientGroup.mk a :=
    (rationalNormKernelQuotientEquiv A.toGrp).symm_apply_eq.mpr
      (rationalNormKernelQuotientEquiv_mk A.toGrp a).symm
  change (QuotientGroup.lift (rationalCommonNormKernel A.toGrp)
    (pointRealFunctional hA phi) (pointRealFunctional_trivial hA phi)
      ((rationalNormKernelQuotientEquiv A.toGrp).symm
        (rationalValuationImageProjection A.toGrp a))).toAdd = _
  rw [he]
  rfl

theorem positiveImageFunctional_pullback (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) :
    rationalImageCharacterPullback A.toGrp
      (rationalImagePositiveCharacter A.toGrp (positiveImageFunctional hA phi)) =
        positiveCharacter hA phi := by
  apply MonoidHom.ext
  intro a
  apply Units.ext
  change (Real.exp (-positiveImageFunctional hA phi
    (Additive.ofMul (rationalValuationImageProjection A.toGrp a)) *
      Real.log (LocalField.residueCardinality F)) : ℂ) = _
  rw [positiveImageFunctional_projection]
  rfl

end SplitTorus

/-- Additive real functionals extend along an injective actual image map. -/
theorem exists_rationalImageRealFunctional_extension (j : A.toGrp ⟶ M)
    (hj : Function.Injective (rationalValuationImageMap j))
    (phi : rationalImageRealFunctionals A.toGrp) :
    ∃ psi : rationalImageRealFunctionals M,
      psi.comp (rationalValuationImageMap j).toAdditive = phi :=
  (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom
    (rationalValuationImageMap j).toAdditive hj phi

/-- Every split-torus real parameter is the restriction of a positive actual
image character whenever its actual image map is injective. -/
theorem exists_positiveImageCharacter_extension_of_injective
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hj : Function.Injective (rationalValuationImageMap j))
    (phi : RealTorusSpace.Vstar A) :
    ∃ psi : rationalImageRealFunctionals M,
      (rationalImageCharacterPullback M (rationalImagePositiveCharacter M psi)).comp
        (rationalPoints.map j) = SplitTorus.positiveCharacter hA phi := by
  obtain ⟨psi, hpsi⟩ := exists_rationalImageRealFunctional_extension j hj
    (SplitTorus.positiveImageFunctional hA phi)
  refine ⟨psi, ?_⟩
  apply MonoidHom.ext
  intro a
  apply Units.ext
  change (Real.exp (-psi (Additive.ofMul
    (rationalValuationImageProjection M (rationalPoints.map j a))) *
      Real.log (LocalField.residueCardinality F)) : ℂ) = _
  rw [← rationalValuationImageMap_projection j a]
  have he := DFunLike.congr_fun hpsi
    (Additive.ofMul (rationalValuationImageProjection A.toGrp a))
  change psi (Additive.ofMul
    (rationalValuationImageMap j (rationalValuationImageProjection A.toGrp a))) =
      SplitTorus.positiveImageFunctional hA phi
        (Additive.ofMul (rationalValuationImageProjection A.toGrp a)) at he
  rw [he, SplitTorus.positiveImageFunctional_projection]
  rfl

/-- Every real parameter on an actual split component extends positively to
the actual valuation image of the connected reductive group. -/
theorem exists_positiveImageCharacter_extension
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j)
    (phi : RealTorusSpace.Vstar A) :
    ∃ psi : rationalImageRealFunctionals M,
      (rationalImageCharacterPullback M (rationalImagePositiveCharacter M psi)).comp
        (rationalPoints.map j) = SplitTorus.positiveCharacter hA phi :=
  exists_positiveImageCharacter_extension_of_injective hA j
    (rationalValuationImageMap_injective j hM hj) phi

/-- Injectivity of the actual image map realizes every split-torus real parameter. -/
theorem normalizedRealPart_imageCharacterPullback_surjective_of_injective
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hj : Function.Injective (rationalValuationImageMap j)) :
    Function.Surjective (fun chi : rationalImageCharacters M =>
      SplitTorus.normalizedRealPart hA
        ((rationalImageCharacterPullback M chi).comp (rationalPoints.map j))) := by
  intro phi
  obtain ⟨psi, hpsi⟩ := exists_positiveImageCharacter_extension_of_injective hA j hj phi
  refine ⟨rationalImagePositiveCharacter M psi, ?_⟩
  dsimp only
  rw [hpsi, SplitTorus.normalizedRealPart_positiveCharacter]

/-- The actual-image character real-part map to a split component is onto. -/
theorem normalizedRealPart_imageCharacterPullback_surjective
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (hM : IsConnectedReductive M) (hj : IsSplitComponent j) :
    Function.Surjective (fun chi : rationalImageCharacters M =>
      SplitTorus.normalizedRealPart hA
        ((rationalImageCharacterPullback M chi).comp (rationalPoints.map j))) :=
  normalizedRealPart_imageCharacterPullback_surjective_of_injective hA j
    (rationalValuationImageMap_injective j hM hj)

end Langlands.Plancherel
