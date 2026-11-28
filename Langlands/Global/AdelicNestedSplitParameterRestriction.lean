import Langlands.Global.AdelicCharacterParameterEquivalences
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.Global.AdelicSplitComponentShifts
import Langlands.Global.AdelicStandardPositiveLog

/-! # Restricting parameters to the split component of a containing parabolic -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace Langlands.Global

open GroupScheme AdelicGroupPoints

namespace AdelicGroupPoints

variable {F : Type} [Field F] {G H : GroupScheme (Spec (CommRingCat.of F))}

private def rationalComplexTensorEquiv (X : Type) [AddCommGroup X] :
    ℂ ⊗[ℚ] (ℚ ⊗[ℤ] X) ≃ₗ[ℂ] ℂ ⊗[ℤ] X :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ X

/-- Injective finite-index character restriction is an isomorphism on complex parameters. -/
def complexCharacterParameterPullbackEquiv (i : H ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    (hindex : (characterRestrict i).range.FiniteIndex) :
    ComplexCharacterParameter F G ≃ₗ[ℂ] ComplexCharacterParameter F H :=
  (rationalComplexTensorEquiv (rationalCharacters G)).symm.trans
    (((LinearEquiv.ofBijective (rationalCharacterRestrictRat i)
      (rationalCharacterRestrictRat_bijective_of_integralRestriction i hi hindex)).baseChange ℚ ℂ _ _).trans
      (rationalComplexTensorEquiv (rationalCharacters H)))

@[simp]
theorem complexCharacterParameterPullbackEquiv_apply (i : H ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    (hindex : (characterRestrict i).range.FiniteIndex) (x : ComplexCharacterParameter F G) :
    complexCharacterParameterPullbackEquiv i hi hindex x = parameterRestrict i x := by
  let f := (characterRestrict i).toIntLinearMap
  let y := (rationalComplexTensorEquiv (rationalCharacters G)).symm x
  have hNat : (rationalComplexTensorEquiv (rationalCharacters H)).toLinearMap ∘ₗ
        (f.baseChange ℚ).baseChange ℂ =
      f.baseChange ℂ ∘ₗ (rationalComplexTensorEquiv (rationalCharacters G)).toLinearMap := by
    ext
    simp [rationalComplexTensorEquiv]
  have h := LinearMap.congr_fun hNat y
  change rationalComplexTensorEquiv (rationalCharacters H) ((f.baseChange ℚ).baseChange ℂ y) =
    f.baseChange ℂ (rationalComplexTensorEquiv (rationalCharacters G) y) at h
  rw [show rationalComplexTensorEquiv (rationalCharacters G) y = x from LinearEquiv.apply_symm_apply _ _]
    at h
  exact h

end AdelicGroupPoints

namespace StandardParabolicFamily

open AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "j" I => (fam.a I ≫ fam.l I)

omit [NumberField F] in
private theorem finiteIndex_splitComponentRestriction (I : Idx) :
    (characterRestrict (j I)).range.FiniteIndex := by
  have hsurj := (fam.isCompatible I).levi.characterRestrict_bijective.2
  have hrange : (characterRestrict (j I)).range = (characterRestrict (fam.a I)).range := by
    ext χ
    change (∃ x, characterRestrict (j I) x = χ) ↔ ∃ y, characterRestrict (fam.a I) y = χ
    simp only [characterRestrict_comp, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨characterRestrict (fam.l I) x, hx⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, rfl⟩
  rw [hrange]
  exact (fam.isCompatible I).splitComponent.finiteIndex_range_characterRestrict
    (fam.isCompatible I).levi.isConnectedReductive

omit [NumberField F] in
private theorem injective_splitComponentRestriction (I : Idx) :
    Function.Injective (characterRestrict (j I)) := by
  let r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
    ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
  exact characterRestrict_splitComponent_injective r

private def splitParameterEquiv (J : Idx) :
    ComplexCharacterParameter F (fam.P J) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.A J).toGrp :=
  complexCharacterParameterPullbackEquiv (fam.a J ≫ fam.l J)
    (fam.injective_splitComponentRestriction J) (fam.finiteIndex_splitComponentRestriction J)

/-- The smaller parabolic's parameter restricted to the split component of the containing
parabolic, expressed as a complex character parameter of the containing parabolic. -/
def nestedSplitParameter {I J : Idx} (hIJ : I ≤ J) :
    ComplexCharacterParameter F (fam.P I) →ₗ[ℂ] ComplexCharacterParameter F (fam.P J) := by
  let k : (fam.A J).toGrp ⟶ fam.P I :=
    CommGroupScheme.groupHom (fam.nestedSplitComponentHom hIJ) ≫ fam.a I ≫ fam.l I
  exact (fam.splitParameterEquiv J).symm.toLinearMap.comp (parameterRestrict (F := F) k)

omit [NumberField F] in
private theorem nestedSplitParameter_pullback {I J : Idx} (hIJ : I ≤ J)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    parameterRestrict (j J) (fam.nestedSplitParameter hIJ lam) =
      parameterRestrict (CommGroupScheme.groupHom (fam.nestedSplitComponentHom hIJ) ≫ j I) lam := by
  have he (x : ComplexCharacterParameter F (fam.P J)) :
      fam.splitParameterEquiv J x = parameterRestrict (fam.a J ≫ fam.l J) x :=
    complexCharacterParameterPullbackEquiv_apply _ _ _ x
  rw [← he]
  exact LinearEquiv.apply_symm_apply _ _

/-- The nested split parameter evaluates on the outer split point as the original parameter
evaluates on its actual lift into the smaller parabolic. -/
theorem parameterPower_nestedSplitParameter {I J : Idx} (hIJ : I ≤ J)
    (lam : ComplexCharacterParameter F (fam.P I))
    (b : fam.positiveSplitComponent J) :
    parameterPower F (fam.P J) (fam.nestedSplitParameter hIJ lam) b.val =
      parameterPower F (fam.P I) lam (fam.splitLift hIJ b).val := by
  let k := CommGroupScheme.groupHom (fam.nestedSplitComponentHom hIJ) ≫ j I
  obtain ⟨a, ha, hba⟩ := b.property
  have he : map F (fam.A J).toGrp (fam.P J) (j J) a = b.val := hba
  have hL : map F (fam.A J).toGrp (fam.P I) k a = (fam.splitLift hIJ b).val := by
    let : IsClosedImmersion (fam.p I).hom.hom.left := fam.isClosedImmersion_p I
    apply (isClosedEmbedding_map F (fam.P I) G (fam.p I)).injective
    rw [fam.map_splitLift]
    have hc : k ≫ fam.nestedParabolicHom hIJ = j J := by
      change (CommGroupScheme.groupHom (fam.nestedSplitComponentHom hIJ) ≫
        fam.a I ≫ fam.l I) ≫ fam.nestedParabolicHom hIJ = _
      simpa only [Category.assoc] using fam.nestedSplitComponentHom_parabolic_comp hIJ
    rw [← map_comp_apply_of_hom, ← fam.nestedParabolicHom_comp hIJ,
      ← Category.assoc, hc, map_comp_apply_of_hom, he]
  rw [← he, ← parameterPower_parameterRestrict, fam.nestedSplitParameter_pullback hIJ,
    parameterPower_parameterRestrict, hL]

omit [NumberField F] in
/-- Unitary parameters remain unitary upon restriction to the containing split component. -/
theorem parameterRealPart_nestedSplitParameter_eq_zero {I J : Idx} (hIJ : I ≤ J)
    {lam : ComplexCharacterParameter F (fam.P I)} (hlam : parameterRealPart F (fam.P I) lam = 0) :
    parameterRealPart F (fam.P J) (fam.nestedSplitParameter hIJ lam) = 0 := by
  let e := realCharacterParameterPullbackEquiv (j J) (fam.injective_splitComponentRestriction J)
    (fam.finiteIndex_splitComponentRestriction J)
  apply e.injective
  have h := congrArg (parameterRealPart F (fam.A J).toGrp)
    (fam.nestedSplitParameter_pullback hIJ lam)
  rw [parameterRealPart_pullback, parameterRealPart_pullback, hlam, map_zero] at h
  change e _ = e _
  rw [e.map_zero, realCharacterParameterPullbackEquiv_apply]
  exact h

/-- Restriction through nested split components preserves values on the actual lifted points
and preserves unitarity. -/
def NestedSplitParameterRestrictionStatement : Prop :=
  ∀ {I J : Idx} (hIJ : I ≤ J) (lam : ComplexCharacterParameter F (fam.P I)),
    (∀ b : fam.positiveSplitComponent J,
      parameterPower F (fam.P J) (fam.nestedSplitParameter hIJ lam) b.val =
        parameterPower F (fam.P I) lam (fam.splitLift hIJ b).val) ∧
    (parameterRealPart F (fam.P I) lam = 0 →
      parameterRealPart F (fam.P J) (fam.nestedSplitParameter hIJ lam) = 0)

theorem nestedSplitParameterRestriction : fam.NestedSplitParameterRestrictionStatement := by
  intro I J hIJ lam
  exact ⟨fam.parameterPower_nestedSplitParameter hIJ lam,
    fam.parameterRealPart_nestedSplitParameter_eq_zero hIJ⟩

end StandardParabolicFamily

end Langlands.Global
