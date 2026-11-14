import Langlands.BruhatTits.IntegralModels.UnramifiedFullModelConstruction
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralZeroAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement
import Langlands.BruhatTits.IntegralModels.Transport.Model
import Langlands.Geometry.Building.UnramifiedVertexMaximalBoundedProof
import Langlands.Geometry.Building.UnramifiedFiniteVertexFixerAssembly
import Langlands.Geometry.Building.IntegerValuationNormalizerSharpReduction
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof
import Langlands.Geometry.Building.UnramifiedSplitBoundedPoints
import Langlands.GroupScheme.IntegralModel.MaximalBoundedConstruction
import Langlands.GroupScheme.IntegralModel.SmoothIntersectionConstruction
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementProof
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Unramified parahoric models from two torus inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj Pointwise

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BruhatTits.IntegralModels

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]

/-- Inner transport carries a normal subgroup intersected with an apartment
fixer to the same subgroup intersected with the translated apartment fixer. -/
theorem map_normal_inf_apartmentFixer_innerIso
    (C : MaximalUnramified.BuildingData F G)
    (H : Subgroup (rationalPoints G)) (hH : H.Normal)
    (g : rationalPoints G) (Ω : Set C.Apartment) :
    (H ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)).map
        (rationalPoints.map (G.innerIso g).hom) =
      H ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω) := by
  have hnormal : H.map (rationalPoints.map (G.innerIso g).hom) = H := by
    rw [rationalPoints_map_innerIso]
    exact Subgroup.normal_iff_map_conj_eq.mp hH g
  have hfix : (C.pointwiseFixer (C.apartmentMap '' Ω)).map
      (rationalPoints.map (G.innerIso g).hom) =
        C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω) := by
    rw [rationalPoints_map_innerIso]
    change (fixingSubgroup (rationalPoints G) (C.apartmentMap '' Ω)).map
        (MulAut.conj g).toMonoidHom =
      fixingSubgroup (rationalPoints G) ((fun x => g • C.apartmentMap x) '' Ω)
    apply SubMulAction.fixingSubgroup_map_conj_eq
    rw [← Set.image_smul, Set.image_image]
  rw [Subgroup.map_inf_eq _ _ _ (rationalPoints_map_injective_of_iso _), hnormal, hfix]

/-- Both fixer identities transfer together with the actual relative component. -/
theorem transport_relativeComponentModelData_apartmentFixers
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (Ω : Set C.Apartment)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hfull : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))
    (hneutral : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (g : rationalPoints G) :
    (D.transport (G.innerIso g)).full.integralPoints =
        characterValuationKernel (MaximalUnramified.valuation F) G ⊓
          C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω) ∧
      (D.transport (G.innerIso g)).neutral.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω) := by
  constructor
  · rw [D.transport_full_integralPoints, hfull]
    exact map_normal_inf_apartmentFixer_innerIso C _
      (characterValuationKernel_normal _ _) g Ω
  · rw [D.transport_neutral_integralPoints, hneutral]
    exact map_normal_inf_apartmentFixer_innerIso C _ E.normal_zeroPoints g Ω

/-- The two torus inputs suffice for compatible full and neutral models over
the actual unramified integers, including every translated apartment. -/
theorem exists_unramifiedParahoricModel_of_torusInputs
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u})
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (g : rationalPoints G) (Ω : Set C.Apartment) (hne : Ω.Nonempty)
    (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    ∃ D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G,
      D.full.integralPoints =
          characterValuationKernel (MaximalUnramified.valuation F) G ⊓
            C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω) ∧
        D.neutral.integralPoints =
          E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω) := by
  obtain ⟨D, hD⟩ := exists_relativeComponentModelData_of_vertexInputs
    MaximalUnramified.vertexOneStabilizerMaximalBounded
    MaximalUnramified.finiteVertexFixerApproximation
    maximalBoundedIntegralModel IntegralModel.smoothIntersection
    IntegralModel.finiteIndexEnlargement F G C 1 Ω hne hb
  have hfull : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω) := by
    simpa only [one_smul] using hD
  have hsharp := E.wholeApartmentZeroFixer_sup_sharpFixer_eq_of_simplyConnectedNormalizer
    C MaximalUnramified.simplyConnectedNormalizerAffineWeyl hne hb
  have hneutral := unramifiedNeutral_integralPoints_eq_zeroFixer
    C E Ω D hfull hModel hBound hsharp
  exact ⟨D.transport (G.innerIso g),
    transport_relativeComponentModelData_apartmentFixers C E Ω D hfull hneutral g⟩

/-- Choose the constructed full model together with its actual relative
identity component, conditional only on the two torus inputs. -/
def unramifiedParahoricModelOfTorusInputs
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u})
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (g : rationalPoints G) (Ω : Set C.Apartment) (hne : Ω.Nonempty)
    (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G :=
  Classical.choose
    (exists_unramifiedParahoricModel_of_torusInputs hModel hBound C E g Ω hne hb)

/-- The constructed pair has both prescribed integral-point images inside the
original rational-point group. -/
theorem unramifiedParahoricModelOfTorusInputs_integralPoints
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u})
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (g : rationalPoints G) (Ω : Set C.Apartment) (hne : Ω.Nonempty)
    (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    (unramifiedParahoricModelOfTorusInputs hModel hBound C E g Ω hne hb).full.integralPoints =
        characterValuationKernel (MaximalUnramified.valuation F) G ⊓
          C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω) ∧
      (unramifiedParahoricModelOfTorusInputs hModel hBound C E g Ω hne hb).neutral.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω) :=
  Classical.choose_spec
    (exists_unramifiedParahoricModel_of_torusInputs hModel hBound C E g Ω hne hb)

end Unramified

/-- The exact host target follows from the two remaining torus propositions,
without any additional premise on its original building or zero datum. -/
theorem unramifiedParahoricModel_of_torusInputs
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u}) :
    UnramifiedParahoricModelStatement.{u} := by
  intro F _ _ _ _ G _ C E g Ω hne hb
  exact exists_unramifiedParahoricModel_of_torusInputs hModel hBound C E g Ω hne hb

end Langlands.BruhatTits.IntegralModels
