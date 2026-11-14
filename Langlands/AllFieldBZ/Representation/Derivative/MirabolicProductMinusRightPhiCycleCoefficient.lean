import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct
open scoped NNReal
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility determinantNorm_rankCast_symm determinantNorm_rightCycle determinantNorm_rightIdentity determinantNorm_rightPsi determinantNorm_rightSubgroup determinantNorm_val_eq_projection generalLinearRankCastIso leftPhiExpected leftPhiProduct leviModulus_binary mirabolicRankCastIso mulEquivHaarChar_conj_levi_inv mulEquivHaarChar_splitKernelConjugation_levi parabolicHalfModulus_binary plusKernelThetaSmooth plusKernelThetaSmooth_sectionInvariant psiMinus_zero_trivial radical_compactOpenBasis radical_compactOpenCover rightBoundaryQuotient rightBoundaryQuotientEquiv rightBoundaryQuotientEquiv_action rightBoundaryQuotientEquiv_natural rightBoundaryTopEquiv rightCharacter_of_mem_rightPsiKernel rightCycleCoefficient rightCycleCoefficientEquiv rightCycleCoefficientEquiv_mk_tmul rightCycleCoefficientEquiv_natural rightCycleCoefficientEquiv_natural_tmul rightCycleCoefficientEquiv_section rightCycleHaarRatio_apply rightCycleIntersectionToKernel rightCycleKernelToIntersection rightCycleStagesCoefficient rightCycle_phiMinus_tmul rightCycle_relations_eq rightCycle_scalar_eq rightIdentityCoefficient rightIdentityCoefficientEquiv rightIdentityCoefficientEquiv_mk_tmul rightIdentityCoefficientEquiv_natural rightIdentityCoefficientEquiv_natural_tmul rightIdentityCoefficientEquiv_section rightIdentityHaarRatio_apply rightIdentityIntersectionToKernel rightIdentityKernelToIntersection rightIdentityStagesCoefficient rightIdentity_psiMinus_tmul rightIdentity_relations_eq rightIdentity_scalar_eq rightPhiBoundary rightPhiProduct rightPhiQuotient rightPhiSubobject rightPsiCoefficientEquiv rightPsiCoefficientEquiv_action rightPsiCoefficientEquiv_action_tmul rightPsiCoefficientEquiv_mk_tmul rightPsiCoefficientEquiv_natural rightPsiCoefficientEquiv_natural_tmul rightPsiCoefficientEquiv_psiMinus rightPsiCoefficientEquiv_section rightPsiCompatibility_zero rightPsiHaarRatio_apply rightPsiInducingCoefficient rightPsiInducingCoefficient_kernel rightPsiKernelCharacter rightPsiLocalizedTensorBilinear rightPsiLocalizedTensorEquiv rightPsiLocalizedTensorEquiv_mk_tmul rightPsiLocalizedTensorForward rightPsiLocalizedTensor_comp rightPsiStagesCoefficient rightPsiTensorBilinear rightPsiTensorEquiv rightPsiTensorEquiv_mk_tmul rightPsiTensorForward rightPsiZeroTarget rightPsiZeroTargetEquiv rightPsiZeroTargetEquiv_action rightPsiZeroTargetEquiv_natural rightPsi_scalar_eq twist_rightInducing_levi_zero
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic hiding leviRadical_haarCharacter radicalCoordinates_isAddHaar radicalHaar_map_leviConj
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-! ## Localized coinvariants of the inducing coefficient under `N` -/

section LocalizedTensor
variable (T : F.TopologicalData) {m r : ℕ}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (τ : Representation ℂ (mirabolic r F.Carrier) W)
  (ρ : Representation ℂ (GeneralLinear m F.Carrier) V) (θ : radical r F.Carrier →* ℂˣ)

/-- A character of the radical, on `N` through the mirabolic block. -/
abbrev rightPsiKernelCharacter : rightPsiKernel m r F.Carrier →* ℂˣ :=
  θ.comp (rightPsiKernelEquiv (m := m) (r := r) (R := F.Carrier)).toMonoidHom

/-- Localizing the first factor intertwines `N` with its character. -/
theorem rightPsiLocalizedTensor_comp (g : rightPsiKernel m r F.Carrier) :
    TensorProduct.map (Jacquet.Localization.mk τ (radical r F.Carrier) θ) LinearMap.id ∘ₗ
        rightPsiInducingCoefficient T τ ρ g.val =
      (rightPsiKernelCharacter θ g : ℂ) •
        TensorProduct.map (Jacquet.Localization.mk τ (radical r F.Carrier) θ)
          (LinearMap.id : V →ₗ[ℂ] V) := by
  apply TensorProduct.ext'
  intro w v
  change TensorProduct.map (Jacquet.Localization.mk τ (radical r F.Carrier) θ) LinearMap.id
      (rightPsiInducingCoefficient T τ ρ g.val (w ⊗ₜ v)) =
    (θ (rightPsiKernelEquiv g) : ℂ) •
      TensorProduct.map (Jacquet.Localization.mk τ (radical r F.Carrier) θ) LinearMap.id (w ⊗ₜ v)
  rw [rightPsiInducingCoefficient_kernel, TensorProduct.map_tmul, TensorProduct.map_tmul,
    TensorProduct.smul_tmul']
  change Jacquet.Localization.mk τ (radical r F.Carrier) θ
      (τ ((rightPsiKernelEquiv g : radical r F.Carrier) : mirabolic r F.Carrier) w) ⊗ₜ
        LinearMap.id v = _
  rw [Jacquet.Localization.mk_apply_subgroup]

/-- Localizing the first factor gives the forward map on localized `N`-coinvariants. -/
def rightPsiLocalizedTensorForward :
    Jacquet.Localization.Coinvariants (rightPsiInducingCoefficient T τ ρ)
        (rightPsiKernel m r F.Carrier) (rightPsiKernelCharacter θ) →ₗ[ℂ]
      Jacquet.Localization.Coinvariants τ (radical r F.Carrier) θ ⊗[ℂ] V :=
  Jacquet.Localization.lift _ _ _
    (TensorProduct.map (Jacquet.Localization.mk τ (radical r F.Carrier) θ) LinearMap.id)
    (fun g x => LinearMap.congr_fun (rightPsiLocalizedTensor_comp T τ ρ θ g) x)

/-- The bilinear map `([w], v) ↦ [w ⊗ v]`. -/
def rightPsiLocalizedTensorBilinear :
    Jacquet.Localization.Coinvariants τ (radical r F.Carrier) θ →ₗ[ℂ]
      V →ₗ[ℂ] Jacquet.Localization.Coinvariants (rightPsiInducingCoefficient T τ ρ)
        (rightPsiKernel m r F.Carrier) (rightPsiKernelCharacter θ) :=
  Jacquet.Localization.lift τ (radical r F.Carrier) θ
    ((TensorProduct.mk ℂ W V).compr₂ (Jacquet.Localization.mk _ _ _)) (fun u w => by
    apply LinearMap.ext
    intro v
    change Jacquet.Localization.mk (rightPsiInducingCoefficient T τ ρ)
        (rightPsiKernel m r F.Carrier) (rightPsiKernelCharacter θ) (τ u w ⊗ₜ v) =
      (θ u : ℂ) • Jacquet.Localization.mk (rightPsiInducingCoefficient T τ ρ)
        (rightPsiKernel m r F.Carrier) (rightPsiKernelCharacter θ) (w ⊗ₜ v)
    have h := rightPsiInducingCoefficient_kernel T τ ρ ((rightPsiKernelEquiv (m := m)).symm u) w v
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h, Jacquet.Localization.mk_apply_subgroup]
    change (θ (rightPsiKernelEquiv ((rightPsiKernelEquiv (m := m)).symm u)) : ℂ) • _ = _
    rw [MulEquiv.apply_symm_apply])

/-- `θ`-localized `N`-coinvariants of `χ_R (τ ⊠ ρ)` are `τ_(V_(r+1), θ) ⊗ ρ`. -/
def rightPsiLocalizedTensorEquiv :
    Jacquet.Localization.Coinvariants (rightPsiInducingCoefficient T τ ρ)
        (rightPsiKernel m r F.Carrier) (rightPsiKernelCharacter θ) ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants τ (radical r F.Carrier) θ ⊗[ℂ] V :=
  LinearEquiv.ofLinearMap (rightPsiLocalizedTensorForward T τ ρ θ)
    (TensorProduct.lift (rightPsiLocalizedTensorBilinear T τ ρ θ))
    (by
      apply TensorProduct.ext'
      intro a v
      obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective τ (radical r F.Carrier) θ a
      rfl)
    (by
      apply Jacquet.Localization.hom_ext
      apply TensorProduct.ext'
      intro w v
      rfl)

@[simp] theorem rightPsiLocalizedTensorEquiv_mk_tmul (w : W) (v : V) :
    rightPsiLocalizedTensorEquiv T τ ρ θ
        (Jacquet.Localization.mk (rightPsiInducingCoefficient T τ ρ)
          (rightPsiKernel m r F.Carrier) (rightPsiKernelCharacter θ) (w ⊗ₜ v)) =
      Jacquet.Localization.mk τ (radical r F.Carrier) θ w ⊗ₜ v := rfl

end LocalizedTensor
/-! ## The kernel intersection -/

section Intersection
variable (k r : ℕ) (R : Type*) [CommRing R]

/-- An element of `A` as an element of `S ∩ ker plusProjection`. -/
def rightCycleIntersectionToKernel (a : rightCycleKernelIntersection k r R) :
    (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightCycStabilizer k r R).subtype :=
  ⟨⟨((a : rightCycleInducing k r R) : rightStages k r R 0).val,
    (a : rightCycleInducing k r R).property⟩,
    congrArg Subtype.val (MonoidHom.mem_ker.mp a.property)⟩

/-- The element of `A` over an element of `S ∩ ker plusProjection`. -/
def rightCycleKernelToIntersection
    (n : (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightCycStabilizer k r R).subtype) :
    rightCycleKernelIntersection k r R :=
  ⟨⟨⟨n.val.val, rightCycStabilizer_le_stages k r R n.val.property⟩, n.val.property⟩,
    MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp n.property))⟩

end Intersection
/-! ## The coefficient and its kernel quotient -/

section Coefficient
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (τ : Representation ℂ (mirabolic (r + 1) F.Carrier) W)
  (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)

/-- The orbit coefficient at the cycle: `χ_R (τ ⊠ ρ)` through the inclusion of the
stabilizer into the right mixed subgroup. -/
abbrev rightCycleCoefficient :
    Representation ℂ (rightCycStabilizer k r F.Carrier) (W ⊗[ℂ] V) :=
  (rightPsiInducingCoefficient T τ ρ).comp (rightCycleInclusion k r F.Carrier)

/-- The coefficient restricted to `HP = S ∩ P`. -/
abbrev rightCycleStagesCoefficient :
    Representation ℂ (rightCycleInducing k r F.Carrier) (W ⊗[ℂ] V) :=
  (rightCycleCoefficient T k r τ ρ).comp
    (Subgroup.subgroupOfEquivOfLe (rightCycStabilizer_le_stages k r F.Carrier)).toMonoidHom

/-- With the character `θ_r` of the kernel subgroup on `A`, the localized relations of the
restricted coefficient are the `θ_r`-localized kernel relations of the right mixed
coefficient. -/
theorem rightCycle_relations_eq (η : rightCycleKernelIntersection k r F.Carrier →* ℂˣ)
    (hη : ∀ a, η a = T.mirabolicTheta ψ r (rightPsiKernelEquiv
      (rightCycleKernelEquiv k r F.Carrier (rightCycleIntersectionToKernel k r F.Carrier a)))) :
    Jacquet.Localization.relations (rightCycleStagesCoefficient T k r τ ρ)
        (rightCycleKernelIntersection k r F.Carrier) η =
      Jacquet.Localization.relations (rightPsiInducingCoefficient T τ ρ)
        (rightPsiKernel (k + 1) (r + 1) F.Carrier)
        (rightPsiKernelCharacter (T.mirabolicTheta ψ r)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨⟨a, v⟩, rfl⟩
    change rightCycleStagesCoefficient T k r τ ρ a v - (η a : ℂ) • v ∈ _
    rw [hη a]
    exact Jacquet.Localization.sub_mem_relations _ _ _
      (rightCycleKernelEquiv k r F.Carrier (rightCycleIntersectionToKernel k r F.Carrier a)) v
  · apply Submodule.span_le.2
    rintro _ ⟨⟨g, v⟩, rfl⟩
    obtain ⟨n, rfl⟩ := (rightCycleKernelEquiv k r F.Carrier).surjective g
    have key := Jacquet.Localization.sub_mem_relations (rightCycleStagesCoefficient T k r τ ρ)
      (rightCycleKernelIntersection k r F.Carrier) η (rightCycleKernelToIntersection k r F.Carrier n) v
    rw [hη (rightCycleKernelToIntersection k r F.Carrier n)] at key
    exact key

/-- The localized coefficient quotient at the cycle is `τ_(V_(r+2), θ_r) ⊗ ρ`. -/
def rightCycleCoefficientEquiv (η : rightCycleKernelIntersection k r F.Carrier →* ℂˣ)
    (hη : ∀ a, η a = T.mirabolicTheta ψ r (rightPsiKernelEquiv
      (rightCycleKernelEquiv k r F.Carrier (rightCycleIntersectionToKernel k r F.Carrier a)))) :
    Jacquet.Localization.Coinvariants (rightCycleStagesCoefficient T k r τ ρ)
        (rightCycleKernelIntersection k r F.Carrier) η ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants τ (radical (r + 1) F.Carrier) (T.mirabolicTheta ψ r) ⊗[ℂ]
        V :=
  (Submodule.quotEquivOfEq _ _ (rightCycle_relations_eq T ψ k r τ ρ η hη)).trans
    (rightPsiLocalizedTensorEquiv T τ ρ (T.mirabolicTheta ψ r))

@[simp] theorem rightCycleCoefficientEquiv_mk_tmul
    (η : rightCycleKernelIntersection k r F.Carrier →* ℂˣ)
    (hη : ∀ a, η a = T.mirabolicTheta ψ r (rightPsiKernelEquiv
      (rightCycleKernelEquiv k r F.Carrier (rightCycleIntersectionToKernel k r F.Carrier a))))
    (w : W) (v : V) :
    rightCycleCoefficientEquiv T ψ k r τ ρ η hη
        (Jacquet.Localization.mk (rightCycleStagesCoefficient T k r τ ρ)
          (rightCycleKernelIntersection k r F.Carrier) η (w ⊗ₜ v)) =
      Jacquet.Localization.mk τ (radical (r + 1) F.Carrier) (T.mirabolicTheta ψ r) w ⊗ₜ v := rfl

/-- The section `l = [[p, X], [0, a]]` acts on a pure tensor by
`χ_R(successor l) [τ(successor p) w] ⊗ ρ(a) v`. -/
theorem rightCycleCoefficientEquiv_section
    (η : rightCycleKernelIntersection k r F.Carrier →* ℂˣ)
    (hη : ∀ a, η a = T.mirabolicTheta ψ r (rightPsiKernelEquiv
      (rightCycleKernelEquiv k r F.Carrier (rightCycleIntersectionToKernel k r F.Carrier a))))
    (l : (rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier)))
    (w : W) (v : V) :
    letI := T.topology
    rightCycleCoefficientEquiv T ψ k r τ ρ η hη
        (Jacquet.Localization.mk (rightCycleStagesCoefficient T k r τ ρ)
          (rightCycleKernelIntersection k r F.Carrier) η
          (rightCycleStagesCoefficient T k r τ ρ
            (Induction.SplitKernelLocalization.subgroupSection
              ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap
                (rightStages k r F.Carrier 0))
              (rightCycleInducing k r F.Carrier) (rightCycleInducing_section_mem k r F.Carrier) l)
            (w ⊗ₜ v))) =
      ((T.rightCharacter (k + 1) (r + 1)).toMonoidHom
          (rightCycleInclusion k r F.Carrier (rightCycleSectionElement k r F.Carrier l)) : ℂ) •
        (Jacquet.Localization.mk τ (radical (r + 1) F.Carrier) (T.mirabolicTheta ψ r)
          (τ (successor (rightProjection (rightCycleLevi k r F.Carrier l)).1) w) ⊗ₜ
            ρ (rightProjection (rightCycleLevi k r F.Carrier l)).2 v) := by
  let _ := T.topology
  have hx : rightInducingRepresentation τ ρ
      (rightCycleInclusion k r F.Carrier (rightCycleSectionElement k r F.Carrier l)) (w ⊗ₜ v) =
      τ (successor (rightProjection (rightCycleLevi k r F.Carrier l)).1) w ⊗ₜ
        ρ (rightProjection (rightCycleLevi k r F.Carrier l)).2 v := by
    rw [rightInducingRepresentation_tmul, ← rightCoefficient_zero_apply,
      rightCoefficient_rightCycleSectionElement]
  change rightCycleCoefficientEquiv T ψ k r τ ρ η hη
      (Jacquet.Localization.mk (rightCycleStagesCoefficient T k r τ ρ)
        (rightCycleKernelIntersection k r F.Carrier) η
        (((T.rightCharacter (k + 1) (r + 1)).toMonoidHom
            (rightCycleInclusion k r F.Carrier (rightCycleSectionElement k r F.Carrier l)) : ℂ) •
          rightInducingRepresentation τ ρ
            (rightCycleInclusion k r F.Carrier (rightCycleSectionElement k r F.Carrier l))
            (w ⊗ₜ v))) = _
  exact linearEquiv_map_smul_of_eq _ _ _ hx rfl

/-- The naturality of `rightCycleCoefficientEquiv_natural` on a pure tensor. -/
theorem rightCycleCoefficientEquiv_natural_tmul
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)}
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (f₁ : letI := T.topology; A ⟶ A') (f₂ : letI := T.topology; B ⟶ B')
    (t : (A ⊗[ℂ] B) →ₗ[ℂ] (A' ⊗[ℂ] B'))
    (ht : letI := T.topology; ∀ (w : A) (b : B),
      t (w ⊗ₜ b) = SmoothRep.hom f₁ w ⊗ₜ SmoothRep.hom f₂ b)
    (η : rightCycleKernelIntersection k r F.Carrier →* ℂˣ)
    (hη : ∀ a, η a = T.mirabolicTheta ψ r (rightPsiKernelEquiv
      (rightCycleKernelEquiv k r F.Carrier (rightCycleIntersectionToKernel k r F.Carrier a))))
    (w : letI := T.topology; A) (b : letI := T.topology; B) :
    letI := T.topology
    rightCycleCoefficientEquiv T ψ k r A'.representation B'.representation η hη
        (Jacquet.Localization.mk (rightCycleStagesCoefficient T k r A'.representation
          B'.representation) (rightCycleKernelIntersection k r F.Carrier) η (t (w ⊗ₜ b))) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map f₁)).toLinearMap
        (SmoothRep.hom f₂).toLinearMap
        (rightCycleCoefficientEquiv T ψ k r A.representation B.representation η hη
          (Jacquet.Localization.mk (rightCycleStagesCoefficient T k r A.representation
            B.representation) (rightCycleKernelIntersection k r F.Carrier) η (w ⊗ₜ b))) := by
  let _ := T.topology
  refine (congrArg (fun x => rightCycleCoefficientEquiv T ψ k r A'.representation
      B'.representation η hη (Jacquet.Localization.mk _ _ η x)) (ht w b)).trans ?_
  refine (rightCycleCoefficientEquiv_mk_tmul T ψ k r A'.representation B'.representation η hη
    _ _).trans ?_
  refine (congrArg (fun x : Jacquet.Localization.Coinvariants A'.representation
      (radical (r + 1) F.Carrier) (T.mirabolicTheta ψ r) => x ⊗ₜ[ℂ] SmoothRep.hom f₂ b)
    (Mirabolic.phiMinus_map_quotient T ψ r f₁ w).symm).trans ?_
  exact (TensorProduct.map_tmul (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map f₁)).toLinearMap
    (SmoothRep.hom f₂).toLinearMap (Mirabolic.phiMinusQuotient T ψ r A w) b).symm

/-- The coefficient identification is natural for linear maps acting by `f₁ ⊗ f₂` on
pure tensors. -/
theorem rightCycleCoefficientEquiv_natural
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)}
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (f₁ : letI := T.topology; A ⟶ A') (f₂ : letI := T.topology; B ⟶ B')
    (t : (A ⊗[ℂ] B) →ₗ[ℂ] (A' ⊗[ℂ] B'))
    (ht : letI := T.topology; ∀ (w : A) (b : B),
      t (w ⊗ₜ b) = SmoothRep.hom f₁ w ⊗ₜ SmoothRep.hom f₂ b)
    (η : rightCycleKernelIntersection k r F.Carrier →* ℂˣ)
    (hη : ∀ a, η a = T.mirabolicTheta ψ r (rightPsiKernelEquiv
      (rightCycleKernelEquiv k r F.Carrier (rightCycleIntersectionToKernel k r F.Carrier a))))
    (x : A ⊗[ℂ] B) :
    letI := T.topology
    rightCycleCoefficientEquiv T ψ k r A'.representation B'.representation η hη
        (Jacquet.Localization.mk (rightCycleStagesCoefficient T k r A'.representation
          B'.representation) (rightCycleKernelIntersection k r F.Carrier) η (t x)) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map f₁)).toLinearMap
        (SmoothRep.hom f₂).toLinearMap
        (rightCycleCoefficientEquiv T ψ k r A.representation B.representation η hη
          (Jacquet.Localization.mk (rightCycleStagesCoefficient T k r A.representation
            B.representation) (rightCycleKernelIntersection k r F.Carrier) η x)) := by
  let _ := T.topology
  induction x using TensorProduct.inductionOn with
  | tmul w b => exact rightCycleCoefficientEquiv_natural_tmul T ψ k r f₁ f₂ t ht η hη w b
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (LinearMap.map_add (TensorProduct.map
      (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map f₁)).toLinearMap
      (SmoothRep.hom f₂).toLinearMap) _ _).symm

end Coefficient
/-! ## The target action -/

section Target
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)

/-- `Φ⁻τ(p) ⊗ ρ(a)` on the class of `w ⊗ b`. -/
theorem rightCycle_phiMinus_tmul
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (g : mirabolic r F.Carrier) (a : GeneralLinear (k + 1) F.Carrier) (w : A) (b : B) :
    letI := T.topology
    TensorProduct.map (((Mirabolic.phiMinus T ψ r).obj A).representation g) (B.representation a)
        (Jacquet.Localization.mk A.representation (radical (r + 1) F.Carrier)
          (T.mirabolicTheta ψ r) w ⊗ₜ b) =
      (Mirabolic.phiMinusCharacter T r g : ℂ) •
        (Jacquet.Localization.mk A.representation (radical (r + 1) F.Carrier)
          (T.mirabolicTheta ψ r) (A.representation (successor g) w) ⊗ₜ B.representation a b) := by
  let _ := T.topology
  exact (TensorProduct.map_tmul _ _ (Mirabolic.phiMinusQuotient T ψ r A w) b).trans
    ((congrArg (· ⊗ₜ[ℂ] _) (Mirabolic.phiMinus_action T ψ r A g w)).trans
      (TensorProduct.smul_tmul' _ _ _).symm)

end Target
/-! ## The scalars -/

section Scalar
open Langlands.Induction
open Langlands.QuotientIntegration
theorem determinantNorm_val_eq_projection (T : F.TopologicalData) {n : ℕ}
    (g : mirabolic n F.Carrier) :
    T.determinantNorm (n + 1) g.val = T.determinantNorm n (projection g) := by
  change T.normalizedAbsUnits (GeneralLinear.determinant g.val) =
    T.normalizedAbsUnits (GeneralLinear.determinant (projection g))
  rw [GeneralLinear.Mirabolic.determinant_projection]

/-- `ν(l)^(-1/2) · |det a| · χ_R(successor l) = χ_R(l) · ν(p)^(-1/2)` at
`l = [[p, X], [0, a]]`, for the right characters of shapes `(k+1, r+1)` and `(k+1, r)`. -/
theorem rightCycle_scalar_eq (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    haveI := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
    ∀ [MeasurableSpace (rightCycleRetraction k r F.Carrier).ker]
      [BorelSpace (rightCycleRetraction k r F.Carrier).ker]
      [LocallyCompactSpace (rightCycleRetraction k r F.Carrier).ker]
      [MeasurableSpace ((rightCycleInducing k r F.Carrier).comap
        (rightCycleRetraction k r F.Carrier).ker.subtype)]
      [BorelSpace ((rightCycleInducing k r F.Carrier).comap
        (rightCycleRetraction k r F.Carrier).ker.subtype)],
      (((Mirabolic.phiMinusCharacter T (k + r + 1)).comp (Subgroup.subtype
          ((rightStages k r F.Carrier 0).comap
            (plusSuccessor (n := k + r + 1) (F := F.Carrier))))) l : ℂ) *
          (Jacquet.complexCharacter (splitKernelHaarRatio (rightCycleRetraction k r F.Carrier)
            ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap
              (rightStages k r F.Carrier 0))
            (rightCycleInducing k r F.Carrier) (rightCycleInducing_section_mem k r F.Carrier)
            ((rightCycStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val)) l : ℂ) *
        ((T.rightCharacter (k + 1) (r + 1)).toMonoidHom
          (rightCycleInclusion k r F.Carrier (rightCycleSectionElement k r F.Carrier l)) : ℂ) =
      ((T.rightCharacter (k + 1) r).toMonoidHom (rightCycleLevi k r F.Carrier l) : ℂ) *
        (Mirabolic.phiMinusCharacter T r (rightProjection (rightCycleLevi k r F.Carrier l)).1 : ℂ) := by
  let _ := T.topology
  let _ := T.fieldT2
  let _ := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  have _ := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
  intro _ _ _ _ _
  rw [LocalFieldPackage.TopologicalData.rightCharacter_apply T (k + 1) (r + 1),
    ← rightCoefficient_zero_apply, rightCoefficient_rightCycleSectionElement,
    LocalFieldPackage.TopologicalData.rightLeviCharacter_apply,
    LocalFieldPackage.TopologicalData.rightCharacter_apply T (k + 1) r,
    LocalFieldPackage.TopologicalData.rightLeviCharacter_apply,
    Jacquet.complexCharacter_apply, rightCycleHaarRatio_apply T k r l]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_realPowerCharacter,
    projection_successor]
  rw [determinantNorm_rightCycle T k r l,
    ← determinantNorm_val_eq_projection T (rightProjection (rightCycleLevi k r F.Carrier l)).1]
  exact rightPsi_scalar_identity_complex _ _ (k + 1) (r + 1)

end Scalar
end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
