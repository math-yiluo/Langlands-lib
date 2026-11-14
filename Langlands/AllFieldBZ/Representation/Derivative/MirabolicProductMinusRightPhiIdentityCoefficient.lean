import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct
open scoped NNReal
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility determinantNorm_rankCast_symm determinantNorm_rightIdentity determinantNorm_rightPsi generalLinearRankCastIso leftPhiExpected leftPhiProduct leviModulus_binary mirabolicRankCastIso mulEquivHaarChar_conj_levi_inv mulEquivHaarChar_splitKernelConjugation_levi parabolicHalfModulus_binary plusKernelThetaSmooth plusKernelThetaSmooth_sectionInvariant psiMinus_zero_trivial radical_compactOpenBasis radical_compactOpenCover rightBoundaryQuotient rightBoundaryQuotientEquiv rightBoundaryQuotientEquiv_action rightBoundaryQuotientEquiv_natural rightBoundaryTopEquiv rightCharacter_of_mem_rightPsiKernel rightIdentityCoefficient rightIdentityCoefficientEquiv rightIdentityCoefficientEquiv_mk_tmul rightIdentityCoefficientEquiv_natural rightIdentityCoefficientEquiv_natural_tmul rightIdentityCoefficientEquiv_section rightIdentityHaarRatio_apply rightIdentityIntersectionToKernel rightIdentityKernelToIntersection rightIdentityStagesCoefficient rightIdentity_psiMinus_tmul rightIdentity_relations_eq rightIdentity_scalar_eq rightPhiBoundary rightPhiProduct rightPhiQuotient rightPhiSubobject rightPsiCoefficientEquiv rightPsiCoefficientEquiv_action rightPsiCoefficientEquiv_action_tmul rightPsiCoefficientEquiv_mk_tmul rightPsiCoefficientEquiv_natural rightPsiCoefficientEquiv_natural_tmul rightPsiCoefficientEquiv_psiMinus rightPsiCoefficientEquiv_section rightPsiCompatibility_zero rightPsiHaarRatio_apply rightPsiInducingCoefficient rightPsiInducingCoefficient_kernel rightPsiStagesCoefficient rightPsiTensorBilinear rightPsiTensorEquiv rightPsiTensorEquiv_mk_tmul rightPsiTensorForward rightPsiZeroTarget rightPsiZeroTargetEquiv rightPsiZeroTargetEquiv_action rightPsiZeroTargetEquiv_natural rightPsi_scalar_eq twist_rightInducing_levi_zero
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

/-! ## Localized coinvariants of a tensor product -/

section Generic
end Generic
variable {F : LocalFieldPackage.{uF}}

/-! ## The kernel intersection -/

section Intersection
variable (k r : ℕ) (R : Type*) [CommRing R]

/-- An element of `A` as an element of `S ∩ ker plusProjection`. -/
def rightIdentityIntersectionToKernel (a : rightIdentityKernelIntersection k r R) :
    (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightIdStabilizer k r R).subtype :=
  ⟨⟨((a : rightIdentityInducing k r R) : rightStages k r R 1).val,
    (a : rightIdentityInducing k r R).property⟩,
    congrArg Subtype.val (MonoidHom.mem_ker.mp a.property)⟩

/-- The element of `A` over an element of `S ∩ ker plusProjection`. -/
def rightIdentityKernelToIntersection
    (n : (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightIdStabilizer k r R).subtype) :
    rightIdentityKernelIntersection k r R :=
  ⟨⟨⟨n.val.val, rightIdStabilizer_le_stages k r R n.val.property⟩, n.val.property⟩,
    MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp n.property))⟩

end Intersection
/-! ## The coefficient and its kernel quotient -/

section Coefficient
variable (T : F.TopologicalData) (k r : ℕ)
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (τ : Representation ℂ (mirabolic (r + 1) F.Carrier) W)
  (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)

/-- The orbit coefficient at the identity: `χ_R (τ ⊠ ρ)` through the inclusion of the
stabilizer into the right mixed subgroup. -/
abbrev rightIdentityCoefficient :
    Representation ℂ (rightIdStabilizer k r F.Carrier) (W ⊗[ℂ] V) :=
  (rightPsiInducingCoefficient T τ ρ).comp (rightIdentityInclusion k r F.Carrier)

/-- The coefficient restricted to `HP = S ∩ P`. -/
abbrev rightIdentityStagesCoefficient :
    Representation ℂ (rightIdentityInducing k r F.Carrier) (W ⊗[ℂ] V) :=
  (rightIdentityCoefficient T k r τ ρ).comp
    (Subgroup.subgroupOfEquivOfLe (rightIdStabilizer_le_stages k r F.Carrier)).toMonoidHom

/-- With a character trivial on `A`, the localized relations of the restricted
coefficient are the kernel relations of the right mixed coefficient. -/
theorem rightIdentity_relations_eq (η : rightIdentityKernelIntersection k r F.Carrier →* ℂˣ)
    (hη : ∀ a, η a = 1) :
    Jacquet.Localization.relations (rightIdentityStagesCoefficient T k r τ ρ)
        (rightIdentityKernelIntersection k r F.Carrier) η =
      Jacquet.relations (rightPsiInducingCoefficient T τ ρ)
        (rightPsiKernel (k + 1) (r + 1) F.Carrier) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨⟨a, v⟩, rfl⟩
    change rightIdentityStagesCoefficient T k r τ ρ a v - (η a : ℂ) • v ∈ _
    simp only [hη, Units.val_one, one_smul]
    exact Jacquet.sub_mem_relations _ _
      (rightIdentityKernelEquiv k r F.Carrier (rightIdentityIntersectionToKernel k r F.Carrier a)) v
  · apply Submodule.span_le.2
    rintro _ ⟨⟨g, v⟩, rfl⟩
    let n := (rightIdentityKernelEquiv k r F.Carrier).symm g
    let a := rightIdentityKernelToIntersection k r F.Carrier n
    have hg : rightIdentityInclusion k r F.Carrier ⟨n.val.val, n.val.property⟩ =
        (g : rightSubgroup (k + 1) (r + 1) F.Carrier) :=
      congrArg Subtype.val ((rightIdentityKernelEquiv k r F.Carrier).apply_symm_apply g)
    have key := Jacquet.Localization.sub_mem_relations (rightIdentityStagesCoefficient T k r τ ρ)
      (rightIdentityKernelIntersection k r F.Carrier) η a v
    simp only [hη, Units.val_one, one_smul] at key
    have hv : rightIdentityStagesCoefficient T k r τ ρ (a : rightIdentityInducing k r F.Carrier) v =
        rightPsiInducingCoefficient T τ ρ (g : rightSubgroup (k + 1) (r + 1) F.Carrier) v := by
      change rightPsiInducingCoefficient T τ ρ
        (rightIdentityInclusion k r F.Carrier ⟨n.val.val, n.val.property⟩) v = _
      rw [hg]
    rw [hv] at key
    exact key

/-- The localized coefficient quotient at the identity orbit is `τ_(V_(r+2)) ⊗ ρ`. -/
def rightIdentityCoefficientEquiv (η : rightIdentityKernelIntersection k r F.Carrier →* ℂˣ)
    (hη : ∀ a, η a = 1) :
    Jacquet.Localization.Coinvariants (rightIdentityStagesCoefficient T k r τ ρ)
        (rightIdentityKernelIntersection k r F.Carrier) η ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants τ (radical (r + 1) F.Carrier) 1 ⊗[ℂ] V :=
  (Submodule.quotEquivOfEq _ _ (rightIdentity_relations_eq T k r τ ρ η hη)).trans
    (rightPsiTensorEquiv T τ ρ)

@[simp] theorem rightIdentityCoefficientEquiv_mk_tmul
    (η : rightIdentityKernelIntersection k r F.Carrier →* ℂˣ) (hη : ∀ a, η a = 1) (w : W) (v : V) :
    rightIdentityCoefficientEquiv T k r τ ρ η hη
        (Jacquet.Localization.mk (rightIdentityStagesCoefficient T k r τ ρ)
          (rightIdentityKernelIntersection k r F.Carrier) η (w ⊗ₜ v)) =
      Jacquet.Localization.mk τ (radical (r + 1) F.Carrier) 1 w ⊗ₜ v := rfl

/-- The section `l = [[A, B], [0, D]]` acts on a pure tensor by
`χ_R(diag) [τ(diag(A, 1)) w] ⊗ ρ(D) v`. -/
theorem rightIdentityCoefficientEquiv_section
    (η : rightIdentityKernelIntersection k r F.Carrier →* ℂˣ) (hη : ∀ a, η a = 1)
    (l : (rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier)))
    (w : W) (v : V) :
    letI := T.topology
    rightIdentityCoefficientEquiv T k r τ ρ η hη
        (Jacquet.Localization.mk (rightIdentityStagesCoefficient T k r τ ρ)
          (rightIdentityKernelIntersection k r F.Carrier) η
          (rightIdentityStagesCoefficient T k r τ ρ
            (Induction.SplitKernelLocalization.subgroupSection
              ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap
                (rightStages k r F.Carrier 1))
              (rightIdentityInducing k r F.Carrier) (rightIdentityInducing_section_mem k r F.Carrier) l)
            (w ⊗ₜ v))) =
      ((T.rightCharacter (k + 1) (r + 1)).toMonoidHom
          (rightIdentityInclusion k r F.Carrier (rightIdentitySectionElement k r F.Carrier l)) : ℂ) •
        (Jacquet.Localization.mk τ (radical (r + 1) F.Carrier) 1
          (τ (levi (leftProjection (rightIdentityLevi k r F.Carrier l)).1) w) ⊗ₜ
            ρ (leftProjection (rightIdentityLevi k r F.Carrier l)).2.val v) := by
  let _ := T.topology
  have hx : rightInducingRepresentation τ ρ
      (rightIdentityInclusion k r F.Carrier (rightIdentitySectionElement k r F.Carrier l))
        (w ⊗ₜ v) =
      τ (levi (leftProjection (rightIdentityLevi k r F.Carrier l)).1) w ⊗ₜ
        ρ (leftProjection (rightIdentityLevi k r F.Carrier l)).2.val v := by
    rw [rightInducingRepresentation_tmul, ← rightCoefficient_one_apply,
      rightCoefficient_rightIdentitySectionElement]
  change rightIdentityCoefficientEquiv T k r τ ρ η hη
      (Jacquet.Localization.mk (rightIdentityStagesCoefficient T k r τ ρ)
        (rightIdentityKernelIntersection k r F.Carrier) η
        (((T.rightCharacter (k + 1) (r + 1)).toMonoidHom
            (rightIdentityInclusion k r F.Carrier (rightIdentitySectionElement k r F.Carrier l)) :
              ℂ) •
          rightInducingRepresentation τ ρ
            (rightIdentityInclusion k r F.Carrier (rightIdentitySectionElement k r F.Carrier l))
            (w ⊗ₜ v))) = _
  exact linearEquiv_map_smul_of_eq _ _ _ hx rfl

/-- The naturality of `rightIdentityCoefficientEquiv_natural` on a pure tensor. -/
theorem rightIdentityCoefficientEquiv_natural_tmul
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)}
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (f₁ : letI := T.topology; A ⟶ A') (f₂ : letI := T.topology; B ⟶ B')
    (t : (A ⊗[ℂ] B) →ₗ[ℂ] (A' ⊗[ℂ] B'))
    (ht : letI := T.topology; ∀ (w : A) (b : B),
      t (w ⊗ₜ b) = SmoothRep.hom f₁ w ⊗ₜ SmoothRep.hom f₂ b)
    (η : rightIdentityKernelIntersection k r F.Carrier →* ℂˣ) (hη : ∀ a, η a = 1)
    (w : letI := T.topology; A) (b : letI := T.topology; B) :
    letI := T.topology
    rightIdentityCoefficientEquiv T k r A'.representation B'.representation η hη
        (Jacquet.Localization.mk (rightIdentityStagesCoefficient T k r A'.representation
          B'.representation) (rightIdentityKernelIntersection k r F.Carrier) η (t (w ⊗ₜ b))) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T (r + 1)).map f₁)).toLinearMap
        (SmoothRep.hom f₂).toLinearMap
        (rightIdentityCoefficientEquiv T k r A.representation B.representation η hη
          (Jacquet.Localization.mk (rightIdentityStagesCoefficient T k r A.representation
            B.representation) (rightIdentityKernelIntersection k r F.Carrier) η (w ⊗ₜ b))) := by
  let _ := T.topology
  refine (congrArg (fun x => rightIdentityCoefficientEquiv T k r A'.representation
      B'.representation η hη (Jacquet.Localization.mk _ _ η x)) (ht w b)).trans ?_
  refine (rightIdentityCoefficientEquiv_mk_tmul T k r A'.representation B'.representation η hη
    _ _).trans ?_
  refine (congrArg (fun x : Jacquet.Localization.Coinvariants A'.representation
      (radical (r + 1) F.Carrier) 1 => x ⊗ₜ[ℂ] SmoothRep.hom f₂ b)
    (Mirabolic.psiMinus_map_quotient T (r + 1) f₁ w).symm).trans ?_
  exact (TensorProduct.map_tmul (SmoothRep.hom ((Mirabolic.psiMinus T (r + 1)).map f₁)).toLinearMap
    (SmoothRep.hom f₂).toLinearMap (Mirabolic.psiMinusQuotient T (r + 1) A w) b).symm

/-- The coefficient identification is natural for linear maps acting by `f₁ ⊗ f₂` on
pure tensors. -/
theorem rightIdentityCoefficientEquiv_natural
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)}
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (f₁ : letI := T.topology; A ⟶ A') (f₂ : letI := T.topology; B ⟶ B')
    (t : (A ⊗[ℂ] B) →ₗ[ℂ] (A' ⊗[ℂ] B'))
    (ht : letI := T.topology; ∀ (w : A) (b : B),
      t (w ⊗ₜ b) = SmoothRep.hom f₁ w ⊗ₜ SmoothRep.hom f₂ b)
    (η : rightIdentityKernelIntersection k r F.Carrier →* ℂˣ) (hη : ∀ a, η a = 1)
    (x : A ⊗[ℂ] B) :
    letI := T.topology
    rightIdentityCoefficientEquiv T k r A'.representation B'.representation η hη
        (Jacquet.Localization.mk (rightIdentityStagesCoefficient T k r A'.representation
          B'.representation) (rightIdentityKernelIntersection k r F.Carrier) η (t x)) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T (r + 1)).map f₁)).toLinearMap
        (SmoothRep.hom f₂).toLinearMap
        (rightIdentityCoefficientEquiv T k r A.representation B.representation η hη
          (Jacquet.Localization.mk (rightIdentityStagesCoefficient T k r A.representation
            B.representation) (rightIdentityKernelIntersection k r F.Carrier) η x)) := by
  let _ := T.topology
  induction x using TensorProduct.inductionOn with
  | tmul w b => exact rightIdentityCoefficientEquiv_natural_tmul T k r f₁ f₂ t ht η hη w b
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (LinearMap.map_add (TensorProduct.map
      (SmoothRep.hom ((Mirabolic.psiMinus T (r + 1)).map f₁)).toLinearMap
      (SmoothRep.hom f₂).toLinearMap) _ _).symm

end Coefficient
/-! ## The target action -/

section Target
variable (T : F.TopologicalData) (k r : ℕ)

/-- `Ψ⁻τ(A) ⊗ ρ(D)` on the class of `w ⊗ b`. -/
theorem rightIdentity_psiMinus_tmul
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (g : GeneralLinear (r + 1) F.Carrier) (d : mirabolic k F.Carrier) (w : A) (b : B) :
    letI := T.topology
    TensorProduct.map (((Mirabolic.psiMinus T (r + 1)).obj A).representation g)
        (((generalLinearRestriction T k).obj B).representation d)
        (Jacquet.Localization.mk A.representation (radical (r + 1) F.Carrier) 1 w ⊗ₜ b) =
      (Mirabolic.psiMinusCharacter T (r + 1) g : ℂ) •
        (Jacquet.Localization.mk A.representation (radical (r + 1) F.Carrier) 1
          (A.representation (levi g) w) ⊗ₜ B.representation d.val b) := by
  let _ := T.topology
  exact (TensorProduct.map_tmul _ _ (Mirabolic.psiMinusQuotient T (r + 1) A w) b).trans
    ((congrArg (· ⊗ₜ[ℂ] _) (Mirabolic.psiMinus_action T (r + 1) A g w)).trans
      (TensorProduct.smul_tmul' _ _ _).symm)

end Target
/-! ## The scalars -/

section Scalar
open Langlands.Induction
open Langlands.QuotientIntegration
/-- `ν(l)^(-1/2) · |det D| · χ_R(diag) = χ_L(l) · ν(A)^(-1/2)` at `l = [[A, B], [0, D]]`. -/
theorem rightIdentity_scalar_eq (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    haveI := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
    ∀ [MeasurableSpace (rightIdentityRetraction k r F.Carrier).ker]
      [BorelSpace (rightIdentityRetraction k r F.Carrier).ker]
      [LocallyCompactSpace (rightIdentityRetraction k r F.Carrier).ker]
      [MeasurableSpace ((rightIdentityInducing k r F.Carrier).comap
        (rightIdentityRetraction k r F.Carrier).ker.subtype)]
      [BorelSpace ((rightIdentityInducing k r F.Carrier).comap
        (rightIdentityRetraction k r F.Carrier).ker.subtype)],
      (((Mirabolic.phiMinusCharacter T (k + r + 1)).comp (Subgroup.subtype
          ((rightStages k r F.Carrier 1).comap
            (plusSuccessor (n := k + r + 1) (F := F.Carrier))))) l : ℂ) *
          (Jacquet.complexCharacter (splitKernelHaarRatio (rightIdentityRetraction k r F.Carrier)
            ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap
              (rightStages k r F.Carrier 1))
            (rightIdentityInducing k r F.Carrier) (rightIdentityInducing_section_mem k r F.Carrier)
            ((rightIdStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val)) l : ℂ) *
        ((T.rightCharacter (k + 1) (r + 1)).toMonoidHom
          (rightIdentityInclusion k r F.Carrier (rightIdentitySectionElement k r F.Carrier l)) : ℂ) =
      ((T.leftCharacter (r + 1) k).toMonoidHom (rightIdentityLevi k r F.Carrier l) : ℂ) *
        (Mirabolic.psiMinusCharacter T (r + 1)
          (leftProjection (rightIdentityLevi k r F.Carrier l)).1 : ℂ) := by
  let _ := T.topology
  let _ := T.fieldT2
  let _ := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  have _ := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
  intro _ _ _ _ _
  rw [LocalFieldPackage.TopologicalData.rightCharacter_apply, ← rightCoefficient_one_apply,
    rightCoefficient_rightIdentitySectionElement, LocalFieldPackage.TopologicalData.rightLeviCharacter_apply,
    LocalFieldPackage.TopologicalData.leftCharacter_apply, LocalFieldPackage.TopologicalData.leftLeviCharacter_apply,
    Jacquet.complexCharacter_apply, rightIdentityHaarRatio_apply T k r l]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_realPowerCharacter, projection_levi]
  rw [determinantNorm_rightIdentity T k r l]
  exact rightPsi_scalar_identity_complex _ _ (k + 1) (r + 1)

end Scalar
end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
