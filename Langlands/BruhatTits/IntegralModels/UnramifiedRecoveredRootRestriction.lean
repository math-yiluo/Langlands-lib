import Langlands.BruhatTits.IntegralModels.UnramifiedResidueArithmetic
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorusResidue
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorusGeneric
import Langlands.BruhatTits.IntegralModels.RecoveredSpecialFibreQuotient
import Langlands.BruhatTits.IntegralModels.IntegralTorusRootRestriction
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentQuotientRoots
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit

/-! # Nonzero restriction of incident roots in recovered apartment models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 120000
set_option maxRecDepth 2500

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels
namespace RecoveredApartmentFixerModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  {Ω : Set D.Apartment}
  (M : RecoveredApartmentFixerModels D Ω)
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} {f : S ⟶ T}
  (hiS : IsMaximalSplitTorus iS)
  (hf : CommGroupScheme.groupHom f ≫ iT = iS)
  (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

local instance recoveredRootIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance recoveredRootIntegerTower : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance recoveredRootIntegerLocalHom : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

private instance recoveredRootExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- The actual quotient on the recovered upper special fibre, whose target
is literally the residue coefficient pullback of the supplied lower quotient. -/
def recoveredQuotient (Q : SpecialFibreQuotientData M.lower) :
    SpecialFibreQuotientData M.upper :=
  Q.baseChangeSpecialFibreIso (fixedFieldIntegers F) (inertiaFixedField F)
    M.recovery.neutralResidueBaseChangeIso

/-- Full reductive-quotient validity survives the actual recovery. -/
theorem recoveredQuotient_isReductiveQuotient
    (Q : SpecialFibreQuotientData M.lower) (hQ : Q.IsReductiveQuotient) :
    (M.recoveredQuotient Q).IsReductiveQuotient := by
  let := unramifiedResidue_isAlgebraic (F := F)
  let := unramifiedResidue_isSeparable (F := F)
  exact Q.isReductiveQuotient_baseChangeSpecialFibreIso
    (fixedFieldIntegers F) (inertiaFixedField F)
    M.recovery.neutralResidueBaseChangeIso hQ

include hG in
/-- The supplied lower apartment torus remains maximal split in the actual
lower reductive quotient. -/
theorem lowerApartmentTorus_quotient_isMaximalSplitTorus
    (Q : SpecialFibreQuotientData M.lower) (hQ : Q.IsReductiveQuotient) :
    IsMaximalSplitTorus
      ((M.lowerApartmentTorus C hDC hiS hf).specialFibreInclusion ≫ Q.projection) := by
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : IsAffineHom M.lower.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd M.lower.neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  let : LocallyOfFiniteType M.lower.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd M.lower.neutral.group.X.hom
        (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  exact (IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel
    Q.radicalInclusion hQ.1.isClosedSubgroup hQ.1.isUnipotent Q.projection hQ.2.1
      (M.lowerApartmentTorus C hDC hiS hf).specialFibreInclusion).mpr
    (M.lowerApartmentTorus_satisfiesTorusClause C hDC hiS hf hG).2

/-- The prescribed upper apartment torus remains maximal in any supplied
valid upper reductive quotient. -/
theorem upperNeutralApartmentTorus_quotient_isMaximalTorus
    (Q : SpecialFibreQuotientData M.upper) (hQ : Q.IsReductiveQuotient) :
    IsMaximalTorus
      ((M.upperNeutralApartmentTorus hG hiT C hDC).specialFibreInclusion ≫ Q.projection) := by
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : IsAffineHom M.upper.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd M.upper.neutral.group.X.hom
      (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
    infer_instance
  let : LocallyOfFiniteType M.upper.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd M.upper.neutral.group.X.hom
        (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
    infer_instance
  exact (M.upperNeutralApartmentTorus_specialInclusion_isMaximalTorus C hDC hG hiT).comp_of_perfect_field_unipotent_kernel
      Q.radicalInclusion hQ.1.isClosedSubgroup
      hQ.1.isUnipotent Q.projection hQ.2.1

/-- The actual recovered torus map and projection satisfy the exact lower
residue coefficient square. -/
theorem apartmentTorusMap_comp_recoveredQuotient
    (Q : SpecialFibreQuotientData M.lower) :
    (M.apartmentTorusSpecialFibreIso C hDC hiS hf).hom ≫
      (GroupScheme.baseChange
        (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
          (CommGroupScheme.groupHom (M.apartmentTorusMap C hDC hiS hf hG hiT)) ≫
      (M.upperNeutralApartmentTorus hG hiT C hDC).specialFibreInclusion ≫
      (M.recoveredQuotient Q).projection =
    (GroupScheme.baseChange
      (algebraBaseMap (IsLocalRing.ResidueField ↥𝒪[F])
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map
      ((M.lowerApartmentTorus C hDC hiS hf).specialFibreInclusion ≫ Q.projection) := by
  have hsquare := congrArg (fun g => g ≫ (M.recoveredQuotient Q).projection)
    (M.apartmentTorusMap_specialFibre_comp_inclusion C hDC hiS hf hG hiT)
  have hprojection := Q.baseChangeSpecialFibreIso_hom_projection
    (fixedFieldIntegers F) (inertiaFixedField F) M.recovery.neutralResidueBaseChangeIso
  simpa only [Category.assoc, recoveredQuotient, hprojection,
    Functor.map_comp] using hsquare

include C hDC hiS hf hG hiT in
/-- An ordinary incident root has nonzero restriction to the coefficient
pullback of the prescribed lower maximal split torus. Global neutral-fixer
equality and positive reduction remain explicit hypotheses. -/
theorem incident_root_restrict_ne_zero
    (Q : SpecialFibreQuotientData M.lower) (hQ : Q.IsReductiveQuotient)
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (x : D.Apartment)
    (hD : M.upper.neutral.integralPoints =
      E.zeroPoints ⊓ D.pointwiseFixer (D.apartmentMap '' {x}))
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (a : relativeRoots
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.affineRoots) (hx : ψ x = 0)
    (hlin : ψ.linear = rootForm
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) a) :
    (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f ≫ a.val ≠ 0 := by
  let A := M.baseChangedLowerApartmentTorus C hDC hiS hf
  let B := (M.upperNeutralApartmentTorus hG hiT C hDC).toIntegralTorusData
  let ρ := M.apartmentTorusMap C hDC hiS hf hG hiT
  let Qup := M.recoveredQuotient Q
  have hQup : Qup.IsReductiveQuotient := M.recoveredQuotient_isReductiveQuotient Q hQ
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have hχ : B.characterSpecialization
      (M.upperNeutralApartmentTorus hG hiT C hDC).isSplit a.val ∈
        roots (B.specialFibreInclusion ≫ Qup.projection) :=
    unramified_quotient_root_of_incidentAffineRoot
      (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
      E x M.upper hD hpositive B
      (M.upperNeutralApartmentTorus hG hiT C hDC).isSplit Qup hQup a hψ hx hlin
  have hne := IntegralTorusData.generic_restriction_ne_zero_of_finite_residue_root
    (A := A) (B := B)
    (M.baseChangedLowerApartmentTorus_isSplit C hDC hiS hf)
    (M.upperNeutralApartmentTorus hG hiT C hDC).isSplit ρ a.val hQ.2.2
    ((M.lowerApartmentTorus C hDC hiS hf).specialFibreInclusion ≫ Q.projection)
    (M.lowerApartmentTorus_quotient_isMaximalSplitTorus C hDC hiS hf hG Q hQ)
    (M.apartmentTorusSpecialFibreIso C hDC hiS hf)
    (B.specialFibreInclusion ≫ Qup.projection)
    (M.upperNeutralApartmentTorus_quotient_isMaximalTorus C hDC hG hiT Qup hQup)
    (M.apartmentTorusMap_comp_recoveredQuotient C hDC hiS hf hG hiT Q) hχ
  change (M.baseChangedLowerApartmentTorus C hDC hiS hf).genericFibreMap
    (M.upperNeutralApartmentTorus hG hiT C hDC).toIntegralTorusData
    (M.apartmentTorusMap C hDC hiS hf hG hiT) ≫ a.val ≠ 0 at hne
  rw [M.genericFibreMap_apartmentTorusMap C hDC hiS hf hG hiT] at hne
  exact hne

end RecoveredApartmentFixerModels
end Langlands.BruhatTits.IntegralModels
