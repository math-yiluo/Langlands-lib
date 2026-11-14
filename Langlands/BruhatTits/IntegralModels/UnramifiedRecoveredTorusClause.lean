import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorus
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredApartmentRoots
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerResidueRoots
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Torus.HenselianSplitRank

/-! # Torus clauses in recovered apartment fixer models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- A closed split integral torus with maximal split generic fibre satisfies
the full torus clause over a Henselian local domain. -/
theorem IntegralTorusData.satisfiesTorusClause_of_generic
    {R K : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (A : IntegralTorusData D S i) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hA : A.IsClosedSplit) :
    A.SatisfiesTorusClause := by
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  refine ⟨hA, ?_⟩
  have hgeneric : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj A.torus)
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map A.inclusion) := by
    apply (IsMaximalSplitTorus.comp_iso_iff _ D.neutral.genericIso).mp
    rw [A.generic_comm]
    exact IsMaximalSplitTorus.iso_comp
      (T' := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj A.torus)
      A.genericIso hi
  exact isMaximalSplitTorus_residue_of_generic
    (IsLocalRing.residue_surjective : Function.Surjective
      (algebraMap R (IsLocalRing.ResidueField R)))
    D.neutral.group (hG.of_iso D.neutral.genericIso)
    A.torus hA.1 A.inclusion hA.2 hgeneric

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

section Lower

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} {f : S ⟶ T}
  (hiS : IsMaximalSplitTorus iS)
  (hf : CommGroupScheme.groupHom f ≫ iT = iS)

/-- The prescribed lower maximal split torus extends as a closed split torus
in the recovered lower neutral model. -/
def lowerApartmentTorus : IntegralTorusData M.lower S iS :=
  integralTorusOfFullRecovery D C hiS hf hDC
    M.lower M.upper M.recovery Ω M.full_integralPoints

theorem lowerApartmentTorus_isClosedSplit :
    (M.lowerApartmentTorus C hDC hiS hf).IsClosedSplit :=
  integralTorusOfFullRecovery_isClosedSplit D C hiS hf hDC
    M.lower M.upper M.recovery Ω M.full_integralPoints

/-- The recovered lower torus satisfies the complete integral torus clause,
including maximal splitness in the neutral special fibre. -/
theorem lowerApartmentTorus_satisfiesTorusClause (hG : IsConnectedReductive G) :
    (M.lowerApartmentTorus C hDC hiS hf).SatisfiesTorusClause := by
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  exact (M.lowerApartmentTorus C hDC hiS hf).satisfiesTorusClause_of_generic
    hG hiS (M.lowerApartmentTorus_isClosedSplit C hDC hiS hf)

end Lower

section Upper

variable (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

/-- The prescribed upper full-model torus is maximal in the full special fibre. -/
theorem upperFullApartmentTorus_specialInclusion_isMaximalTorus :
    IsMaximalTorus
      (M.upperFullApartmentTorus hG hiT C hDC).specialFibreInclusion := by
  let : Smooth M.upper.full.group.X.hom := M.upper.full_smooth
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  exact (M.upperFullApartmentTorus hG hiT C hDC).specialInclusion_isMaximalTorus
    hG.baseChange_of_algebraicExtension hiT
    (M.upperFullApartmentTorus_isClosedSubgroup hG hiT C hDC)

/-- The same prescribed upper torus is maximal in the neutral special fibre. -/
theorem upperNeutralApartmentTorus_specialInclusion_isMaximalTorus :
    IsMaximalTorus
      (M.upperNeutralApartmentTorus hG hiT C hDC).specialFibreInclusion := by
  let : Smooth M.upper.neutral.group.X.hom := M.upper.neutral_smooth
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  exact (M.upperNeutralApartmentTorus hG hiT C hDC).specialInclusion_isMaximalTorus
    hG.baseChange_of_algebraicExtension hiT
    (M.upperNeutralApartmentTorus_isClosedSubgroup hG hiT C hDC)

end Upper
end RecoveredApartmentFixerModels
end Langlands.BruhatTits.IntegralModels
