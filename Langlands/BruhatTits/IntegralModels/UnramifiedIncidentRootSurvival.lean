import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionStatement
import Langlands.BruhatTits.IntegralModels.IntegralTorusRootData
import Langlands.BruhatTits.IntegralModels.IntegralRootPerfectLifting
import Langlands.BruhatTits.IntegralModels.IntegralRootDoubleComparison
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroRoots
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion

/-! # Incident-root survival in a supplied upper unramified model -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

namespace IntegralSplitTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    {N : IntegralModel R K G} [Smooth N.group.X.hom]
    (A : IntegralSplitTorusData N i)

/-- An ambient integral section whose generic point lies in the original
root group factors through the actual integral root model. -/
theorem exists_rootModel_section_of_generic_mem (a : characterLattice S) (ha : a ≠ 0)
    (z : N.integralSections) (hz : N.integralPointMap z ∈ rootGroupPoints i a) :
    ∃ v : (A.rootModel a ha).integralSections,
      rationalPoints.map (A.rootModelMap a ha).hom v = z := by
  have hmem : N.integralPointMap z ∈
      (A.rootModel a ha).integralPoints.map (rationalPoints.map (A.rootInclusion a ha)) := by
    rw [A.rootModel_integralPoints_eq a ha]
    exact ⟨⟨z, rfl⟩, hz⟩
  obtain ⟨p, ⟨v, rfl⟩, hp⟩ := hmem
  refine ⟨v, N.integralPointMap_injective ?_⟩
  rw [(A.rootModelMap a ha).integralPointMap_naturality]
  exact hp

end IntegralSplitTorusData

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (x : C.Apartment)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hD : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))

private instance incidentSurvival_neutralSmooth : Smooth D.neutral.group.X.hom :=
  D.neutral_smooth

include hD

/-- The positive-reduction statement on a singleton controls every ambient
integral section whose generic point lies in the root group. -/
theorem unramified_singleton_reductiveReduction_eq_one_iff
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (A : IntegralSplitTorusData D.neutral C.i)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (a : relativeRoots C.i) (z : D.neutral.integralSections)
    (hz : D.neutral.integralPointMap z ∈ rootGroupPoints C.i a.val) :
    Q.reductiveReduction z = 1 ↔
      D.neutral.integralPointMap z ∈ C.apartment.filtrationPlus x a 0 := by
  obtain ⟨v, hv⟩ := A.exists_rootModel_section_of_generic_mem a a.2.1 z hz
  have hp := hpositive F G C E {x} (Set.singleton_nonempty x)
    (by intro f; simpa only [Set.image_singleton] using (show BddAbove {f x} from bddAbove_singleton))
    D hD A Q hQ a v
  rw [← (A.rootModelMap a a.2.1).integralPointMap_naturality, hv] at hp
  calc
    Q.reductiveReduction z = 1 ↔ D.neutral.reduction z ∈ Q.radicalPoints := by
      rw [← MonoidHom.mem_ker, Q.ker_reductiveReduction hQ.2.1]
      rfl
    _ ↔ D.neutral.integralPointMap z ∈ C.apartment.filtrationPlus x a 0 := by
      simpa only [Set.mem_singleton_iff, exists_eq_left] using hp

/-- An actual zero-depth root point outside strict depth times the complete
KP doubled-root group forces the same character to survive in the quotient. -/
theorem unramified_quotient_root_of_depth_boundary
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (T : IntegralTorusData D C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (a : relativeRoots C.i) (g : rationalPoints G)
    (hg : g ∈ C.apartment.filtration x a 0)
    (hout : g ∉ (C.apartment.filtrationPlus x a 0 : Set (rationalPoints G)) *
      (doubleRootGroupPoints C.i a.val : Set (rationalPoints G))) :
    T.characterSpecialization hT a.val ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection) := by
  let : Smooth G.X.hom := C.isConnectedReductive.smooth
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  let : Mono C.i.hom.hom.left := mono_of_isMaximalSplitTorus C.isMaximalSplitTorus
  have hroot := relativeRootSystem (inertiaFixedField F) G C.isConnectedReductive
    C.S C.i C.isMaximalSplitTorus
  have hgroot := C.apartment.filtration_le_rootGroupPoints x a 0 hg
  have hgint : g ∈ D.neutral.integralPoints := by
    have hi : g ∈ rootGroupPoints C.i a.val ⊓
        (E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x})) := by
      rw [rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E {x} a,
        C.apartment.rootFixer_singleton]
      exact hg
    rw [hD]
    exact hi.2
  obtain ⟨z, hz⟩ := hgint
  have hzroot : D.neutral.integralPointMap z ∈ rootGroupPoints C.i a.val := hz.symm ▸ hgroot
  by_contra habsent
  have hcompare := T.quotient_subgroup_eq_double_of_absent_root hT Q hQ hroot a.property habsent
  have hzred := T.quotient_reduction_mem_rootFunctor hT Q a.val a.2.1 z hzroot
  rw [hcompare] at hzred
  have h2a0 : 2 • a.val ≠ 0 :=
    C.isMaximalSplitTorus.1.1.nsmul_ne_zero a.2.1 (by decide)
  obtain ⟨y, hyroot, hyred⟩ :=
    T.exists_integral_root_quotient_lift_of_perfectResidue hT Q hQ
      (2 • a.val) h2a0 (Q.reductiveReduction z) hzred
  have hydouble : D.neutral.integralPointMap y ∈ doubleRootGroupPoints C.i a.val := by
    rw [← rootGroupPoints_double_eq_doubleRootGroupPoints C.i
      C.isMaximalSplitTorus.1.1 hroot a.property]
    exact hyroot
  have hyfirst : D.neutral.integralPointMap y ∈ rootGroupPoints C.i a.val :=
    RelativeRoot.double_subgroup_le C.i a.val _ hyroot
  have hdiffroot : D.neutral.integralPointMap (z * y⁻¹) ∈ rootGroupPoints C.i a.val := by
    rw [map_mul, map_inv]
    exact (rootGroupPoints C.i a.val).mul_mem hzroot
      ((rootGroupPoints C.i a.val).inv_mem hyfirst)
  have hdiffred : Q.reductiveReduction (z * y⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change Q.reductiveReduction z *
      (rationalPoints.map Q.projection (D.neutral.reduction y))⁻¹ = 1
    rw [hyred, mul_inv_cancel]
  have hdiffplus := (unramified_singleton_reductiveReduction_eq_one_iff
    C E x D hD hpositive (T.toIntegralSplitTorusData hT) Q hQ a
      (z * y⁻¹) hdiffroot).mp hdiffred
  apply hout
  refine ⟨D.neutral.integralPointMap (z * y⁻¹), hdiffplus,
    D.neutral.integralPointMap y, hydouble, ?_⟩
  change D.neutral.integralPointMap (z * y⁻¹) * D.neutral.integralPointMap y = g
  rw [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one, hz]

/-- The actual quotient root supplied by a depth-boundary witness, retaining
exactly the canonical specialization of the original character. -/
def unramifiedDepthBoundaryQuotientRoot
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (T : IntegralTorusData D C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (a : relativeRoots C.i) (g : rationalPoints G)
    (hg : g ∈ C.apartment.filtration x a 0)
    (hout : g ∉ (C.apartment.filtrationPlus x a 0 : Set (rationalPoints G)) *
      (doubleRootGroupPoints C.i a.val : Set (rationalPoints G))) :
    relativeRoots (T.specialFibreInclusion ≫ Q.projection) :=
  ⟨T.characterSpecialization hT a.val,
    unramified_quotient_root_of_depth_boundary C E x D hD hpositive T hT Q hQ a g hg hout⟩

@[simp] theorem unramifiedDepthBoundaryQuotientRoot_character
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (T : IntegralTorusData D C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (a : relativeRoots C.i) (g : rationalPoints G)
    (hg : g ∈ C.apartment.filtration x a 0)
    (hout : g ∉ (C.apartment.filtrationPlus x a 0 : Set (rationalPoints G)) *
      (doubleRootGroupPoints C.i a.val : Set (rationalPoints G))) :
    (unramifiedDepthBoundaryQuotientRoot C E x D hD hpositive T hT Q hQ a g hg hout).val =
      T.characterSpecialization hT a.val := rfl

end Unramified

end Langlands.BruhatTits.IntegralModels
