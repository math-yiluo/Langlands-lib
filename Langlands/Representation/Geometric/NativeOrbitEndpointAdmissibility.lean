import Langlands.Representation.Geometric.StabilizerQuotientAdmissibility
import Langlands.Representation.Geometric.RepresentedGeometricLemmaCompactHaar
import Langlands.Representation.Induction.CoefficientSplitStagesAmbient
import Langlands.Representation.Induction.CompactQuotientProof

/-! Native endpoint admissibility for the original compact orbit comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 20000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

universe u uR uV

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance nativeEndpointPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}
  {B : Type uR} [CommRing B] [Algebra ℂ B]
  {V : Type uV} [AddCommGroup V] [Module B V]

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "π" => IsSemidirectDecomposition.projection dQ
local notation "s" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le dQ)
local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "S" => D.compactComparisonSaturation
local notation "K" => Subgroup.comap s S
local notation "hSI" => D.compactComparisonSaturation_section_mem_stabilizer
local notation "NQH" => Subgroup.comap (Subgroup.subtype H) (MonoidHom.ker (π))
local notation "rS" => splitStagesRetraction π s
  (fun m => IsSemidirectDecomposition.projection_levi dQ m)
  S D.projectionKernel_le_compactComparisonSaturation
local notation "sS" => MonoidHom.subgroupComap s S
local notation "HS" => Subgroup.subgroupOf H S
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rS)) HS
local notation "hHS" => IsClosed.preimage
  (continuous_subtype_val : Continuous (Subgroup.subtype S))
  (Geometric.isClosed_orbitStabilizer (pointImage p) (pointImage q) z⁻¹
    (isClosed_pointImage p hp.isClosedSubgroup))

local instance nativeEndpointKernelLocallyCompact : LocallyCompactSpace (MonoidHom.ker rS) :=
  representedNestedKernelLocallyCompactSpace q lQ rQ hq hrQ hmulQ
    S D.projectionKernel_le_compactComparisonSaturation
local instance nativeEndpointKernelMeasurable : MeasurableSpace (MonoidHom.ker rS) := borel _
local instance nativeEndpointKernelBorel : BorelSpace (MonoidHom.ker rS) := ⟨rfl⟩
local instance nativeEndpointIntersectionMeasurable : MeasurableSpace I := borel _
local instance nativeEndpointIntersectionBorel : BorelSpace I := ⟨rfl⟩

/-- The exact original normal quotient and section action at the endpoint of
native induction in stages, before its scalar Haar twist. -/
def compactComparisonNativeSectionCoefficient (ρ : Representation B H V) :
    Representation B K (Jacquet.Coinvariants ρ NQH) :=
  (ρ.toCoinvariants NQH).comp (splitStagesInducingSection s S H hSI)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [Algebra ℂ B] in
/-- Removing the nested target subgroup identifies the action with the
original intersection quotient without changing its native carrier. -/
theorem compactComparisonNativeSectionCoefficient_eq (ρ : Representation B H V) :
    D.compactComparisonNativeSectionCoefficient ρ =
      (D.targetStabilizerCoinvariantRepresentation ρ).comp
        D.compactComparisonLeviEquiv.toMonoidHom := rfl

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The actual nested section sends the same original ambient point into the
same full orbit stabilizer as the represented intersection section. -/
theorem compactComparisonNativeSection_eq :
    splitStagesInducingSection s S H hSI =
      D.targetParabolicPointsToStabilizer.comp
        D.compactComparisonLeviEquiv.toMonoidHom := rfl

/-- The exact relative-integral Haar character, transported back to the
original nested stages endpoint and embedded as constant B coefficients. -/
def compactComparisonNativeHaarCharacter : SmoothCharacter B K where
  toMonoidHom :=
    (Units.map (RingHom.toMonoidHom (algebraMap ℂ B))).comp
      (D.compactIntegralHaarCharacter.comp D.compactComparisonLeviEquiv.toMonoidHom)
  isOpen_ker := by
    apply Subgroup.isOpen_mono
      (H₁ := (D.compactIntegralHaarCharacter.comp
        D.compactComparisonLeviEquiv.toMonoidHom).ker)
    · intro x hx
      change (Units.map (RingHom.toMonoidHom (algebraMap ℂ B)))
        (D.compactIntegralHaarCharacter (D.compactComparisonLeviEquiv x)) = 1
      change D.compactIntegralHaarCharacter (D.compactComparisonLeviEquiv x) = 1 at hx
      rw [hx, map_one]
    · exact D.isOpen_ker_compactIntegralHaarCharacter.preimage
        D.compactComparisonLeviEquiv.continuous

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The transported coefficient character is exactly the constant image of
the original nested relative-integral Haar ratio used by native stages. -/
theorem compactComparisonNativeHaarCharacter_eq_nested :
    D.compactComparisonNativeHaarCharacter.toMonoidHom =
      (Units.map (RingHom.toMonoidHom (algebraMap ℂ B))).comp
        (Jacquet.complexCharacter (splitKernelHaarRatio rS sS HS hSI hHS)) := by
  apply MonoidHom.ext
  intro x
  exact congrArg
    ((Units.map (RingHom.toMonoidHom (algebraMap ℂ B))).comp
      (Jacquet.complexCharacter (splitKernelHaarRatio rS sS HS hSI hHS)))
    (D.compactComparisonLeviEquiv.symm_apply_apply x)

/-- The original native stabilizer-kernel quotient, acted on by the original
section and multiplied by the exact relative-integral Haar scalar. -/
def compactComparisonNativeCoefficient (ρ : Representation B H V) :
    Representation B K (Jacquet.Coinvariants ρ NQH) :=
  Langlands.twist D.compactComparisonNativeHaarCharacter.toMonoidHom
    (D.compactComparisonNativeSectionCoefficient ρ)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The stages endpoint has admissible native coefficients whenever its
actual intersection quotient does. -/
theorem compactComparisonNativeCoefficient_isAdmissible [IsNoetherianRing B]
    (ρ : Representation B H V)
    (hρ : IsAdmissible (D.targetStabilizerCoinvariantRepresentation ρ)) :
    IsAdmissible (D.compactComparisonNativeCoefficient ρ) := by
  apply (isAdmissible_twist_iff _ _
    D.compactComparisonNativeHaarCharacter.isOpen_ker).mpr
  rw [D.compactComparisonNativeSectionCoefficient_eq]
  exact isAdmissible_comp_continuousMulEquiv _ D.compactComparisonLeviEquiv hρ

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Compactness of the actual endpoint quotient and admissibility of its
native coefficients imply admissibility of the compactly induced endpoint. -/
theorem compactComparisonNativeCompactInduced_isAdmissible [IsNoetherianRing B]
    [CompactSpace (LeftQuotient K)]
    (ρ : Representation B H V)
    (hρ : IsAdmissible (D.targetStabilizerCoinvariantRepresentation ρ)) :
    IsAdmissible (compactInduced K (D.compactComparisonNativeCoefficient ρ)) :=
  isAdmissible_of_injective (compactInclusion K _)
    (compactInclusion_bijective_of_compactSpace K _).injective
    (smoothInduced_isAdmissible_of_compactSpace K _
      (D.compactComparisonNativeCoefficient_isAdmissible ρ hρ))

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Plancherel.RationalNormalized

set_option backward.isDefEq.respectTransparency.types true

open GroupScheme Aubert.General.RepresentedParabolic Induction
open Langlands.AlgebraicGeometry.PointTopology

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance universalNativeEndpointAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance universalNativeEndpointPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance universalNativeEndpointFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : N ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hmul : IsIso (subgroupMultiplication l n))
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {Q L U : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l n r.isCompatible.parabolic hn
    r.isCompatible.levi hmul q lQ nQ hq hnQ hlQ hmulQ z)
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance universalNativeEndpointRegularCommRing : CommRing (RegularAlgebra r) :=
  Subalgebra.toCommRing _
local instance universalNativeEndpointRegularAlgebra : Algebra ℂ (RegularAlgebra r) :=
  Subalgebra.algebra _
local instance universalNativeEndpointTensorAddCommGroup :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup
local instance universalNativeEndpointTensorModule :
    Module (RegularAlgebra r) (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.leftModule

/-- The original positive-normalized universal inducing action restricted
to the full actual orbit stabilizer, with its coefficient instances pinned. -/
def universalNativeEndpointStabilizerCoefficient
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :
    Representation (RegularAlgebra r)
      (Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹)
      (RegularAlgebra r ⊗[ℂ] E) :=
  (inducingRepresentation r h hU σ).comp
    (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹)

/-- The original native endpoint coefficient, including its exact Haar scalar. -/
def universalNativeEndpointCoefficient
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  D.compactComparisonNativeCoefficient
    (B := RegularAlgebra r) (V := RegularAlgebra r ⊗[ℂ] E)
    (universalNativeEndpointStabilizerCoefficient r h hU σ)

/-- The exact native coefficient at the actual universal orbit endpoint,
including its original Haar scalar, is admissible over the same complete B. -/
theorem universalCompactComparisonNativeCoefficient_isAdmissible
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsAdmissible σ) (hcusp : IsSupercuspidal r σ) :
    IsAdmissible (R := RegularAlgebra r)
      (universalNativeEndpointCoefficient r hn hmul h hU D σ) := by
  let := regularAlgebra_isNoetherianRing r
  exact D.compactComparisonNativeCoefficient_isAdmissible
    (B := RegularAlgebra r) (V := RegularAlgebra r ⊗[ℂ] E) _
    (universalTargetStabilizerCoinvariant_isAdmissible r hn hmul h hU D σ hσ hcusp)

local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ nQ hq.isClosedSubgroup hnQ hmulQ
local notation "s" => Subgroup.inclusion (Aubert.General.IsSemidirectDecomposition.levi_le dQ)
local notation "K" => Subgroup.comap s D.compactComparisonSaturation

set_option maxHeartbeats 80000 in
/-- Compactness of the original output-Levi quotient gives admissibility
of the actual universal compact stages endpoint, with no coefficient-finiteness premise. -/
theorem universalCompactComparisonNativeCompactInduced_isAdmissible
    [CompactSpace (LeftQuotient K)]
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsAdmissible σ) (hcusp : IsSupercuspidal r σ) :
    IsAdmissible (R := RegularAlgebra r)
      (V := CompactFunctions K (universalNativeEndpointCoefficient r hn hmul h hU D σ))
      (compactInduced (R := RegularAlgebra r) K
      (universalNativeEndpointCoefficient r hn hmul h hU D σ)) := by
  let := regularAlgebra_isNoetherianRing r
  exact D.compactComparisonNativeCompactInduced_isAdmissible
    (B := RegularAlgebra r) (V := RegularAlgebra r ⊗[ℂ] E) _
    (universalTargetStabilizerCoinvariant_isAdmissible r hn hmul h hU D σ hσ hcusp)

end Langlands.Plancherel.RationalNormalized
