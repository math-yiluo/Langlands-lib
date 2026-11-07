import Langlands.Representation.Geometric.RepresentedGeometricLemmaCompactGeometry
import Langlands.Representation.Induction.SplitStagesAmbientHaar

/-! # The original ambient Haar ratio of the represented compact comparison -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Induction

open Aubert.General MeasureTheory MeasureTheory.Measure

private theorem ambientHaarRatio_of_stabilizer_eq
    {A : Type u} [Group A] [TopologicalSpace A]
    [IsTopologicalGroup A] [LocallyCompactSpace A]
    {Q L U : Subgroup A} (d : IsSemidirectDecomposition Q L U)
    (S : Subgroup Q) (hker : d.projection.ker ≤ S)
    (F : Subgroup A) (H : Subgroup Q)
    (heq : H = (Q ⊓ F).subgroupOf Q)
    (hU : IsClosed (U : Set A)) (hF : IsClosed (F : Set A))
    [LocallyCompactSpace (MonoidHom.ker (splitStagesRetraction d.projection
      (Subgroup.inclusion d.levi_le) (fun l => d.projection_levi l) S hker))]
    [MeasurableSpace (MonoidHom.ker (splitStagesRetraction d.projection
      (Subgroup.inclusion d.levi_le) (fun l => d.projection_levi l) S hker))]
    [BorelSpace (MonoidHom.ker (splitStagesRetraction d.projection
      (Subgroup.inclusion d.levi_le) (fun l => d.projection_levi l) S hker))]
    [MeasurableSpace ((H.subgroupOf S).comap
      (MonoidHom.ker (splitStagesRetraction d.projection
        (Subgroup.inclusion d.levi_le) (fun l => d.projection_levi l) S hker)).subtype)]
    [BorelSpace ((H.subgroupOf S).comap
      (MonoidHom.ker (splitStagesRetraction d.projection
        (Subgroup.inclusion d.levi_le) (fun l => d.projection_levi l) S hker)).subtype)]
    (hsH : ∀ l : S.comap (Subgroup.inclusion d.levi_le),
      Subgroup.inclusion d.levi_le (l : L) ∈ H)
    (hSF : ∀ l : S.comap (Subgroup.inclusion d.levi_le), ((l : L) : A) ∈ F)
    (hHS : IsClosed (H.subgroupOf S : Set S))
    (l : S.comap (Subgroup.inclusion d.levi_le)) :
    splitKernelHaarRatio
        (splitStagesRetraction d.projection (Subgroup.inclusion d.levi_le)
          (fun m => d.projection_levi m) S hker)
        (MonoidHom.subgroupComap (Subgroup.inclusion d.levi_le) S)
        (H.subgroupOf S) hsH hHS l =
      HaarModulus.closedRestrictCharacter U hU L d.levi_le_normalizer (l : L) /
        HaarModulus.closedNormalizerCharacter (U ⊓ F) (hU.inter hF)
          ⟨((l : L) : A), splitStagesAmbient_normalizes d F
            ⟨(l : L).property, hSF l⟩⟩ := by
  subst H
  exact splitStagesAmbientHaarRatio_apply d S hker F hU hF hsH hHS l

end Langlands.Induction

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance compactHaarAmbientTopology : TopologicalSpace (rationalPoints G) :=
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

local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "π" => IsSemidirectDecomposition.projection dQ
local notation "sQ" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le dQ)
local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "F" => Subgroup.map
  (MulEquiv.toMonoidHom (MulAut.conj z⁻¹)) (pointImage p)
local notation "Kt" => geometricTargetIntersection (pointImage (lQ ≫ q)) (pointImage p) z⁻¹
local notation "KQ" => Subgroup.subgroupOf Kt (pointImage (lQ ≫ q))
local notation "UI" => pointImage (rQ ≫ q)
local notation "C" => geometricTargetIntersection UI (pointImage p) z⁻¹
local notation "hUI" => isClosed_pointImage_comp q rQ hq.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hrQ))
local notation "hPJ" => isClosed_pointImage p hp.isClosedSubgroup
local notation "hF" => isClosed_map_conj (pointImage p) hPJ z⁻¹
local notation "hH" => Geometric.isClosed_orbitStabilizer
  (pointImage p) (pointImage q) z⁻¹ hPJ

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "S" => compactComparisonSaturation D
local notation "hker" => projectionKernel_le_compactComparisonSaturation D
local notation "rS" => splitStagesRetraction π sQ
  (fun m => IsSemidirectDecomposition.projection_levi dQ m) S hker
local notation "sS" => MonoidHom.subgroupComap sQ S
local notation "HS" => Subgroup.subgroupOf H S
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rS)) HS
local notation "hSI" => compactComparisonSaturation_section_mem_stabilizer D
local notation "hHS" => IsClosed.preimage
  (continuous_subtype_val : Continuous (Subgroup.subtype S)) hH

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The original Levi section identifies the compact comparison subgroup
with the literal target intersection inside the original Levi. -/
theorem compactComparisonSaturation_comap_section :
    Subgroup.comap sQ S = KQ := by
  ext m
  change (π) ⟨(m : rationalPoints G), (dQ).levi_le m.property⟩ ∈ KQ ↔ m ∈ KQ
  rw [IsSemidirectDecomposition.projection_levi]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The compact comparison subgroup is the full original target intersection,
with unchanged ambient points and induced topology. -/
def compactComparisonLeviEquiv : Subgroup.comap sQ S ≃ₜ* Kt :=
  (subgroupCongrContinuous D.compactComparisonSaturation_comap_section).trans
    (subgroupOfContinuousEquiv inf_le_left)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
@[simp] theorem compactComparisonLeviEquiv_apply (x : Subgroup.comap sQ S) :
    (D.compactComparisonLeviEquiv x : rationalPoints G) =
      ((x : pointImage (lQ ≫ q)) : rationalPoints G) := rfl

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
@[simp] theorem compactComparisonLeviEquiv_symm_apply (x : Kt) :
    (((D.compactComparisonLeviEquiv.symm x : Subgroup.comap sQ S) :
      pointImage (lQ ≫ q)) : rationalPoints G) = (x : rationalPoints G) := rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
private theorem stabilizer_eq_ambient_intersection :
    H = (pointImage q ⊓ F).subgroupOf (pointImage q) := by
  ext a
  change (MulAut.conj (z⁻¹)⁻¹) (a : rationalPoints G) ∈ pointImage p ↔
    (a : rationalPoints G) ∈ pointImage q ∧
      (a : rationalPoints G) ∈ F
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv]
  exact ⟨fun h => ⟨a.property, h⟩, fun h => h.2⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
private theorem compactComparison_section_mem_conjugate
    (x : Subgroup.comap sQ S) :
    ((x : pointImage (lQ ≫ q)) : rationalPoints G) ∈ F :=
  (D.compactComparisonLeviEquiv x).property.2

/-- The target radical modulus on the whole original target intersection. -/
def compactAmbientRadicalModulus (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ z) : Kt →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter UI hUI Kt
    (le_trans inf_le_left (IsSemidirectDecomposition.levi_le_normalizer dQ))

/-- The correction-intersection modulus on that same full target intersection. -/
def compactAmbientCorrectionModulus (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ z) : Kt →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter C ((hUI).inter hF) Kt
    (splitStagesAmbient_normalizes dQ F)

local instance compactHaarKernelLocallyCompact :
    LocallyCompactSpace (MonoidHom.ker rS) :=
  representedNestedKernelLocallyCompactSpace q lQ rQ hq hrQ hmulQ S hker

local instance compactHaarKernelMeasurable : MeasurableSpace (MonoidHom.ker rS) := borel _
local instance compactHaarKernelBorel : BorelSpace (MonoidHom.ker rS) := ⟨rfl⟩
local instance compactHaarIntersectionMeasurable : MeasurableSpace I := borel _
local instance compactHaarIntersectionBorel : BorelSpace I := ⟨rfl⟩

/-- The exact Haar character from the actual nested relative integral,
transported to the whole original target intersection. -/
def compactIntegralHaarCharacter : Kt →* ℂˣ :=
  (Jacquet.complexCharacter (splitKernelHaarRatio rS sS HS hSI hHS)).comp
    D.compactComparisonLeviEquiv.symm.toMonoidHom

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The nested Haar ratio is the original radical modulus divided by the
literal correction-intersection modulus. No dynamic realization is needed. -/
theorem compactIntegralHaarCharacter_eq_ambient (x : Kt) :
    D.compactIntegralHaarCharacter x =
      Jacquet.complexCharacter D.compactAmbientRadicalModulus x /
        Jacquet.complexCharacter D.compactAmbientCorrectionModulus x := by
  have hh :
      splitKernelHaarRatio rS sS HS hSI hHS (D.compactComparisonLeviEquiv.symm x) =
        D.compactAmbientRadicalModulus x / D.compactAmbientCorrectionModulus x :=
    Induction.ambientHaarRatio_of_stabilizer_eq dQ S hker F H
      (stabilizer_eq_ambient_intersection (p := p) (q := q) (z := z)) hUI hF hSI
      D.compactComparison_section_mem_conjugate hHS (D.compactComparisonLeviEquiv.symm x)
  apply Units.ext
  change (((((splitKernelHaarRatio rS sS HS hSI hHS
    (D.compactComparisonLeviEquiv.symm x) : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ)) = _
  rw [hh]
  simp only [Units.val_div_eq_div_val, Jacquet.complexCharacter_apply,
    NNReal.coe_div, Complex.ofReal_div]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The original radical modulus is smooth on the whole target intersection. -/
theorem isOpen_ker_compactAmbientRadicalModulus :
    IsOpen (D.compactAmbientRadicalModulus.ker : Set Kt) :=
  HaarModulus.isOpen_ker_closedRestrictCharacter UI hUI Kt
    (le_trans inf_le_left (IsSemidirectDecomposition.levi_le_normalizer dQ))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The correction-intersection modulus is smooth on that same group. -/
theorem isOpen_ker_compactAmbientCorrectionModulus :
    IsOpen (D.compactAmbientCorrectionModulus.ker : Set Kt) :=
  HaarModulus.isOpen_ker_closedRestrictCharacter C ((hUI).inter hF) Kt
    (splitStagesAmbient_normalizes dQ F)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The literal compact-integral scalar twist preserves smooth coefficients. -/
theorem isOpen_ker_compactIntegralHaarCharacter :
    IsOpen (D.compactIntegralHaarCharacter.ker : Set Kt) := by
  apply Subgroup.isOpen_mono
    (H₁ := D.compactAmbientRadicalModulus.ker ⊓ D.compactAmbientCorrectionModulus.ker)
  · intro x hx
    change D.compactIntegralHaarCharacter x = 1
    rw [D.compactIntegralHaarCharacter_eq_ambient]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Jacquet.complexCharacter_apply,
      show D.compactAmbientRadicalModulus x = 1 from hx.1,
      show D.compactAmbientCorrectionModulus x = 1 from hx.2]
    simp only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, div_self one_ne_zero]
  · exact D.isOpen_ker_compactAmbientRadicalModulus.inter
      D.isOpen_ker_compactAmbientCorrectionModulus

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
