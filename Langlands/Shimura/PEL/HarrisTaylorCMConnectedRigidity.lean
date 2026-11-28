import Langlands.Shimura.PEL.HarrisTaylorCMWitnessBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelRigidityProof
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.AbelianScheme.ConnectedGeometricPointHomFaithfulnessStatement
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof

/-! # Uniqueness of witnesses of the normalized CM class relation on connected bases -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

/-- A rational homomorphism of abelian schemes over a connected locally noetherian
base with invertible integers vanishes if its pullback to one algebraically closed
geometric point vanishes, given the integral statement. -/
theorem rationalHom_eq_zero_of_geometricBaseChange
    (G0 : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    {S : Scheme.{0}} [IsLocallyNoetherian S] [ConnectedSpace S]
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A B : AbelianScheme S} (f : Hom0 A B) (hf : rationalBaseChangeHom s f = 0) :
    f = 0 := by
  obtain ⟨n, hn, g, hg⟩ := Tate.exists_positive_integral_multiple f
  have h1 : Rationalization.ofHom ((baseChange s).map g) =
      Rationalization.ofHom (0 : (baseChange s).obj A ⟶ (baseChange s).obj B) := by
    rw [← rationalBaseChangeHom_ofHom, hg, map_nsmul, hf, smul_zero, map_zero]
  obtain ⟨m, hm, hmg⟩ := (Rationalization.ofHom_eq_iff_exists_zsmul_eq _ _).mp h1
  have hbc : (baseChange s).map (m • g) = 0 := by
    rw [Functor.map_zsmul, hmg, smul_zero]
  have hmg0 : m • g = 0 := G0 S hu Ω s A B (m • g) hbc
  have hnat : m.natAbs • g = 0 := natAbs_nsmul_eq_zero.mpr hmg0
  have hg0 : g = 0 := by
    apply Tate.hom_nsmul_injective hu (Int.natAbs_pos.mpr hm)
    simpa only [smul_zero] using hnat
  have hnf : n • f = 0 := by rw [← hg, hg0, map_zero]
  have hqf : (n : ℚ) • f = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hnf
  rw [← inv_smul_smul₀ (show (n : ℚ) ≠ 0 by exact_mod_cast hn.ne') f, hqf, smul_zero]

/-- Pullback along a base map from a scheme with an algebraically closed
geometric point is injective on rational Hom out of a connected base with
invertible integers, given geometric-point faithfulness. -/
theorem rationalBaseChangeHom_injective_of_geometricPoint
    (geometricFaithfulness : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    {S T : Scheme.{0}} [IsLocallyNoetherian S] [ConnectedSpace S]
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    (b : T ⟶ S) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (A B : AbelianScheme S) :
    Function.Injective (rationalBaseChangeHom b (A := A) (B := B)) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply rationalHom_eq_zero_of_geometricBaseChange geometricFaithfulness hu (t ≫ b)
  have hz : rationalBaseChangeHom b (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  let e := baseChangeCompIso b t B
  have he : comp0 _ _ _ (rationalBaseChangeHom (t ≫ b) (f - g))
      (homToHom0 e.hom) = 0 := by
    rw [rationalBaseChangeHom_base_comp, hz, map_zero, map_zero]
  have he' := congrArg (fun r => comp0 _ _ _ r (homToHom0 e.inv)) he
  rw [comp0_assoc, comp0_homToHom0, e.hom_inv_id, homToHom0_id, comp0_id0] at he'
  simpa only [map_zero, LinearMap.zero_apply] using he'

end Langlands.AbelianScheme

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "admissible" => AdmissibleCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

include dualityNaturality polarizationStability in
/-- Witnesses of the normalized CM class relation between two fixed
representatives on a connected locally noetherian base are unique, when the
coarse level has geometric rigidity. The representatives are taken at a
geometric point `𝟙 ≫ z`; the uniqueness is derived by pulling a self-witness
back to the geometric point, applying rigidity there, and using the integral
faithfulness statement on the connected base. -/
theorem witness_eq_of_geometricRigidity
    (G0 : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    {U : HarrisLevel D}
    (hRigid : CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor U)
    {Z : Scheme.{0}} [ConnectedSpace Z] [IsLocallyNoetherian Z] (p : Z ⟶ Spec (.of F))
    (lieZ : LieBaseChangeNaturalityStatement Z)
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Z, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu Z k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu Z k.val).X.hom]
    (addZ : PositivePairAdditivity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := Z))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Z)
    (hs : ∀ Y : Cover Z, Finite (Fiber (𝟙 _ ≫ z) Y))
    (x y : HarrisLevelData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h (𝟙 _ ≫ z) hs htor hu U)
    (hx : PositiveObjectCondition D C hΦ preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C p) x.1)
    (hn : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L p x.1) :
    letI := auxiliaryStarRing D C
    ∀ (q q' : ℚˣ) (e e' : x.1.actionObj ≅ y.1.actionObj)
      (he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
        associativity comparison symmetry stability square universality addZ x.1 y.1 q e)
      (he' : PolarizedWeilLevel.Multiple preservation composition unitCoherence
        associativity comparison symmetry stability square universality addZ x.1 y.1 q' e'),
      PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hs htor hu addZ x.1 y.1
          ((hodgeLevelFunctor D C).obj U) q e he x.2 = y.2 →
      PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hs htor hu addZ x.1 y.1
          ((hodgeLevelFunctor D C).obj U) q' e' he' x.2 = y.2 →
      e = e' := by
  let := auxiliaryStarRing D C
  intro q q' e e' he he' hl hl'
  -- The self-witness `e ≫ e'⁻¹`.
  let σ : x.1.actionObj ≅ x.1.actionObj := e.trans e'.symm
  have hσ := PolarizedWeilLevel.multiple_trans preservation composition unitCoherence
    associativity comparison symmetry stability square universality addZ he
    (PolarizedWeilLevel.multiple_symm preservation composition unitCoherence
      associativity comparison symmetry stability square universality addZ he')
  have hfix : PolarizedWeilLevel.levelIso preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hs htor hu addZ x.1 x.1
      ((hodgeLevelFunctor D C).obj U) (q * q'⁻¹) σ hσ x.2 = x.2 := by
    rw [PolarizedWeilLevel.levelIso_trans, Equiv.trans_apply, hl,
      ← PolarizedWeilLevel.levelIso_symm, ← hl', Equiv.symm_apply_apply]
    all_goals first
      | exact he
      | exact he'
      | exact PolarizedWeilLevel.multiple_symm preservation composition unitCoherence
          associativity comparison symmetry stability square universality addZ he'
  -- Admissibility of the geometric point.
  let : IsLocallyNoetherian (Over.mk (z ≫ p)).left :=
    show IsLocallyNoetherian (Spec (CommRingCat.of Ω)) from inferInstance
  let : ConnectedSpace (Over.mk (z ≫ p)).left :=
    show ConnectedSpace (Spec (CommRingCat.of Ω)) from inferInstance
  have hp : admissible (Over.mk (z ≫ p)) :=
    (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk (z ≫ p))).mpr
        (fun B => ⟨relativeDualSchemeExistence.{0} _ B,
          relativeDualSchemeGeometry.{0} _ B (relativeDualSchemeExistence.{0} _ B)⟩)
  have : ∀ k : Index (fun _ => True), IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom :=
    hp.muFinite
  have : ∀ k : Index (fun _ => True), Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom :=
    hp.muEtale
  let dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := Z),
      PositivePullbackDualData D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality z X := by
    intro X
    exact Classical.choice (hp.dualExists
      ((Langlands.AbelianScheme.baseChange z).obj X.actionObj.abelianScheme))
  -- Pull the self-witness back to the geometric point.
  obtain ⟨hσb, hfixb⟩ := levelDataBaseChange_witness D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability z compatibility h (𝟙 _)
    (HarrisGeometricPoint.mk Ω (𝟙 _)).finiteFibers hs htor hu hp.torsionUnits dualData
    addZ hp.pairAdditivity x x (q * q'⁻¹) σ hσ hfix
  have hGood := levelDataBaseChange_objectCondition D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability z compatibility h (𝟙 _)
    (HarrisGeometricPoint.mk Ω (𝟙 _)).finiteFibers hs htor hu hp.torsionUnits dualData
    p lieZ x hx
  have hNum := HarrisNumericalWeilLevel.levelDataBaseChange_numericalObjectCondition D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability z compatibility h (𝟙 _)
    (HarrisGeometricPoint.mk Ω (𝟙 _)).finiteFibers hs htor hu hp.torsionUnits dualData
    lieZ L p x hn
  have hrefl := hRigid Ω (z ≫ p) hp _ hGood hNum _ (q * q'⁻¹) _ hσb hfixb
  -- Transfer the identity back along the geometric point.
  have hzero : rationalBaseChangeHom z
      (RationalAlgebraAction.hom0 σ.hom - id0 x.1.actionObj.abelianScheme) = 0 := by
    have k := congrArg (fun i => RationalAlgebraAction.hom0 i.hom) hrefl
    simp only [Functor.mapIso_hom, RationalAlgebraAction.hom0_pullback_map,
      Iso.refl_hom, RationalAlgebraAction.hom0_id] at k
    rw [map_sub, k]
    exact sub_eq_zero.mpr (rationalBaseChangeHom_identity z _).symm
  have hσid := sub_eq_zero.mp (rationalHom_eq_zero_of_geometricBaseChange G0 hu z _ hzero)
  have hσrefl : σ.hom = 𝟙 _ := RationalAlgebraAction.hom_ext hσid
  apply Iso.ext
  have k : e.hom ≫ e'.inv = 𝟙 _ := hσrefl
  calc e.hom = (e.hom ≫ e'.inv) ≫ e'.hom := by simp
    _ = e'.hom := by rw [k]; exact Category.id_comp _

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
