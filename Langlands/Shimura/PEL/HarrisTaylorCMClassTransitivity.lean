import Langlands.Shimura.PEL.OrbitFibers
import Langlands.Shimura.PEL.HarrisTaylorCMNormalActions

/-! # Actual normal translation between CM classes with equal coarse image -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
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


variable {S : Scheme.{0}}
  (p : S ⟶ Spec (.of F))
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "reflexStructure" => D.harrisTaylorReflexStructure C p
local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "Good" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
local notation "Num" => NumericalObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
local notation "HarrisClasses" => HarrisIsoClass D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity
local notation "Condition" => ClassCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "Classes" => IsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "mkClass" => classOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "mkHarris" => harrisClassOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity
local notation "mapClass" => classMap D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "tower" => isoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p


local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "scalarEquiv" =>
  D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)
local notation "orbitTower" => PolarizedWeilLevel.levelTower preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu

variable (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
  [(V.subgroup.subgroupOf U.subgroup).Normal]

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem representativeOrbit_exists_normalTranslate
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S)) :
    letI := auxiliaryStarRing D C
    ∀ (x y : (orbitTower X).obj ((indexFunctor).obj V)),
    (orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) x =
      (orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) y →
    ∃ g : U.subgroup,
      (orbitTower X).map
        ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) x = y := by
  let := auxiliaryStarRing D C
  intro x y hxy
  let Frame := WeilAdelicFrame preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
  let : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
      (D.harrisHodgePELForm C))ᵐᵒᵖ Frame :=
    weilAdelicFrameRightAction preservation composition unitCoherence associativity
      comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
      compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
  have hVU' : ((indexFunctor).obj V).subgroup ≤ ((indexFunctor).obj U).subgroup :=
    fun _ hv => hVU hv
  have hconj : ∀ a ∈ ((indexFunctor).obj U).subgroup,
      ∀ b ∈ ((indexFunctor).obj V).subgroup,
        a⁻¹ * b * a ∈ ((indexFunctor).obj V).subgroup := by
    intro a ha b hb
    let a' : U.subgroup := ⟨(scalarEquiv).symm a, ha⟩
    have hmem :=
      (CompactOpenLevel.normalInverseArrow U V hVU a'⁻¹).respects
        ((scalarEquiv).symm b) hb
    change (scalarEquiv).symm (a⁻¹ * b * a) ∈ V.subgroup
    simpa only [map_mul, map_inv, CompactOpenLevel.normalInverseArrow_element,
      Subgroup.coe_inv, inv_inv] using hmem
  have hxy' :
      RightOrbit.translate (X := Frame)
        (U := ((indexFunctor).obj V).subgroup) (V := ((indexFunctor).obj U).subgroup)
        1 (by intro v hv; simpa using hVU' hv) x.val =
      RightOrbit.translate (X := Frame)
        (U := ((indexFunctor).obj V).subgroup) (V := ((indexFunctor).obj U).subgroup)
        1 (by intro v hv; simpa using hVU' hv) y.val := by
    rw [hodgeLevelFunctor_inclusion] at hxy
    exact congrArg Subtype.val hxy
  obtain ⟨a, ha, h⟩ := RightOrbit.exists_translate_of_forget_eq hVU' hconj
    x.val y.val hxy'
  refine ⟨(⟨(scalarEquiv).symm a, ha⟩ : U.subgroup)⁻¹, ?_⟩
  apply Subtype.ext
  change RightOrbit.translate
      ((indexFunctor).map
        (CompactOpenLevel.normalInverseArrow U V hVU
          (⟨(scalarEquiv).symm a, ha⟩ : U.subgroup)⁻¹)).element
      ((indexFunctor).map
        (CompactOpenLevel.normalInverseArrow U V hVU
          (⟨(scalarEquiv).symm a, ha⟩ : U.subgroup)⁻¹)).respects x.val = y.val
  simpa only [hodgeLevelFunctor_map_element, CompactOpenLevel.normalInverseArrow_element,
    Subgroup.coe_inv, inv_inv, ContinuousMulEquiv.apply_symm_apply] using h

local notation "transport" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "mapRep" => mapRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu

/-- Equal coarse CM classes are related at fine level by an element of the
original coarse Harris subgroup. The same two jointly satisfying polarized
representatives and the actual rational isogeny witness are retained. -/
theorem classMap_exists_normalTranslate (x y : Classes V)
    (hxy : mapClass (CompactOpenLevel.inclusion hVU) x =
      mapClass (CompactOpenLevel.inclusion hVU) y) :
    ∃ g : U.subgroup,
      mapClass (CompactOpenLevel.normalInverseArrow U V hVU g) x = y := by
  let := auxiliaryStarRing D C
  obtain ⟨⟨X, a⟩, hX, hnX, hx⟩ := classOf_surjective D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality reflexStructure
    compatibility h s hs htor hu additivity L p x
  obtain ⟨⟨Y, b⟩, hY, hnY, hy⟩ := classOf_surjective D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality reflexStructure
    compatibility h s hs htor hu additivity L p y
  rw [← hx, ← hy] at hxy ⊢
  let xU : Data U := mapRep (CompactOpenLevel.inclusion hVU) ⟨X, a⟩
  let yU : Data U := mapRep (CompactOpenLevel.inclusion hVU) ⟨Y, b⟩
  change mkClass xU hX hnX = mkClass yU hY hnY at hxy
  obtain ⟨q, e, he, hcoarse⟩ :=
    (classOf_eq_iff D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality reflexStructure compatibility
      h s hs htor hu additivity L p xU yU hX hY hnX hnY).mp hxy
  let z := transport X Y ((indexFunctor).obj V) q e he a
  have hforget :
      (orbitTower Y).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) z =
      (orbitTower Y).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) b := by
    calc
      _ = transport X Y ((indexFunctor).obj U) q e he
          ((orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) a) :=
        (PolarizedWeilLevel.levelIso_map preservation composition unitCoherence
          associativity comparison symmetry stability square universality compatibility
          h A (D.harrisHodgePELForm C) s hs htor hu additivity
          ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) q e he a).symm
      _ = _ := hcoarse
  obtain ⟨g, hg⟩ := representativeOrbit_exists_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h s hs htor hu U V hVU Y z b hforget
  refine ⟨g, ?_⟩
  change mkClass (mapRep (CompactOpenLevel.normalInverseArrow U V hVU g) ⟨X, a⟩)
      hX hnX = mkClass ⟨Y, b⟩ hY hnY
  apply (classOf_eq_iff D C hΦ preservation composition unitCoherence associativity
    comparison symmetry stability square universality reflexStructure compatibility
    h s hs htor hu additivity L p
    (mapRep (CompactOpenLevel.normalInverseArrow U V hVU g) ⟨X, a⟩)
    ⟨Y, b⟩ hX hY hnX hnY).mpr
  refine ⟨q, e, he, ?_⟩
  exact (PolarizedWeilLevel.levelIso_map preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility
    h A (D.harrisHodgePELForm C) s hs htor hu additivity
    ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g))
    q e he a).trans hg

/-- A chosen element of the original coarse Harris subgroup translating the
specified fine classes. Its existence is proved on the original quotient. -/
def normalClassTranslation (x y : Classes V)
    (hxy : mapClass (CompactOpenLevel.inclusion hVU) x =
      mapClass (CompactOpenLevel.inclusion hVU) y) : U.subgroup :=
  Classical.choose (classMap_exists_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    p compatibility h s hs htor hu additivity U V hVU x y hxy)

/-- The chosen original subgroup element acts through the original
inverse-right transporter and gives the specified target class. -/
theorem classMap_normalClassTranslation (x y : Classes V)
    (hxy : mapClass (CompactOpenLevel.inclusion hVU) x =
      mapClass (CompactOpenLevel.inclusion hVU) y) :
    mapClass (CompactOpenLevel.normalInverseArrow U V hVU
      (normalClassTranslation D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        p compatibility h s hs htor hu additivity U V hVU x y hxy)) x = y :=
  Classical.choose_spec (classMap_exists_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    p compatibility h s hs htor hu additivity U V hVU x y hxy)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
