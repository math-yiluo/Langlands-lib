import Langlands.Shimura.PEL.HarrisTaylorCMClassTransitivity
import Langlands.Shimura.PEL.HarrisTaylorCMOrbitStabilizers
import Langlands.Shimura.PEL.PolarizedWeilLevelStabilizers

/-! # Class stabilizers under actual coarse-level rigidity -/

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

local notation "transport" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "mapRep" => mapRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ

/-- Rigidity of the actual coarse-level objects: a rational self-isogeny
preserving the polarization up to a scalar and the given coarse orbit is the
identity. Both determinant and numerical tests apply to this same object. -/
def CoarseLevelHasNoAutomorphisms (U : HarrisLevel D) : Prop :=
  letI := auxiliaryStarRing D C
  ∀ (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S)),
    Good X → Num X →
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj)
      (he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
        associativity comparison symmetry stability square universality additivity X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a → e = Iso.refl _

local notation "Rigid" => CoarseLevelHasNoAutomorphisms D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  p compatibility h s hs htor hu additivity

variable (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
  [(V.subgroup.subgroupOf U.subgroup).Normal]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Forgetting to the coarse level erases the original normal translation. -/
theorem representativeOrbit_forget_normalTranslate
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S))
    (g : U.subgroup) :
    letI := auxiliaryStarRing D C
    ∀ a : (orbitTower X).obj ((indexFunctor).obj V),
      (orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU))
          ((orbitTower X).map
            ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) a) =
        (orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) a := by
  let := auxiliaryStarRing D C
  intro a
  have hcoset :
      ((indexFunctor).map
        (CompactOpenLevel.normalInverseArrow U V hVU g ≫
          CompactOpenLevel.inclusion hVU)).element⁻¹ *
        ((indexFunctor).map (CompactOpenLevel.inclusion hVU)).element ∈
      ((indexFunctor).obj U).subgroup := by
    simpa only [hodgeLevelFunctor_map_element, CompactOpenLevel.comp_element,
      CompactOpenLevel.normalInverseArrow_element, CompactOpenLevel.inclusion,
      mul_one, map_one, mul_one, map_inv, inv_inv] using
      (hodgeLevelFunctor_obj_mem D C U (g : OriginalGroup)).mpr g.property
  calc
    _ = (orbitTower X).map ((indexFunctor).map
        (CompactOpenLevel.normalInverseArrow U V hVU g ≫
          CompactOpenLevel.inclusion hVU)) a := by
      rw [(indexFunctor).map_comp, (orbitTower X).map_comp]
      rfl
    _ = _ := PolarizedWeilLevel.levelTower_map_eq_of_target_coset preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality compatibility h A (D.harrisHodgePELForm C) s hs htor hu
      _ _ hcoset X a

/-- Coarse rigidity removes the actual self-isogeny in a fine class-equality
witness, leaving precisely membership in the original fine subgroup. -/
theorem classOf_normalTranslate_eq_self_iff (hRigid : Rigid U)
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S))
    (hX : Good X) (hnX : Num X) (g : U.subgroup) :
    letI := auxiliaryStarRing D C
    ∀ a : (orbitTower X).obj ((indexFunctor).obj V),
      mkClass (mapRep (CompactOpenLevel.normalInverseArrow U V hVU g) ⟨X, a⟩)
          hX hnX = mkClass ⟨X, a⟩ hX hnX ↔
        (g : OriginalGroup) ∈ V.subgroup := by
  let := auxiliaryStarRing D C
  intro a
  constructor
  · intro hclass
    obtain ⟨q, e, he, hlevel⟩ :=
      (classOf_eq_iff D C hΦ preservation composition unitCoherence associativity
        comparison symmetry stability square universality reflexStructure compatibility
        h s hs htor hu additivity L p
        (mapRep (CompactOpenLevel.normalInverseArrow U V hVU g) ⟨X, a⟩)
        ⟨X, a⟩ hX hX hnX hnX).mp hclass
    change transport X X ((indexFunctor).obj V) q e he
      ((orbitTower X).map
        ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) a) = a
      at hlevel
    have hcoarse :
        transport X X ((indexFunctor).obj U) q e he
            ((orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) a) =
          (orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) a := by
      calc
        _ = transport X X ((indexFunctor).obj U) q e he
            ((orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU))
              ((orbitTower X).map
                ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) a)) := by
          rw [representativeOrbit_forget_normalTranslate D C preservation composition
            unitCoherence associativity comparison symmetry stability square universality
            compatibility h s hs htor hu U V hVU X g a]
        _ = (orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU))
            (transport X X ((indexFunctor).obj V) q e he
              ((orbitTower X).map
                ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) a)) :=
          PolarizedWeilLevel.levelIso_map preservation composition unitCoherence
            associativity comparison symmetry stability square universality compatibility
            h A (D.harrisHodgePELForm C) s hs htor hu additivity
            ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) q e he _
        _ = _ := congrArg
          ((orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU))) hlevel
    have heid := hRigid X hX hnX
      ((orbitTower X).map ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) a)
      q e he hcoarse
    subst e
    rw [PolarizedWeilLevel.levelIso_identity_of_multiple preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity
      X ((indexFunctor).obj V) q he] at hlevel
    exact (representativeOrbit_normalTranslate_eq_self_iff D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h s hs htor hu U V hVU X g a).mp hlevel
  · intro hg
    have hlevel :=
      (representativeOrbit_normalTranslate_eq_self_iff D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        compatibility h s hs htor hu U V hVU X g a).mpr hg
    change mkClass ⟨X, (orbitTower X).map
        ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) a⟩ hX hnX =
      mkClass ⟨X, a⟩ hX hnX
    rw [hlevel]

/-- The stabilizer criterion holds for every actual CM rational-isogeny class,
using a representative satisfying both original conditions. -/
theorem classMap_normalTranslate_eq_self_iff (hRigid : Rigid U)
    (g : U.subgroup) (x : Classes V) :
    mapClass (CompactOpenLevel.normalInverseArrow U V hVU g) x = x ↔
      (g : OriginalGroup) ∈ V.subgroup := by
  obtain ⟨⟨X, a⟩, hX, hnX, hx⟩ := classOf_surjective D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality reflexStructure
    compatibility h s hs htor hu additivity L p x
  rw [← hx]
  exact classOf_normalTranslate_eq_self_iff D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h s hs
    htor hu additivity U V hVU hRigid X hX hnX g a

/-- Original normal translation is trivial after the actual class-level
forgetful map, before any rigidity premise. -/
theorem classMap_forget_normalTranslate (g : U.subgroup) (x : Classes V) :
    mapClass (CompactOpenLevel.inclusion hVU)
        (mapClass (CompactOpenLevel.normalInverseArrow U V hVU g) x) =
      mapClass (CompactOpenLevel.inclusion hVU) x := by
  let := auxiliaryStarRing D C
  obtain ⟨⟨X, a⟩, hX, hnX, hx⟩ := classOf_surjective D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality reflexStructure
    compatibility h s hs htor hu additivity L p x
  rw [← hx]
  change mkClass ⟨X, (orbitTower X).map
        ((indexFunctor).map (CompactOpenLevel.inclusion hVU))
        ((orbitTower X).map
          ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) a)⟩ hX hnX =
    mkClass ⟨X, (orbitTower X).map
      ((indexFunctor).map (CompactOpenLevel.inclusion hVU)) a⟩ hX hnX
  rw [representativeOrbit_forget_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h s hs htor hu U V hVU X g a]

/-- The original inverse-right class translations have the left-action order. -/
theorem classMap_normalTranslate_mul (g k : U.subgroup) (x : Classes V) :
    mapClass (CompactOpenLevel.normalInverseArrow U V hVU (g * k)) x =
      mapClass (CompactOpenLevel.normalInverseArrow U V hVU g)
        (mapClass (CompactOpenLevel.normalInverseArrow U V hVU k) x) := by
  change (tower).map (CompactOpenLevel.normalInverseArrow U V hVU (g * k)) x =
    (tower).map (CompactOpenLevel.normalInverseArrow U V hVU g)
      ((tower).map (CompactOpenLevel.normalInverseArrow U V hVU k) x)
  rw [CompactOpenLevel.normalInverseArrow_mul, (tower).map_comp]
  rfl

/-- Equality between two original translations of the same actual CM class
is exactly equality modulo the fine subgroup, under coarse rigidity. -/
theorem classMap_normalTranslate_eq_iff (hRigid : Rigid U)
    (g k : U.subgroup) (x : Classes V) :
    mapClass (CompactOpenLevel.normalInverseArrow U V hVU g) x =
        mapClass (CompactOpenLevel.normalInverseArrow U V hVU k) x ↔
      (g : OriginalGroup) * (k : OriginalGroup)⁻¹ ∈ V.subgroup := by
  have hfix := classMap_normalTranslate_eq_self_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    p compatibility h s hs htor hu additivity U V hVU hRigid (g * k⁻¹)
    (mapClass (CompactOpenLevel.normalInverseArrow U V hVU k) x)
  have hcomp :
      mapClass (CompactOpenLevel.normalInverseArrow U V hVU (g * k⁻¹))
          (mapClass (CompactOpenLevel.normalInverseArrow U V hVU k) x) =
        mapClass (CompactOpenLevel.normalInverseArrow U V hVU g) x := by
    rw [← classMap_normalTranslate_mul D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility
      h s hs htor hu additivity U V hVU (g * k⁻¹) k x]
    simp only [inv_mul_cancel_right]
  rw [hcomp] at hfix
  exact hfix

/-- Original residual translation embeds the residual group into actual CM
rational-isogeny classes, with coarse rigidity as its explicit hypothesis. -/
def classResidualEmbedding (hRigid : Rigid U) (x : Classes V) :
    (U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) ↪ Classes V := by
  refine ⟨Quotient.lift
    (fun g : U.subgroup =>
      mapClass (CompactOpenLevel.normalInverseArrow U V hVU g) x) ?_, ?_⟩
  · intro g k hrel
    apply (classMap_normalTranslate_eq_iff D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility h s hs
      htor hu additivity U V hVU hRigid g k x).mpr
    have heq : (g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) = k :=
      Quotient.sound hrel
    have hdiv := QuotientGroup.eq_iff_div_mem.mp heq
    exact hdiv
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro g k heq
    apply QuotientGroup.eq_iff_div_mem.mpr
    exact (classMap_normalTranslate_eq_iff D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility h s hs
      htor hu additivity U V hVU hRigid g k x).mp heq

local notation "residualEmbedding" => classResidualEmbedding D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p compatibility
  h s hs htor hu additivity U V hVU

/-- The residual embedding evaluates to the original class map on each
element of the original subgroup. -/
@[simp] theorem classResidualEmbedding_mk (hRigid : Rigid U)
    (x : Classes V) (g : U.subgroup) :
    residualEmbedding hRigid x (g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) =
      mapClass (CompactOpenLevel.normalInverseArrow U V hVU g) x := rfl

/-- The image of every residual translation lies in the same actual coarse
class fiber as the supplied starting class. -/
theorem classResidualEmbedding_forget (hRigid : Rigid U) (x : Classes V)
    (q : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) :
    mapClass (CompactOpenLevel.inclusion hVU) (residualEmbedding hRigid x q) =
      mapClass (CompactOpenLevel.inclusion hVU) x := by
  induction q using Quotient.inductionOn with
  | h g =>
    exact classMap_forget_normalTranslate D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility h s hs
      htor hu additivity U V hVU g x

/-- Coarse rigidity and the proved class transitivity construct a bijection
from the original residual group to the exact coarse fiber of the actual
fine class tower. No quotient representatives are selected by its forward map. -/
def classResidualFiberEquiv (hRigid : Rigid U) (x : Classes V) :
    (U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) ≃
      {y : Classes V // mapClass (CompactOpenLevel.inclusion hVU) y =
        mapClass (CompactOpenLevel.inclusion hVU) x} :=
  Equiv.ofBijective
    (fun q => ⟨residualEmbedding hRigid x q,
      classResidualEmbedding_forget D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality p compatibility h s hs
        htor hu additivity U V hVU hRigid x q⟩)
    ⟨fun _ _ hq => (residualEmbedding hRigid x).injective (congrArg Subtype.val hq), by
      intro y
      obtain ⟨g, hg⟩ := classMap_exists_normalTranslate D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        p compatibility h s hs htor hu additivity U V hVU x y.val y.property.symm
      exact ⟨(g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup), Subtype.ext hg⟩⟩

/-- The fiber equivalence sends an original subgroup element to its original
normal inverse-right class translation. -/
@[simp] theorem classResidualFiberEquiv_mk (hRigid : Rigid U)
    (x : Classes V) (g : U.subgroup) :
    (classResidualFiberEquiv D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality p compatibility h s hs htor hu
        additivity U V hVU hRigid x
        (g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup)).val =
      mapClass (CompactOpenLevel.normalInverseArrow U V hVU g) x := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
