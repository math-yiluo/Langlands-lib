import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedClasses
import Langlands.AlgebraicGeometry.FiniteEtale.IdentityPoint

/-! # Surjective CM level transitions at identity points -/

universe u v w

namespace Langlands.Shimura.PEL.InvariantOrbit

variable {G : Type u} {Γ : Type v} {X : Type w}
  [Group G] [Group Γ] [MulAction Gᵐᵒᵖ X] [MulAction Γ X]
  [SMulCommClass Γ Gᵐᵒᵖ X] [Subsingleton Γ]
  {U V : Subgroup G}

private theorem translate_surjective_of_subsingleton (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V) :
    Function.Surjective (translate (X := X) (Γ := Γ) g hg) := by
  intro q
  obtain ⟨x, hx⟩ := Quotient.mk_surjective q.val
  refine ⟨⟨RightOrbit.mk U (right x g⁻¹), ?_⟩, ?_⟩
  · intro γ
    rw [Subsingleton.elim γ 1, one_smul]
  · apply Subtype.ext
    change RightOrbit.mk V (right (right x g⁻¹) g) = q.val
    rw [right_mul, inv_mul_cancel, right_one]
    exact hx

end Langlands.Shimura.PEL.InvariantOrbit

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

section AtBase

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


variable [Subsingleton (FundamentalGroup s hs)]

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem representativeOrbitMap_surjective
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S))
    {U V : HarrisLevel D} (f : U ⟶ V) :
    letI := auxiliaryStarRing D C
    Function.Surjective
      ((PolarizedWeilLevel.levelTower preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility
        h A (D.harrisHodgePELForm C) s hs htor hu X).map
          ((hodgeLevelFunctor D C).map f)) := by
  let := auxiliaryStarRing D C
  let Frame := WeilAdelicFrame preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
  let : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
      (D.harrisHodgePELForm C))ᵐᵒᵖ Frame :=
    weilAdelicFrameRightAction preservation composition unitCoherence associativity
      comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
      compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
  let : MulAction (FundamentalGroup s hs) Frame :=
    weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity
      comparison symmetry stability compatibility rationalWeilGeometricTransport
      X.hasDual X.geometry X.inversePoincare X.evaluation X.polarization
      h X.actionObj.action A (D.harrisHodgePELForm C) s hs htor hu
  let : SMulCommClass (FundamentalGroup s hs)
      (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
        (D.harrisHodgePELForm C))ᵐᵒᵖ Frame :=
    weilAdelicFrameActionsComm preservation composition unitCoherence associativity
      comparison symmetry stability compatibility rationalWeilGeometricTransport
      X.hasDual X.geometry X.inversePoincare X.evaluation X.polarization
      h X.actionObj.action A (D.harrisHodgePELForm C) s hs htor hu
  exact InvariantOrbit.translate_surjective_of_subsingleton
    ((hodgeLevelFunctor D C).map f).element ((hodgeLevelFunctor D C).map f).respects

/-- Triviality of the actual point-functor automorphism group lets every
transporter lift without changing the polarized representative. -/
theorem classMap_surjective_of_subsingleton {U V : HarrisLevel D} (f : U ⟶ V) :
    Function.Surjective (mapClass f) := by
  intro q
  obtain ⟨x, hx, hn, hq⟩ := classOf_surjective D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality reflexStructure
    compatibility h s hs htor hu additivity L p q
  rcases x with ⟨X, z⟩
  obtain ⟨y, hy⟩ := representativeOrbitMap_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h s hs htor hu X f z
  refine ⟨mkClass ⟨X, y⟩ hx hn, ?_⟩
  rw [← hq]
  exact congrArg (fun z' => mkClass ⟨X, z'⟩ hx hn) hy

end AtBase

section IdentityPoint

variable {Ω : Type} [Field Ω]
  (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (hs : ∀ Y : Cover (Spec (CommRingCat.of Ω)), Finite (Fiber (𝟙 (Spec (CommRingCat.of Ω))) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Spec (CommRingCat.of Ω), ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := Spec (CommRingCat.of Ω)))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "reflexStructure" => D.harrisTaylorReflexStructure C p
local notation "Classes" => IsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu additivity L p
local notation "mapClass" => classMap D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu additivity L p

/-- Surjectivity of every original CM transporter at the identity point of a
field spectrum. The triviality premise is proved by naturality on sections. -/
theorem identityPoint_classMap_surjective {U V : HarrisLevel D} (f : U ⟶ V) :
    Function.Surjective (mapClass f) :=
  classMap_surjective_of_subsingleton D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility
    h (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu additivity f

/-- A chosen actual fine-level CM class above a given coarse-level class.
The class, polarized representative and all its witnesses are constructed
using the proved orbit lift; no nonemptiness hypothesis is added. -/
def identityPointLevelLift {U V : HarrisLevel D} (f : U ⟶ V) : Classes V → Classes U :=
  Function.surjInv (identityPoint_classMap_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    p compatibility h hs htor hu additivity f)

/-- The chosen lift maps to the original class under the original transition. -/
@[simp] theorem classMap_identityPointLevelLift {U V : HarrisLevel D}
    (f : U ⟶ V) (q : Classes V) :
    mapClass f (identityPointLevelLift D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility
      h hs htor hu additivity f q) = q :=
  Function.surjInv_eq (identityPoint_classMap_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    p compatibility h hs htor hu additivity f) q

end IdentityPoint

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
