import Langlands.Shimura.PEL.HarrisTaylorCMSchemeLevels

/-! # Target-coset descent of actual CM moduli and scheme transitions -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura

namespace CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- Actual transporters with the same target right coset are equivalent. -/
def targetCosetSetoid (U V : CompactOpenLevel G) : Setoid (U ⟶ V) where
  r f g := f.element⁻¹ * g.element ∈ V.subgroup
  iseqv := by
    constructor
    · intro f
      simp
    · intro f g hfg
      simpa using V.subgroup.inv_mem hfg
    · intro f g h hfg hgh
      simpa [mul_assoc] using V.subgroup.mul_mem hfg hgh

/-- The target-right-coset quotient of the genuine transporter arrows. -/
abbrev TargetCosetArrow (U V : CompactOpenLevel G) := Quotient (targetCosetSetoid U V)

end CompactOpenLevel

namespace PEL

section Orbits

variable {G : Type u} {Γ : Type v} {X : Type w}
  [Group G] [Group Γ] [MulAction Gᵐᵒᵖ X] [MulAction Γ X]
  [SMulCommClass Γ Gᵐᵒᵖ X] {U V : Subgroup G}

/-- Translation on right orbits depends only on the target right coset. -/
theorem RightOrbit.translate_eq_of_target_coset (g h : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V)
    (hh : ∀ u ∈ U, h⁻¹ * u * h ∈ V)
    (hgh : g⁻¹ * h ∈ V) (q : RightOrbit X U) :
    RightOrbit.translate g hg q = RightOrbit.translate h hh q := by
  induction q using Quotient.inductionOn with
  | h x =>
    apply (RightOrbit.mk_eq_mk V _ _).mpr
    refine ⟨g⁻¹ * h, hgh, ?_⟩
    simp [right_mul]

/-- The same target-coset equality holds after imposing monodromy invariance. -/
theorem InvariantOrbit.translate_eq_of_target_coset (g h : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V)
    (hh : ∀ u ∈ U, h⁻¹ * u * h ∈ V)
    (hgh : g⁻¹ * h ∈ V) (q : InvariantOrbit (X := X) Γ U) :
    InvariantOrbit.translate g hg q = InvariantOrbit.translate h hh q :=
  Subtype.ext (RightOrbit.translate_eq_of_target_coset g h hg hh hgh q.val)

end Orbits

namespace PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  {S : Scheme.{u}} {D : Type v} [Ring D] [Algebra ℚ D] [StarRing D]
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  [QuasiSeparatedSpace S]

local notation "PObj" => PolarizedAction preservation composition unitCoherence
  associativity comparison symmetry stability square universality S D
local notation "tower" => levelTower preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu
local notation "Level" => FiniteAdelicScalarExtensionLevel D V ψ

/-- Target-coset equality is proved on the actual compatible frame orbit. -/
theorem levelTower_map_eq_of_target_coset {K L : Level} (f g : K ⟶ L)
    (hfg : f.element⁻¹ * g.element ∈ L.subgroup) (X : PObj) (x : (tower X).obj K) :
    (tower X).map f x = (tower X).map g x := by
  let : MulAction
      (ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ)ᵐᵒᵖ
      (WeilAdelicFrame preservation composition unitCoherence associativity comparison
        symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
        compatibility X.polarization h X.actionObj.action V ψ s) :=
    weilAdelicFrameRightAction preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    compatibility X.polarization h X.actionObj.action V ψ s
  apply Subtype.ext
  exact RightOrbit.translate_eq_of_target_coset f.element g.element f.respects g.respects
    hfg x.val

variable (additivity : PairAdditivity preservation composition unitCoherence associativity
  comparison symmetry stability square universality (S := S) (D := D))

local notation "classes" => isoClassTower preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity
local notation "mkClass" => classOf preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity

/-- Equality on actual frame orbits descends to polarized rational-isogeny classes. -/
theorem isoClassTower_map_eq_of_target_coset {K L : Level} (f g : K ⟶ L)
    (hfg : f.element⁻¹ * g.element ∈ L.subgroup) :
    (classes).map f = (classes).map g := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro ⟨X, x⟩
  change mkClass ⟨X, (tower X).map f x⟩ = mkClass ⟨X, (tower X).map g x⟩
  rw [levelTower_map_eq_of_target_coset preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h V ψ s hs htor hu f g hfg]

end PolarizedWeilLevel

namespace HarrisNumericalWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E F Φ)
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  {S : Scheme.{0}}
  (b : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L F]
  (p : S ⟶ Spec (.of F))


local notation "Level" => HarrisLevel D
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "scalarEquiv" =>
  D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)
local notation "tower" => isoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity L p

/-- The actual original Harris numerical tower depends only on target right cosets. -/
theorem isoClassTower_map_eq_of_target_coset {U V : Level} (f g : U ⟶ V)
    (hfg : f.element⁻¹ * g.element ∈ V.subgroup) :
    (tower).map f = (tower).map g := by
  let := auxiliaryStarRing D C
  have hf : ((indexFunctor).map f).element⁻¹ * ((indexFunctor).map g).element ∈
      ((indexFunctor).obj V).subgroup := by
    change (scalarEquiv f.element)⁻¹ * scalarEquiv g.element ∈ _
    rw [← map_inv, ← map_mul]
    exact (hodgeLevelFunctor_obj_mem D C V _).mpr hfg
  have e := PolarizedWeilLevel.isoClassTower_map_eq_of_target_coset preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity
    ((indexFunctor).map f) ((indexFunctor).map g) hf
  ext q
  apply Subtype.ext
  apply Subtype.ext
  exact ConcreteCategory.congr_hom e q.val.val

end HarrisNumericalWeilLevel

namespace HarrisTaylorCMWeilLevel

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


open Langlands.AlgebraicGeometry

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

section Geometric

variable {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S] [ConnectedSpace S] [IsLocallyNoetherian S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "geoTower" => geometricClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h htor hu additivity
local notation "familyTower" => compatibleGeometricFamilyTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  p compatibility h htor hu additivity

omit [ConnectedSpace S] [IsLocallyNoetherian S] in
/-- Target-coset equality at every actual geometric point, with its own field. -/
theorem geometricClassTower_map_eq_of_target_coset {U V : HarrisLevel D} (f g : U ⟶ V)
    (hfg : f.element⁻¹ * g.element ∈ V.subgroup) (a : HarrisGeometricPoint S) :
    (geoTower a).map f = (geoTower a).map g :=
  HarrisNumericalWeilLevel.isoClassTower_map_eq_of_target_coset D C
    (isCMSection_harrisCMSection E (algebraMap L F) τ₀) preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C p) compatibility h a.hom a.finiteFibers htor hu
    additivity L p f g hfg

/-- Equality descends to the compatible family over all actual geometric points. -/
theorem compatibleGeometricFamilyTower_map_eq_of_target_coset
    {U V : HarrisLevel D} (f g : U ⟶ V)
    (hfg : f.element⁻¹ * g.element ∈ V.subgroup) :
    (familyTower).map f = (familyTower).map g := by
  ext x
  apply Subtype.ext
  funext a
  exact ConcreteCategory.congr_hom
    (geometricClassTower_map_eq_of_target_coset D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor
      p hu additivity f g hfg a) (x.val a)

end Geometric

local notation "unpointed" => unpointedClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor
local notation "disconnected" => disconnectedClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor

/-- Equality on the actual connected admissible CM test schemes. -/
theorem unpointedClassTower_map_eq_of_target_coset {U V : HarrisLevel D} (f g : U ⟶ V)
    (hfg : f.element⁻¹ * g.element ∈ V.subgroup) (X : Bases) :
    (unpointed X).map f = (unpointed X).map g :=
  compatibleGeometricFamilyTower_map_eq_of_target_coset D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor X.obj.hom X.property.torsionUnits X.property.pairAdditivity f g hfg

/-- Equality on the product over actual connected component schemes. -/
theorem disconnectedClassTower_map_eq_of_target_coset {U V : HarrisLevel D} (f g : U ⟶ V)
    (hfg : f.element⁻¹ * g.element ∈ V.subgroup) (X : DisBases) :
    (disconnected X).map f = (disconnected X).map g := by
  ext x
  funext c
  exact ConcreteCategory.congr_hom
    (unpointedClassTower_map_eq_of_target_coset D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor
      f g hfg (componentCMBase D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality X c)) (x c)

/-- Equality of natural transformations of the exact small-level CM presheaves. -/
theorem smallLevelClassPresheafTower_map_eq_of_target_coset
    {U V : SmallCMLevel D} (f g : U ⟶ V)
    (hfg : f.hom.element⁻¹ * g.hom.element ∈ V.obj.subgroup) :
    (moduli).map f = (moduli).map g := by
  ext X x
  exact ConcreteCategory.congr_hom
    (disconnectedClassTower_map_eq_of_target_coset D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor
      f.hom g.hom hfg X.unop) x

/-- The target-coset relation on the original sufficiently small transporter arrows. -/
def smallCMTargetCosetSetoid (U V : SmallCMLevel D) : Setoid (U ⟶ V) :=
  (CompactOpenLevel.targetCosetSetoid U.obj V.obj).comap (fun f => f.hom)

/-- Genuine small-level transporters modulo the target right coset. -/
abbrev SmallCMTargetCosetArrow (U V : SmallCMLevel D) :=
  Quotient (smallCMTargetCosetSetoid D U V)

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R
local notation "schemeTower" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R

/-- Exact Yoneda recovery preserves the proved target-coset equality. -/
theorem representedCMBaseTower_map_eq_of_target_coset
    {U V : SmallCMLevel D} (f g : U ⟶ V)
    (hfg : f.hom.element⁻¹ * g.hom.element ∈ V.obj.subgroup) :
    (baseTower).map f = (baseTower).map g := by
  dsimp only [representedCMBaseTower]
  rw [smallLevelClassPresheafTower_map_eq_of_target_coset D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor f g hfg]

/-- The actual scheme transitions depend only on the target right coset. -/
theorem representedCMSchemeTower_map_eq_of_target_coset
    {U V : SmallCMLevel D} (f g : U ⟶ V)
    (hfg : f.hom.element⁻¹ * g.hom.element ∈ V.obj.subgroup) :
    (schemeTower).map f = (schemeTower).map g :=
  congrArg (fun k : (R U).base ⟶ (R V).base => k.hom.left)
    (representedCMBaseTower_map_eq_of_target_coset D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R f g hfg)

/-- The actual represented scheme map descends through target right cosets. -/
def representedCMTargetCosetMap {U V : SmallCMLevel D} :
    SmallCMTargetCosetArrow D U V → ((schemeTower).obj U ⟶ (schemeTower).obj V) :=
  Quotient.lift (fun f => (schemeTower).map f) (fun f g hfg =>
    representedCMSchemeTower_map_eq_of_target_coset D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R f g hfg)

local notation "cosetMap" => representedCMTargetCosetMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R

/-- Evaluation at a genuine transporter recovers its actual scheme transition. -/
@[simp] theorem representedCMTargetCosetMap_mk {U V : SmallCMLevel D} (f : U ⟶ V) :
    cosetMap (Quotient.mk _ f) = (schemeTower).map f := rfl

/-- Every coset-induced map remains over the original CM field. -/
theorem representedCMTargetCosetMap_over {U V : SmallCMLevel D}
    (q : SmallCMTargetCosetArrow D U V) :
    cosetMap q ≫ (R V).base.obj.hom = (R U).base.obj.hom := by
  induction q using Quotient.inductionOn with
  | h f =>
    exact representedCMSchemeTower_over D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R f

/-- An actual target-level element acts trivially on its represented scheme. -/
theorem representedCMSchemeTower_map_eq_id_of_mem {U : SmallCMLevel D} (f : U ⟶ U)
    (hf : f.hom.element ∈ U.obj.subgroup) : (schemeTower).map f = 𝟙 _ := by
  have hfid : f.hom.element⁻¹ * (𝟙 U : U ⟶ U).hom.element ∈ U.obj.subgroup := by
    simpa using U.obj.subgroup.inv_mem hf
  simpa using representedCMSchemeTower_map_eq_of_target_coset D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R f (𝟙 U) hfid

/-- The identity transporter class gives the identity of the actual scheme. -/
@[simp] theorem representedCMTargetCosetMap_id (U : SmallCMLevel D) :
    cosetMap (Quotient.mk _ (𝟙 U)) = 𝟙 _ := by
  simp

/-- Changing exact representing choices commutes with every coset-induced map. -/
theorem representedCMTargetCosetMap_comparison
    (R' : ∀ U : SmallCMLevel D,
      CMLevelRepresentation D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U)
    {U V : SmallCMLevel D} (q : SmallCMTargetCosetArrow D U V) :
    cosetMap q ≫
        (representedCMSchemeTowerComparison D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor R R').hom.app V =
      (representedCMSchemeTowerComparison D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor R R').hom.app U ≫
        representedCMTargetCosetMap D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor R' q := by
  induction q using Quotient.inductionOn with
  | h f =>
    exact (representedCMSchemeTowerComparison D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R R').hom.naturality f

/-- The coset construction specialized to exactly the stated CM existence target. -/
def cmTargetCosetMap
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) {U V : SmallCMLevel D} :
    SmallCMTargetCosetArrow D U V →
      ((cmSchemeTower D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q).obj U ⟶
       (cmSchemeTower D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q).obj V) :=
  representedCMTargetCosetMap D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor (chosenCMLevelRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q)

end HarrisTaylorCMWeilLevel

end PEL
end Langlands.Shimura
