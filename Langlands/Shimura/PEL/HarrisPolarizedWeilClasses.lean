import Langlands.Shimura.PEL.PolarizedWeilLevelClasses
import Langlands.Shimura.PEL.RationalLieDeterminantClasses

/-! # Harris determinant classes with actual polarizations and Weil levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E F Φ)

/-- The star operation is the constructed positive auxiliary involution,
using the same whole Hodge-positive witness as the regular source form. -/
@[instance_reducible]
def auxiliaryStarRing : StarRing A where
  star := (D.harrisHodgePELAlgebra C).involution
  star_involutive := (D.harrisHodgePELAlgebra C).involution.involutive
  star_mul := (D.harrisHodgePELAlgebra C).involution.map_mul
  star_add := (D.harrisHodgePELAlgebra C).involution.apply_add

omit [IsScalarTower ℚ F A] in
@[simp] theorem auxiliary_star (a : A) :
    letI := auxiliaryStarRing D C
    star a = (D.harrisHodgePELAlgebra C).involution a := rfl

omit [IsScalarTower ℚ F A] in
include D in
private theorem rationalFinite : FiniteDimensional ℚ A := by
  have : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  exact FiniteDimensional.trans ℚ E A

section GeneralStar

variable [StarRing A]

variable
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

local notation "PObj" => PolarizedWeilLevel.PolarizedAction preservation composition
  unitCoherence associativity comparison symmetry stability square universality S A

/-- The actual all-chart Lie/reflex polynomial condition on a polarized object. -/
def ObjectCondition (X : PObj) : Prop :=
  D.HarrisRationalLieDeterminantCondition C hΦ b X.actionObj.abelianScheme X.actionObj.action

local notation "Good" => ObjectCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b

variable
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]

local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "Data" => PolarizedWeilLevel.LevelData preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) s hs htor hu
local notation "tower" => PolarizedWeilLevel.levelTower preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) s hs htor hu

variable
  (additivity : PolarizedWeilLevel.PairAdditivity preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S) (D := A))

local notation "Ambient" => PolarizedWeilLevel.IsoClass preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "ambientClass" => PolarizedWeilLevel.classOf preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "forget" => PolarizedWeilLevel.forgetAction preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "ambientMap" => PolarizedWeilLevel.classMap preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "mapRep" => PolarizedWeilLevel.mapData preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) s hs htor hu

/-- The Harris determinant predicate pulled back along the actual forget-action map. -/
def ClassCondition {K : Level} (q : Ambient K) : Prop :=
  D.HarrisRationalLieDeterminantClassCondition C hΦ b (forget q)

local notation "Condition" => ClassCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity

@[simp] theorem classCondition_classOf {K : Level} (x : Data K) :
    Condition (ambientClass x) ↔ Good x.1 := Iff.rfl

/-- The condition agrees with every actual representative of an ambient class. -/
theorem classCondition_iff_of_classOf_eq {K : Level} (q : Ambient K) (x : Data K)
    (hx : ambientClass x = q) : Condition q ↔ Good x.1 := by
  subst q
  rfl

/-- A satisfying class has an actual geometrically polarized, determinant-compatible
representative carrying a monodromy-fixed compatible level orbit. -/
theorem classCondition_iff_exists {K : Level} (q : Ambient K) :
    Condition q ↔ ∃ x : Data K, ambientClass x = q ∧ Good x.1 := by
  constructor
  · intro hq
    obtain ⟨x, hx⟩ := PolarizedWeilLevel.classOf_surjective preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity K q
    exact ⟨x, hx, (classCondition_iff_of_classOf_eq D C hΦ preservation composition
      unitCoherence associativity comparison symmetry stability square universality b
      compatibility h s hs htor hu additivity q x hx).mp hq⟩
  · rintro ⟨x, hx, hX⟩
    exact (classCondition_iff_of_classOf_eq D C hΦ preservation composition
      unitCoherence associativity comparison symmetry stability square universality b
      compatibility h s hs htor hu additivity q x hx).mpr hX

/-- Actual polarized regular-source Weil-level classes satisfying the Harris determinant condition. -/
def IsoClass (K : Level) := {q : Ambient K // Condition q}

local notation "Classes" => IsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity

/-- A determinant-compatible actual representative defines its restricted class. -/
def classOf {K : Level} (x : Data K) (hx : Good x.1) : Classes K :=
  ⟨ambientClass x, hx⟩

local notation "mkClass" => classOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity

@[simp] theorem classOf_val {K : Level} (x : Data K) (hx : Good x.1) :
    (mkClass x hx).val = ambientClass x := rfl

local notation "Multiple" => PolarizedWeilLevel.Multiple preservation composition unitCoherence
  associativity comparison symmetry stability square universality additivity
local notation "transport" => PolarizedWeilLevel.levelIso preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) s hs htor hu additivity

/-- Restricting the class type retains exactly the actual polarized-isogeny
relation, including rational invertibility and the geometric multiplier equation. -/
theorem classOf_eq_iff {K : Level} (x y : Data K) (hx : Good x.1) (hy : Good y.1) :
    mkClass x hx = mkClass y hy ↔
      ∃ q : ℚˣ, ∃ e : x.1.actionObj ≅ y.1.actionObj,
        ∃ he : Multiple x.1 y.1 q e, transport x.1 y.1 K q e he x.2 = y.2 := by
  rw [Subtype.ext_iff]
  exact PolarizedWeilLevel.classOf_eq_iff preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity

/-- Every restricted class has an actual representative satisfying the determinant condition. -/
theorem classOf_surjective {K : Level} (q : Classes K) :
    ∃ (x : Data K) (hx : Good x.1), mkClass x hx = q := by
  obtain ⟨x, hx, hX⟩ := (classCondition_iff_exists D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h s hs htor hu additivity q.val).mp q.property
  exact ⟨x, hX, Subtype.ext hx⟩

/-- Forget polarization and levels, retaining the actual determinant action class. -/
def forgetDeterminantAction {K : Level} (q : Classes K) :
    D.HarrisRationalLieDeterminantClass C hΦ b := ⟨forget q.val, q.property⟩

local notation "forgetDet" => forgetDeterminantAction D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity

@[simp] theorem forgetDeterminantAction_classOf {K : Level} (x : Data K) (hx : Good x.1) :
    forgetDet (mkClass x hx) =
      D.harrisRationalLieDeterminantClassOf C hΦ b x.1.actionObj hx := rfl

/-- The actual transporter map preserves the condition because it preserves
the actual forgotten action class. -/
theorem classCondition_classMap {K L : Level} (f : K ⟶ L) (q : Ambient K) :
    Condition (ambientMap f q) ↔ Condition q := by
  unfold ClassCondition
  rw [PolarizedWeilLevel.forgetAction_classMap]

/-- Actual transporter maps restrict to the satisfying polarized classes. -/
def classMap {K L : Level} (f : K ⟶ L) (q : Classes K) : Classes L :=
  ⟨ambientMap f q.val, (classCondition_classMap D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h s hs htor hu additivity f q.val).mpr q.property⟩

local notation "mapClass" => classMap D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity

@[simp] theorem classMap_val {K L : Level} (f : K ⟶ L) (q : Classes K) :
    (mapClass f q).val = ambientMap f q.val := rfl

@[simp] theorem classMap_classOf {K L : Level} (f : K ⟶ L)
    (x : Data K) (hx : Good x.1) :
    mapClass f (mkClass x hx) = mkClass (mapRep f x) hx := rfl

@[simp] theorem classMap_id (K : Level) (q : Classes K) :
    mapClass (𝟙 K) q = q := by
  apply Subtype.ext
  exact PolarizedWeilLevel.classMap_id preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity K q.val

theorem classMap_comp {K L M : Level} (f : K ⟶ L) (g : L ⟶ M) (q : Classes K) :
    mapClass (f ≫ g) q = mapClass g (mapClass f q) := by
  apply Subtype.ext
  exact PolarizedWeilLevel.classMap_comp preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity f g q.val

@[simp] theorem forgetDeterminantAction_classMap {K L : Level}
    (f : K ⟶ L) (q : Classes K) : forgetDet (mapClass f q) = forgetDet q := by
  apply Subtype.ext
  exact PolarizedWeilLevel.forgetAction_classMap preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity f q.val

/-- The actual regular-source polarized-isogeny class tower with the Harris determinant restriction. -/
def isoClassTower : Level ⥤ Type 1 where
  obj K := Classes K
  map f := ↾(mapClass f)
  map_id K := by
    ext q
    exact classMap_id D C hΦ preservation composition unitCoherence associativity comparison
      symmetry stability square universality b compatibility h s hs htor hu additivity K q
  map_comp f g := by
    ext q
    exact classMap_comp D C hΦ preservation composition unitCoherence associativity comparison
      symmetry stability square universality b compatibility h s hs htor hu additivity f g q

local notation "restrictedTower" => isoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity
local notation "ambientTower" => PolarizedWeilLevel.isoClassTower preservation composition
  unitCoherence associativity comparison symmetry stability square universality compatibility
  h A (D.harrisHodgePELForm C) s hs htor hu additivity

@[simp] theorem isoClassTower_map_classOf {K L : Level} (f : K ⟶ L)
    (x : Data K) (hx : Good x.1) :
    (restrictedTower).map f (mkClass x hx) = mkClass (mapRep f x) hx := rfl

/-- The restricted tower embeds naturally into the actual ambient polarized tower. -/
def inclusionNatTrans : restrictedTower ⟶ ambientTower where
  app _ := ↾Subtype.val
  naturality {_K _L} _f := rfl

/-- The determinant action class is constant along all actual level arrows. -/
def forgetDeterminantActionNatTrans :
    restrictedTower ⟶
      (Functor.const Level).obj (D.HarrisRationalLieDeterminantClass C hΦ b) where
  app _ := ↾forgetDet
  naturality {K L} f := by
    ext q
    exact forgetDeterminantAction_classMap D C hΦ preservation composition unitCoherence
      associativity comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity f q

/-- The actual level-forgetting map restricts to determinant-compatible classes. -/
def forgetLevel {K L : Level} (hK : K.toSubgroup ≤ L.toSubgroup) :
    Classes K → Classes L := mapClass (CompactOpenLevel.inclusion hK)

/-- Forgetting changes only the actual compatible level orbit. -/
@[simp] theorem forgetLevel_classOf {K L : Level}
    (hK : K.toSubgroup ≤ L.toSubgroup) (X : PObj) (x : (tower X).obj K)
    (hX : Good X) :
    forgetLevel D C hΦ preservation composition unitCoherence associativity comparison
      symmetry stability square universality b compatibility h s hs htor hu additivity hK
      (mkClass ⟨X, x⟩ hX) =
      mkClass ⟨X, Tate.weilAdelicLevelForget preservation composition unitCoherence
        associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
        X.hasDual X.geometry X.inversePoincare X.evaluation X.polarization
        h X.actionObj.action A (D.harrisHodgePELForm C) htor hu hK x⟩ hX := rfl

section Hecke

variable [Module.Finite ℚ A]

local notation "G" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)

/-- The inclusion leg of the actual compact-open intersection span. -/
def heckeLeft (K L : Level) (g : G) :
    Classes (CompactOpenLevel.heckeLevel K L g) → Classes K :=
  mapClass (CompactOpenLevel.heckeLeft K L g)

/-- The actual right-translation leg preserves the determinant restriction. -/
def heckeRight (K L : Level) (g : G) :
    Classes (CompactOpenLevel.heckeLevel K L g) → Classes L :=
  mapClass (CompactOpenLevel.heckeRight K L g)

@[simp] theorem heckeLeft_classOf (K L : Level) (g : G)
    (x : Data (CompactOpenLevel.heckeLevel K L g)) (hx : Good x.1) :
    heckeLeft D C hΦ preservation composition unitCoherence associativity comparison
      symmetry stability square universality b compatibility h s hs htor hu additivity K L g
      (mkClass x hx) = mkClass (mapRep (CompactOpenLevel.heckeLeft K L g) x) hx := rfl

@[simp] theorem heckeRight_classOf (K L : Level) (g : G)
    (x : Data (CompactOpenLevel.heckeLevel K L g)) (hx : Good x.1) :
    heckeRight D C hΦ preservation composition unitCoherence associativity comparison
      symmetry stability square universality b compatibility h s hs htor hu additivity K L g
      (mkClass x hx) = mkClass (mapRep (CompactOpenLevel.heckeRight K L g) x) hx := rfl

/-- The first restricted leg is the actual Weil-level forgetting map on representatives. -/
theorem heckeLeft_representative (K L : Level) (g : G)
    (X : PObj) (x : (tower X).obj (CompactOpenLevel.heckeLevel K L g)) (hX : Good X) :
    heckeLeft D C hΦ preservation composition unitCoherence associativity comparison
      symmetry stability square universality b compatibility h s hs htor hu additivity K L g
      (mkClass ⟨X, x⟩ hX) =
      mkClass ⟨X, Tate.weilAdelicCompactOpenHeckeLeft preservation composition unitCoherence
        associativity comparison symmetry stability compatibility X.hasDual X.geometry
        X.inversePoincare X.evaluation X.polarization h X.actionObj.action A
        (D.harrisHodgePELForm C) s hs htor hu K L g x⟩ hX := rfl

/-- The second restricted leg is actual right translation on compatible frames. -/
theorem heckeRight_representative (K L : Level) (g : G)
    (X : PObj) (x : (tower X).obj (CompactOpenLevel.heckeLevel K L g)) (hX : Good X) :
    heckeRight D C hΦ preservation composition unitCoherence associativity comparison
      symmetry stability square universality b compatibility h s hs htor hu additivity K L g
      (mkClass ⟨X, x⟩ hX) =
      mkClass ⟨X, Tate.weilAdelicCompactOpenHeckeRight preservation composition unitCoherence
        associativity comparison symmetry stability compatibility X.hasDual X.geometry
        X.inversePoincare X.evaluation X.polarization h X.actionObj.action A
        (D.harrisHodgePELForm C) s hs htor hu K L g x⟩ hX := rfl

end Hecke

end GeneralStar

section PositiveStar

variable
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

/-- Actual polarized actions for the constructed positive auxiliary left involution. -/
abbrev PositivePolarizedAction :=
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.PolarizedAction preservation composition unitCoherence associativity
    comparison symmetry stability square universality S A

local notation "PositiveObject" => PositivePolarizedAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (S := S)

/-- The determinant condition on an actual positive-auxiliary polarized action. -/
def PositiveObjectCondition (b : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
    (X : PositiveObject) : Prop :=
  letI := auxiliaryStarRing D C
  ObjectCondition D C hΦ preservation composition unitCoherence associativity comparison
    symmetry stability square universality b X

/-- Ordered-pair dual additivity for these actual polarized actions. -/
def PositivePairAdditivity : Prop :=
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.PairAdditivity preservation composition unitCoherence associativity
    comparison symmetry stability square universality (S := S) (D := A)

variable
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

local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)

/-- Actual positive-auxiliary polarized actions with a fixed compatible level orbit. -/
abbrev PositiveLevelData (K : Level) :=
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.LevelData preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu K

variable
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "PositiveData" => PositiveLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "PositiveGood" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b

/-- Canonical positive-auxiliary regular-source classes, with actual determinant restriction. -/
abbrev PositiveIsoClass (K : Level) :=
  letI := auxiliaryStarRing D C
  IsoClass D C hΦ preservation composition unitCoherence associativity comparison
    symmetry stability square universality b compatibility h s hs htor hu additivity K

local notation "PositiveClasses" => PositiveIsoClass D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity

/-- The canonical-positive class of a determinant-compatible actual representative. -/
def positiveClassOf {K : Level} (x : PositiveData K) (hx : PositiveGood x.1) :
    PositiveClasses K :=
  letI := auxiliaryStarRing D C
  classOf D C hΦ preservation composition unitCoherence associativity comparison
    symmetry stability square universality b compatibility h s hs htor hu additivity x hx

local notation "positiveMk" => positiveClassOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity

theorem positiveClassOf_surjective {K : Level} (q : PositiveClasses K) :
    ∃ (x : PositiveData K) (hx : PositiveGood x.1), positiveMk x hx = q := by
  let := auxiliaryStarRing D C
  exact classOf_surjective D C hΦ preservation composition unitCoherence associativity
    comparison symmetry stability square universality b compatibility h s hs htor hu additivity q

/-- Equality retains the actual rational-isogeny and geometric multiplier criterion. -/
theorem positiveClassOf_eq_iff {K : Level} (x y : PositiveData K)
    (hx : PositiveGood x.1) (hy : PositiveGood y.1) :
    letI := auxiliaryStarRing D C
    positiveMk x hx = positiveMk y hy ↔
      ∃ q : ℚˣ, ∃ e : x.1.actionObj ≅ y.1.actionObj,
        ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
          associativity comparison symmetry stability square universality additivity x.1 y.1 q e,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h
          A (D.harrisHodgePELForm C) s hs htor hu additivity x.1 y.1 K q e he x.2 = y.2 := by
  let := auxiliaryStarRing D C
  exact classOf_eq_iff D C hΦ preservation composition unitCoherence associativity
    comparison symmetry stability square universality b compatibility h s hs htor hu additivity x y hx hy

/-- The canonical positive-auxiliary specialization is a genuine transporter functor. -/
def positiveIsoClassTower : Level ⥤ Type 1 :=
  letI := auxiliaryStarRing D C
  isoClassTower D C hΦ preservation composition unitCoherence associativity comparison
    symmetry stability square universality b compatibility h s hs htor hu additivity

local notation "positiveTower" => positiveIsoClassTower D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity

@[simp] theorem positiveIsoClassTower_obj (K : Level) :
    (positiveTower).obj K = PositiveClasses K := rfl

/-- The canonical-positive tower uses the actual compatible-orbit transporter on representatives. -/
@[simp] theorem positiveIsoClassTower_map_classOf {K L : Level} (f : K ⟶ L)
    (x : PositiveData K) (hx : PositiveGood x.1) :
    letI := auxiliaryStarRing D C
    (positiveTower).map f (positiveMk x hx) =
      positiveMk (PolarizedWeilLevel.mapData preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility
        h A (D.harrisHodgePELForm C) s hs htor hu f x) hx := rfl

/-- Forget the actual positive-auxiliary polarization and level data naturally. -/
def positiveForgetDeterminantActionNatTrans :
    positiveTower ⟶
      (Functor.const Level).obj (D.HarrisRationalLieDeterminantClass C hΦ b) :=
  letI := auxiliaryStarRing D C
  forgetDeterminantActionNatTrans D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    s hs htor hu additivity

/-- Natural inclusion into the actual polarized tower with the same positive involution. -/
def positiveInclusionNatTrans :
    letI := auxiliaryStarRing D C
    positiveTower ⟶ PolarizedWeilLevel.isoClassTower preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h
      A (D.harrisHodgePELForm C) s hs htor hu additivity :=
  letI := auxiliaryStarRing D C
  inclusionNatTrans D C hΦ preservation composition unitCoherence associativity comparison
    symmetry stability square universality b compatibility h s hs htor hu additivity

/-- The actual canonical-positive forgetting map for an inclusion of compact-open levels. -/
def positiveForgetLevel {K L : Level} (hK : K.toSubgroup ≤ L.toSubgroup) :
    PositiveClasses K → PositiveClasses L :=
  (positiveTower).map (CompactOpenLevel.inclusion hK)

@[simp] theorem positiveForgetLevel_classOf {K L : Level}
    (hK : K.toSubgroup ≤ L.toSubgroup) (x : PositiveData K) (hx : PositiveGood x.1) :
    letI := auxiliaryStarRing D C
    positiveForgetLevel D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity hK (positiveMk x hx) =
      positiveMk (PolarizedWeilLevel.mapData preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility
        h A (D.harrisHodgePELForm C) s hs htor hu (CompactOpenLevel.inclusion hK) x) hx := rfl

local notation "G" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)

/-- The canonical-positive intersection leg, deriving regular-module finiteness from D. -/
def positiveHeckeLeft (K L : Level) (g : G) :
    letI := rationalFinite D
    PositiveClasses (CompactOpenLevel.heckeLevel K L g) → PositiveClasses K :=
  letI := rationalFinite D
  (positiveTower).map (CompactOpenLevel.heckeLeft K L g)

/-- The canonical-positive right-translation leg at the actual intersection level. -/
def positiveHeckeRight (K L : Level) (g : G) :
    letI := rationalFinite D
    PositiveClasses (CompactOpenLevel.heckeLevel K L g) → PositiveClasses L :=
  letI := rationalFinite D
  (positiveTower).map (CompactOpenLevel.heckeRight K L g)

@[simp] theorem positiveHeckeLeft_classOf (K L : Level) (g : G)
    (x : letI := rationalFinite D
      PositiveData (CompactOpenLevel.heckeLevel K L g)) (hx : PositiveGood x.1) :
    letI := rationalFinite D
    letI := auxiliaryStarRing D C
    positiveHeckeLeft D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h s hs htor hu
      additivity K L g (positiveMk x hx) =
      positiveMk (PolarizedWeilLevel.mapData preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) s hs htor hu (CompactOpenLevel.heckeLeft K L g) x) hx := rfl

@[simp] theorem positiveHeckeRight_classOf (K L : Level) (g : G)
    (x : letI := rationalFinite D
      PositiveData (CompactOpenLevel.heckeLevel K L g)) (hx : PositiveGood x.1) :
    letI := rationalFinite D
    letI := auxiliaryStarRing D C
    positiveHeckeRight D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h s hs htor hu
      additivity K L g (positiveMk x hx) =
      positiveMk (PolarizedWeilLevel.mapData preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) s hs htor hu (CompactOpenLevel.heckeRight K L g) x) hx := rfl

end PositiveStar

omit [IsScalarTower ℚ F A] in
/-- The chosen star and the regular trace form have the actual left-adjoint relation. -/
theorem auxiliary_form_adjoint (a x y : A) :
    letI := auxiliaryStarRing D C
    D.harrisHodgePELForm C (a * x) y = D.harrisHodgePELForm C x (star a * y) :=
  D.harrisHodgePELForm_left C a x y

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
