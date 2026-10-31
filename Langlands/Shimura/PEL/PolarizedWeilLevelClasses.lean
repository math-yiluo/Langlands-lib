import Langlands.AbelianScheme.RationalAlgebraActionClasses
import Langlands.AlgebraicGeometry.Picard.RelativePolarization
import Langlands.AlgebraicGeometry.Picard.RationalPolarizationCompatibility
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevels
import Langlands.AbelianScheme.Tate.WeilLevelIsogenyCoherence
import Langlands.AbelianScheme.Tate.WeilRationalFunctorialityProof

/-! # Isogeny classes of polarized actions with actual Weil levels -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

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
  (S : Scheme.{u}) (D : Type v) [Ring D] [Algebra ℚ D] [StarRing D]

/-- Actual faithful rational action and geometric polarization, with the
constructed dual and the source involution equation. -/
structure PolarizedAction where
  actionObj : RationalAlgebraAction S D
  hasDual : HasDualScheme actionObj.abelianScheme
  geometry : DualSchemeGeometry actionObj.abelianScheme hasDual
  inversePoincare : LineBundle
    ((relativeSpace actionObj.abelianScheme.X.hom).obj
      (dualScheme actionObj.abelianScheme hasDual))
  evaluation : tensorObj (poincareFamily actionObj.abelianScheme hasDual).obj.carrier
      inversePoincare.obj ≅
    structureSheaf ((relativeSpace actionObj.abelianScheme.X.hom).obj
      (dualScheme actionObj.abelianScheme hasDual))
  dualEndAdditivity : DualSchemeMapAdditivity preservation stability
    actionObj.abelianScheme actionObj.abelianScheme hasDual hasDual
  polarization : actionObj.abelianScheme ⟶
    dualAbelianSchemeFromEvaluation actionObj.abelianScheme hasDual geometry preservation
      inversePoincare evaluation stability composition unitCoherence associativity
      comparison symmetry
  isPolarization : IsPolarization preservation square universality actionObj.abelianScheme
    hasDual geometry inversePoincare evaluation stability composition unitCoherence
    associativity comparison symmetry polarization
  faithful : Function.Injective actionObj.action
  involutionCompatible : IsInvolutionCompatible preservation composition unitCoherence
    associativity comparison symmetry stability hasDual dualEndAdditivity inversePoincare
    evaluation geometry actionObj.action.toRingHom (Rationalization.ofHom polarization)

local notation "PObj" => PolarizedAction preservation composition unitCoherence
  associativity comparison symmetry stability square universality S D

variable {S D}
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

/-- The actual compact-open Weil level tower attached to a polarized action. -/
def levelTower (X : PObj) : FiniteAdelicScalarExtensionLevel D V ψ ⥤ Type (max u w) :=
  weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
    comparison symmetry stability compatibility X.hasDual X.geometry X.inversePoincare
    X.evaluation X.polarization h X.actionObj.action V ψ s hs htor hu

local notation "tower" => levelTower preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu
local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ

/-- An actual polarized action and a geometrically fixed orbit of actual compatible frames. -/
abbrev LevelData (K : LevelIndex) := Σ X : PObj, (tower X).obj K

local notation "Data" => LevelData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu

/-- Explicit ordered-pair additivity of the actual constructed dual maps. -/
def PairAdditivity : Prop := ∀ X Y : PObj,
  DualSchemeMapAdditivity preservation stability X.actionObj.abelianScheme
    Y.actionObj.abelianScheme X.hasDual Y.hasDual

variable (additivity : PairAdditivity preservation composition unitCoherence associativity
  comparison symmetry stability square universality (S := S) (D := D))

/-- The actual rational dual-pullback equation, with no replacement pairing hypothesis. -/
def Multiple (X Y : PObj) (q : ℚˣ) (e : X.actionObj ≅ Y.actionObj) : Prop :=
  IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual Y.hasDual X.geometry Y.geometry
    X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation (additivity X Y)
    (q : ℚ) (RationalAlgebraAction.underlyingIso e).hom
    (Rationalization.ofHom X.polarization) (Rationalization.ofHom Y.polarization)

local notation "Mult" => Multiple preservation composition unitCoherence associativity
  comparison symmetry stability square universality additivity

/-- Actual rational-isogeny transport on actual Weil-compatible fixed orbit sets. -/
def levelIso (X Y : PObj) (K : LevelIndex) (q : ℚˣ)
    (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e) :
    (tower X).obj K ≃ (tower Y).obj K :=
  weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison
    symmetry stability X.hasDual Y.hasDual X.geometry Y.geometry X.inversePoincare
    X.evaluation Y.inversePoincare Y.evaluation (additivity X Y)
    X.polarization Y.polarization compatibility rationalWeilFunctoriality
    rationalWeilGeometricTransport h X.actionObj.action Y.actionObj.action V ψ s hs htor hu
    K.toSubgroup q (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines e.hom) he

local notation "transport" => levelIso preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity

omit hμfin hμet [QuasiSeparatedSpace S] in
lemma multiple_refl (X : PObj) : Mult X X 1 (Iso.refl _) :=
  IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    (additivity X X) (Rationalization.ofHom X.polarization)

omit hμfin hμet [QuasiSeparatedSpace S] in
lemma multiple_trans {X Y Z : PObj} {q r : ℚˣ}
    {e : X.actionObj ≅ Y.actionObj} {f : Y.actionObj ≅ Z.actionObj}
    (he : Mult X Y q e) (hf : Mult Y Z r f) : Mult X Z (q * r) (e.trans f) :=
  IsRationalDualPullbackMultiple.comp preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual Y.hasDual X.geometry Y.geometry
    X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation (additivity X Y)
    Z.hasDual Z.geometry Z.inversePoincare Z.evaluation (additivity Y Z) (additivity X Z)
    (q : ℚ) (r : ℚ) (RationalAlgebraAction.underlyingIso e).hom
    (RationalAlgebraAction.underlyingIso f).hom
    (Rationalization.ofHom X.polarization) (Rationalization.ofHom Y.polarization)
    (Rationalization.ofHom Z.polarization) he hf

omit hμfin hμet [QuasiSeparatedSpace S] in
lemma multiple_symm {X Y : PObj} {q : ℚˣ} {e : X.actionObj ≅ Y.actionObj}
    (he : Mult X Y q e) : Mult Y X q⁻¹ e.symm :=
  IsRationalDualPullbackMultiple.inv preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual Y.hasDual X.geometry Y.geometry
    X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation (additivity X Y)
    (additivity Y X) (additivity Y Y) q (RationalAlgebraAction.underlyingIso e)
    (Rationalization.ofHom X.polarization) (Rationalization.ofHom Y.polarization) he

@[simp] lemma levelIso_refl (X : PObj) (K : LevelIndex) :
    transport X X K 1 (Iso.refl _)
      (multiple_refl preservation composition unitCoherence associativity comparison symmetry
        stability square universality additivity X) = Equiv.refl _ := by
  exact weilAdelicLevelIsogeny_refl preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    X.polarization (additivity X X) compatibility rationalWeilFunctoriality
    rationalWeilGeometricTransport h X.actionObj.action V ψ s hs htor hu K.toSubgroup

lemma levelIso_trans {X Y Z : PObj} (K : LevelIndex) (q r : ℚˣ)
    (e : X.actionObj ≅ Y.actionObj) (f : Y.actionObj ≅ Z.actionObj)
    (he : Mult X Y q e) (hf : Mult Y Z r f) :
    transport X Z K (q * r) (e.trans f)
      (multiple_trans preservation composition unitCoherence associativity comparison symmetry
        stability square universality additivity he hf) =
      (transport X Y K q e he).trans (transport Y Z K r f hf) := by
  exact weilAdelicLevelIsogenyComp_eq_trans preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    X.polarization Y.hasDual Y.geometry Y.inversePoincare Y.evaluation Y.polarization
    Z.hasDual Z.geometry Z.inversePoincare Z.evaluation Z.polarization
    (additivity X Y) (additivity Y Z) (additivity X Z) compatibility rationalWeilFunctoriality
    rationalWeilGeometricTransport h X.actionObj.action Y.actionObj.action Z.actionObj.action
    V ψ s hs htor hu K.toSubgroup q r (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.underlyingIso f) (RationalAlgebraAction.intertwines e.hom)
    (RationalAlgebraAction.intertwines f.hom) he hf

lemma levelIso_symm {X Y : PObj} (K : LevelIndex) (q : ℚˣ)
    (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e) :
    (transport X Y K q e he).symm = transport Y X K q⁻¹ e.symm
      (multiple_symm preservation composition unitCoherence associativity comparison symmetry
        stability square universality additivity he) := by
  exact weilAdelicLevelIsogeny_symm preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    X.polarization Y.hasDual Y.geometry Y.inversePoincare Y.evaluation Y.polarization
    (additivity X Y) (additivity Y X) (additivity Y Y) compatibility rationalWeilFunctoriality
    rationalWeilGeometricTransport h X.actionObj.action Y.actionObj.action V ψ s hs htor hu
    K.toSubgroup q (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines e.hom) he

/-- Actual isogeny transport commutes with every compact-open transporter arrow. -/
lemma levelIso_map {X Y : PObj} {K L : LevelIndex} (f : K ⟶ L)
    (q : ℚˣ) (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e)
    (x : (tower X).obj K) :
    transport X Y L q e he ((tower X).map f x) =
      (tower Y).map f (transport X Y K q e he x) := by
  exact weilAdelicLevelIsogeny_translate preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual Y.hasDual X.geometry Y.geometry
    X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation (additivity X Y)
    X.polarization Y.polarization compatibility rationalWeilFunctoriality
    rationalWeilGeometricTransport h X.actionObj.action Y.actionObj.action V ψ s hs htor hu
    q (RationalAlgebraAction.underlyingIso e) (RationalAlgebraAction.intertwines e.hom)
    he f.element f.respects x

/-- Equivalence by an actual equivariant rational isogeny carrying the polarization
up to a rational unit and carrying the actual fixed level orbit. -/
def isogenySetoid (K : LevelIndex) : Setoid (Data K) where
  r x y := ∃ q : ℚˣ, ∃ e : x.1.actionObj ≅ y.1.actionObj,
    ∃ he : Mult x.1 y.1 q e, transport x.1 y.1 K q e he x.2 = y.2
  iseqv := by
    constructor
    · rintro ⟨X, x⟩
      refine ⟨1, Iso.refl _, multiple_refl preservation composition unitCoherence
        associativity comparison symmetry stability square universality additivity X, ?_⟩
      rw [levelIso_refl]
      rfl
    · rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨q, e, he, hxy⟩
      refine ⟨q⁻¹, e.symm, multiple_symm preservation composition unitCoherence
        associativity comparison symmetry stability square universality additivity he, ?_⟩
      rw [← levelIso_symm, ← hxy]
      exact Equiv.symm_apply_apply _ _
    · rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨Z, z⟩ ⟨q, e, he, hxy⟩ ⟨r, f, hf, hyz⟩
      refine ⟨q * r, e.trans f, multiple_trans preservation composition unitCoherence
        associativity comparison symmetry stability square universality additivity he hf, ?_⟩
      rw [levelIso_trans]
      exact (congrArg (transport Y Z K r f hf) hxy).trans hyz

local notation "rel" => isogenySetoid preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity

/-- Isogeny classes of actual faithful polarized actions with actual Weil levels. -/
abbrev IsoClass (K : LevelIndex) := Quotient (rel K)

local notation "Classes" => IsoClass preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity

/-- The class of actual polarized action and fixed Weil-compatible level data. -/
def classOf {K : LevelIndex} (x : Data K) : Classes K := Quotient.mk _ x

local notation "mkClass" => classOf preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity

/-- Equality of classes is exactly the stated actual polarized-isogeny relation. -/
theorem classOf_eq_iff {K : LevelIndex} {x y : Data K} :
    mkClass x = mkClass y ↔
      ∃ q : ℚˣ, ∃ e : x.1.actionObj ≅ y.1.actionObj, ∃ he : Mult x.1 y.1 q e,
        transport x.1 y.1 K q e he x.2 = y.2 :=
  Quotient.eq

/-- Every class has an actual faithful polarized abelian-scheme representative. -/
theorem classOf_surjective (K : LevelIndex) :
    Function.Surjective (fun x : Data K => mkClass x) := Quotient.mk_surjective

/-- Forgetting polarization and levels gives the actual rational action class. -/
def forgetAction {K : LevelIndex} : Classes K → RationalAlgebraAction.IsoClass S D :=
  Quotient.lift (fun x => RationalAlgebraAction.classOf x.1.actionObj) (by
    rintro x y ⟨q, e, he, hxy⟩
    exact RationalAlgebraAction.classOf_eq_iff.mpr ⟨e⟩)

local notation "forget" => forgetAction preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity

@[simp] theorem forgetAction_classOf {K : LevelIndex} (x : Data K) :
    forget (mkClass x) = RationalAlgebraAction.classOf x.1.actionObj := rfl

/-- Apply an actual transporter map to the level orbit, retaining the actual geometry. -/
def mapData {K L : LevelIndex} (f : K ⟶ L) (x : Data K) : Data L :=
  ⟨x.1, (tower x.1).map f x.2⟩

local notation "mapRep" => mapData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu

/-- Commutation of actual level transport proves preservation of the isogeny relation. -/
lemma mapData_related {K L : LevelIndex} (f : K ⟶ L) {x y : Data K}
    (hxy : (rel K).r x y) : (rel L).r (mapRep f x) (mapRep f y) := by
  rcases hxy with ⟨q, e, he, hxy⟩
  refine ⟨q, e, he, ?_⟩
  exact (levelIso_map preservation composition unitCoherence associativity comparison symmetry
    stability square universality compatibility h V ψ s hs htor hu additivity f q e he x.2).trans
    (congrArg ((tower y.1).map f) hxy)

/-- Actual compact-open transporter maps descend to the polarized isogeny quotient. -/
def classMap {K L : LevelIndex} (f : K ⟶ L) : Classes K → Classes L :=
  Quotient.map (mapRep f) (fun _ _ hxy =>
    mapData_related preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity f hxy)

local notation "mapClass" => classMap preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity

@[simp] theorem classMap_classOf {K L : LevelIndex} (f : K ⟶ L) (x : Data K) :
    mapClass f (mkClass x) = mkClass (mapRep f x) := rfl

@[simp] theorem classMap_id (K : LevelIndex) (x : Classes K) :
    mapClass (𝟙 K) x = x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨X, x⟩
  change mkClass ⟨X, (tower X).map (𝟙 K) x⟩ = mkClass ⟨X, x⟩
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem classMap_comp {K L M : LevelIndex} (f : K ⟶ L) (g : L ⟶ M)
    (x : Classes K) : mapClass (f ≫ g) x = mapClass g (mapClass f x) := by
  refine Quotient.inductionOn x ?_
  rintro ⟨X, x⟩
  change mkClass ⟨X, (tower X).map (f ≫ g) x⟩ =
    mkClass ⟨X, (tower X).map g ((tower X).map f x)⟩
  rw [Functor.map_comp]
  rfl

/-- Transporter maps preserve the forgotten actual rational action class. -/
@[simp] theorem forgetAction_classMap {K L : LevelIndex} (f : K ⟶ L)
    (x : Classes K) : forget (mapClass f x) = forget x := by
  refine Quotient.inductionOn x ?_
  intro x
  rfl

/-- The actual polarized-isogeny class tower on compact-open transporter levels. -/
def isoClassTower : LevelIndex ⥤ Type (max (u + 1) v w) where
  obj K := Classes K
  map f := ↾(mapClass f)
  map_id K := by
    ext x
    exact classMap_id preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity K x
  map_comp f g := by
    ext x
    exact classMap_comp preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity f g x

local notation "classTower" => isoClassTower preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity

@[simp] theorem isoClassTower_obj (K : LevelIndex) :
    (classTower).obj K = Classes K := rfl

@[simp] theorem isoClassTower_map_classOf {K L : LevelIndex} (f : K ⟶ L) (x : Data K) :
    (classTower).map f (mkClass x) = mkClass (mapRep f x) := rfl

/-- The level tower forgets naturally to a constant actual rational action class. -/
def forgetActionNatTrans :
    classTower ⟶
      (Functor.const LevelIndex).obj (ULift.{w} (RationalAlgebraAction.IsoClass S D)) where
  app _ := ↾(fun x => ULift.up (forget x))
  naturality {K L} f := by
    ext x
    exact congrArg ULift.up (forgetAction_classMap preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h V ψ
      s hs htor hu additivity f x)

/-- The actual class map associated to an inclusion of compact-open levels. -/
def forgetLevel {K L : LevelIndex} (hK : K.toSubgroup ≤ L.toSubgroup) :
    Classes K → Classes L := mapClass (CompactOpenLevel.inclusion hK)

/-- An inclusion forgets only the finer orbit level on an actual representative. -/
@[simp] theorem forgetLevel_classOf {K L : LevelIndex}
    (hK : K.toSubgroup ≤ L.toSubgroup) (X : PObj) (x : (tower X).obj K) :
    forgetLevel preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity hK
      (mkClass ⟨X, x⟩) =
      mkClass ⟨X, weilAdelicLevelForget preservation composition unitCoherence associativity
        comparison symmetry stability compatibility rationalWeilGeometricTransport
        X.hasDual X.geometry X.inversePoincare X.evaluation X.polarization
        h X.actionObj.action V ψ htor hu hK x⟩ := rfl

section Hecke

variable [Module.Finite ℚ V]

local notation "G" => ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ

/-- The first leg of the Hecke span forgets the intersection level on actual classes. -/
def heckeLeft (K L : LevelIndex) (g : G) :
    Classes (CompactOpenLevel.heckeLevel K L g) → Classes K :=
  mapClass (CompactOpenLevel.heckeLeft K L g)

/-- The second leg translates actual compatible frames by the specified similitude. -/
def heckeRight (K L : LevelIndex) (g : G) :
    Classes (CompactOpenLevel.heckeLevel K L g) → Classes L :=
  mapClass (CompactOpenLevel.heckeRight K L g)

@[simp] theorem heckeLeft_classOf (K L : LevelIndex) (g : G)
    (x : Data (CompactOpenLevel.heckeLevel K L g)) :
    heckeLeft preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity K L g
      (mkClass x) = mkClass (mapRep (CompactOpenLevel.heckeLeft K L g) x) := rfl

@[simp] theorem heckeRight_classOf (K L : LevelIndex) (g : G)
    (x : Data (CompactOpenLevel.heckeLevel K L g)) :
    heckeRight preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity K L g
      (mkClass x) = mkClass (mapRep (CompactOpenLevel.heckeRight K L g) x) := rfl

/-- The first Hecke leg uses the published actual Weil-compatible forgetting map. -/
theorem heckeLeft_representative (K L : LevelIndex) (g : G)
    (X : PObj) (x : (tower X).obj (CompactOpenLevel.heckeLevel K L g)) :
    heckeLeft preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity K L g
      (mkClass ⟨X, x⟩) =
      mkClass ⟨X, weilAdelicCompactOpenHeckeLeft preservation composition unitCoherence
        associativity comparison symmetry stability compatibility X.hasDual X.geometry
        X.inversePoincare X.evaluation X.polarization h X.actionObj.action V ψ
        s hs htor hu K L g x⟩ := rfl

/-- The second Hecke leg uses the published actual Weil-compatible right translation. -/
theorem heckeRight_representative (K L : LevelIndex) (g : G)
    (X : PObj) (x : (tower X).obj (CompactOpenLevel.heckeLevel K L g)) :
    heckeRight preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity K L g
      (mkClass ⟨X, x⟩) =
      mkClass ⟨X, weilAdelicCompactOpenHeckeRight preservation composition unitCoherence
        associativity comparison symmetry stability compatibility X.hasDual X.geometry
        X.inversePoincare X.evaluation X.polarization h X.actionObj.action V ψ
        s hs htor hu K L g x⟩ := rfl

end Hecke

end Langlands.Shimura.PEL.PolarizedWeilLevel
