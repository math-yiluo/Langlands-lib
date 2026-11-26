import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelRepresentabilityStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LocalizationBase
import Langlands.AbelianScheme.RelativeIntegralActions
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility

/-! # Ordinary polarized full-level moduli over the Harris base field -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry

variable (F : Type) [Field F] [CharZero F]

local notation "SpecF" => Spec (CommRingCat.of F)
local notation "Tests" => ObjectProperty.FullSubcategory
  (fun T : Over SpecF => IsLocallyNoetherian T.left)
local notation "LocRing" m:max => Localization.Away (m : ℤ)
local notation "LocSpec" m:max => Spec (CommRingCat.of (LocRing m))

/-- Every locally noetherian test over the characteristic-zero field is an
ordinary level base of any fixed positive modulus. -/
def ordinaryFieldTestFunctor (m : ℕ) (hm : 0 < m) : Tests ⥤ LevelBase m where
  obj T := ⟨T.obj.left, T.property, cmBaseTorsionUnit T.obj.hom ⟨m, hm, trivial⟩⟩
  map f := LevelBase.homMk f.hom.left
  map_id _ := rfl
  map_comp _ _ := rfl

variable (P : Prerequisites.{0}) (g d m : ℕ) (hd : 0 < d) (hm : 3 ≤ m)

private theorem positiveModulus {k : ℕ} (hk : 3 ≤ k) : 0 < k :=
  lt_of_lt_of_le (by decide : 0 < 3) hk

local notation "moduliF" =>
  (ordinaryFieldTestFunctor F m (positiveModulus hm)).op ⋙ moduliFunctor P g d m hd hm
local notation "points" => fun X => (locallyNoetherianTestInclusion SpecF).op ⋙ uliftYoneda.{1}.obj X

/-- The ordinary polarized full-level functor represented over `F`, with
its actual quasi-compact structure morphism and projective-space immersion. -/
structure OrdinaryCMFieldModuliRepresentation where
  scheme : Over SpecF
  dim : ℕ
  embedding : scheme.left ⟶ ProjectiveSpace F dim
  isImmersion : IsImmersion embedding
  embedding_comp : embedding ≫ projectiveSpaceToSpec F dim = scheme.hom
  quasiCompact : QuasiCompact scheme.hom
  represents : points scheme ≅ moduliF

local notation "Rep" => OrdinaryCMFieldModuliRepresentation F P g d m hd hm

instance OrdinaryCMFieldModuliRepresentation.isLocallyNoetherian (M : Rep) :
    IsLocallyNoetherian M.scheme.left := by
  let : IsImmersion M.embedding := M.isImmersion
  have h : LocallyOfFiniteType M.scheme.hom :=
    M.embedding_comp ▸
      (inferInstance : LocallyOfFiniteType (M.embedding ≫ projectiveSpaceToSpec F M.dim))
  exact LocallyOfFiniteType.isLocallyNoetherian M.scheme.hom

/-- The actual universal family is represented by a datum in the class of
the identity map on the ordinary representing scheme. -/
def OrdinaryCMFieldModuliRepresentation.universalDatum (M : Rep) :
    Datum P M.scheme.left g d m :=
  let T : Tests := ⟨M.scheme, inferInstance⟩
  Quotient.out (M.represents.hom.app (op T) (ULift.up (𝟙 M.scheme)) :
    Moduli P M.scheme.left g d m)

/-- Every classifying morphism gives the class of the actual pullback of the
chosen universal datum. -/
theorem OrdinaryCMFieldModuliRepresentation.represents_hom_apply
    (M : Rep) (T : Tests) (f : T.obj ⟶ M.scheme) :
    M.represents.hom.app (op T) (ULift.up f) =
      (M.universalDatum.pullback f.left).classOf := by
  let X : Tests := ⟨M.scheme, inferInstance⟩
  let a : T ⟶ X := ObjectProperty.homMk f
  have hn := M.represents.hom.naturality_apply a.op
    (show (points M.scheme).obj (op X) from (ULift.up (𝟙 M.scheme) : ULift.{1} _))
  change M.represents.hom.app (op T) (ULift.up (f ≫ 𝟙 M.scheme)) =
    Moduli.pullback f.left (M.represents.hom.app (op X) (ULift.up (𝟙 M.scheme))) at hn
  rw [Category.comp_id] at hn
  have hc : M.universalDatum.classOf =
      M.represents.hom.app (op X) (ULift.up (𝟙 M.scheme)) := Quotient.out_eq _
  rw [← hc] at hn
  exact hn

private def localizationToField (k : ℕ) (hk : 3 ≤ k) : LocRing k →+* F :=
  IsLocalization.Away.lift (k : ℤ) (g := Int.castRingHom F) (by
    have h : IsUnit (k : F) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (positiveModulus hk).ne')
    simpa using h)

local notation "fieldMap" => Spec.map (CommRingCat.ofHom (localizationToField F m hm))

variable (X : LevelBase m) (π : X.obj ⟶ LocSpec m)

private def fieldPullback : Over SpecF :=
  Over.mk (pullback.snd π fieldMap)

local notation "changed" => fieldPullback F m hm X π
local notation "proj" => pullback.fst π fieldMap

private def fieldPullbackHomEquiv (T : Tests) :
    (T.obj ⟶ changed) ≃ ((ordinaryFieldTestFunctor F m (positiveModulus hm)).obj T ⟶ X) where
  toFun f := LevelBase.homMk (f.left ≫ proj)
  invFun f := Over.homMk
    (pullback.lift f.hom T.obj.hom (LevelBase.localization_hom_ext _ _))
    (pullback.lift_snd _ _ _)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w f).symm
  right_inv f := by
    apply ObjectProperty.hom_ext
    exact pullback.lift_fst _ _ _

private def fieldPullbackRepresents
    (R : uliftYoneda.{1}.obj X ≅ moduliFunctor P g d m hd hm) :
    points changed ≅ moduliF := by
  let tests := (ordinaryFieldTestFunctor F m (positiveModulus hm)).op
  refine (?_ : points changed ≅ tests ⋙ uliftYoneda.{1}.obj X) ≪≫
    Functor.isoWhiskerLeft tests R
  refine NatIso.ofComponents
    (fun T => ((Equiv.ulift.trans (fieldPullbackHomEquiv F m hm X π T.unop)).trans
        Equiv.ulift.symm).toIso) ?_
  intro T T' f
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  apply ObjectProperty.hom_ext
  exact Category.assoc _ _ _

/-- Base change a fine ordinary representer and its immersion from
`Spec ℤ[1/m]` to `Spec F`. The resulting comparison uses all actual maps on
the locally noetherian tests over `F`. -/
def ordinaryCMFieldModuliRepresentation_of_fineModuli
    (hπ : QuasiCompact π) (N : ℕ) (i : X.obj ⟶ ProjectiveSpace (LocRing m) N)
    (hi : IsImmersion i) (hcomp : i ≫ projectiveSpaceToSpec (LocRing m) N = π)
    (R : uliftYoneda.{1}.obj X ≅ moduliFunctor P g d m hd hm) : Rep := by
  letI : Algebra (LocRing m) F := (localizationToField F m hm).toAlgebra
  let sq := IsPullback.of_hasPullback π fieldMap
  let j := ProjectiveSpace.baseChangeLift (R := LocRing m) (B := F) sq i hcomp
  refine
    { scheme := changed
      dim := N
      embedding := j
      isImmersion := ?_
      embedding_comp := ProjectiveSpace.baseChangeLift_toSpec sq i hcomp
      quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) sq hπ
      represents := fieldPullbackRepresents F P g d m hd hm X π R }
  exact MorphismProperty.of_isPullback (P := @IsImmersion)
    (ProjectiveSpace.baseChangeLift_isPullback sq i hcomp) hi

/-- Ordinary representability over the integer localization supplies the
eventual ordinary ambient schemes over the characteristic-zero field. -/
theorem exists_eventualOrdinaryCMFieldModuliRepresentation
    (H : LargeLevelRepresentabilityStatement) (hg : 0 < g) :
    ∃ N : ℕ, ∀ (m : ℕ), N ≤ m → ∀ hm : 3 ≤ m,
      Nonempty (OrdinaryCMFieldModuliRepresentation F P g d m hd hm) := by
  obtain ⟨N, hN⟩ := H P g d hg hd
  refine ⟨N, fun m hm hm3 => ?_⟩
  obtain ⟨X, π, hπ, ⟨N', i, hi, hcomp⟩, ⟨R⟩⟩ := hN m hm hm3
  exact ⟨ordinaryCMFieldModuliRepresentation_of_fineModuli F P g d m hd hm3
    X π hπ N' i hi hcomp R⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
