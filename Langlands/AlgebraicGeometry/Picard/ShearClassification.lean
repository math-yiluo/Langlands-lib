import Langlands.AlgebraicGeometry.Picard.PoincareSquare
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.DualSchemeTensor
import Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationStatement
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions
import Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Classifying the shear pullback of a Picard-zero family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (B : AbelianScheme S) (hB : HasDualScheme B)

/-- The underlying line bundle of the pullback of the chosen Poincaré family. -/
abbrev poincarePullback {W : Over S} (φ : W ⟶ dualScheme B hB) :
    LineBundle ((relativeSpace B.X.hom).obj W) :=
  (RigidifiedLineBundle.forget _).obj
    ((RigidifiedLineBundle.relativePullback B.X.hom (unitSection B) (unitSection_comp B) φ).obj
      (poincareFamily B hB))

/-- Pulling back a pullback of the Poincaré bundle along a map of parameter schemes. -/
def poincarePullbackComp {V W : Over S} (h : V ⟶ W) (φ : W ⟶ dualScheme B hB) :
    (LineBundle.pullback ((relativeSpace B.X.hom).map h)).obj (poincarePullback B hB φ) ≅
      poincarePullback B hB (h ≫ φ) :=
  LineBundle.pullbackCompEqIso _ _ ((relativeSpace B.X.hom).map_comp h φ).symm
    ((RigidifiedLineBundle.forget _).obj (poincareFamily B hB))

/-- The rigidification identifies the restriction along the section with the trivial
bundle. -/
def rigidificationIso {X S' : Scheme.{u}} {ε : S' ⟶ X} (L : RigidifiedLineBundle ε) :
    (LineBundle.pullback ε).obj ((RigidifiedLineBundle.forget ε).obj L) ≅
      LineBundle.trivial S' :=
  ObjectProperty.isoMk _ L.obj.rigidification.symm

/-- The pullback of a family along the shear map `(t, b, b') ↦ (t, b * b')`. -/
abbrev shearBundle {T : Over S} (L : RigidifiedFamily B T) :
    LineBundle ((relativeSpace B.X.hom).obj (relativeOver B T)) :=
  (LineBundle.pullback (shear B (relativeFst B T) (relativeSnd B T))).obj
    ((RigidifiedLineBundle.forget _).obj L)

lemma unitSection_shear (T : Over S) :
    (relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app (relativeOver B T) ≫
      shear B (relativeFst B T) (relativeSnd B T) = 𝟙 _ := by
  rw [relativeSection_shear]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact (Category.id_comp (pullback.fst T.hom B.X.hom)).symm
  · rw [pullback.lift_snd]
    exact (Category.id_comp (pullback.snd T.hom B.X.hom)).symm

/-- The unit section of `T ×_S B`, as a morphism over `S`. -/
def unitPoint (T : Over S) : T ⟶ relativeOver B T :=
  Over.homMk ((relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app T) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc]
    exact (congrArg (· ≫ T.hom)
      (relativeSection_projection B.X.hom (unitSection B) (unitSection_comp B) T)).trans
        (Category.id_comp _))

@[simp] lemma unitPoint_left_eq_relativeSection (T : Over S) :
    (unitPoint B T).left = (relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app T :=
  rfl

@[reassoc (attr := simp)]
lemma unitPoint_fst (T : Over S) : unitPoint B T ≫ relativeFst B T = 𝟙 T := by
  ext
  exact relativeSection_projection B.X.hom (unitSection B) (unitSection_comp B) T

lemma unitPoint_snd (T : Over S) : unitPoint B T ≫ relativeSnd B T = 1 := by
  ext
  rw [Over.comp_left, one_left]
  exact relativeSection_snd B.X.hom (unitSection B) (unitSection_comp B) T

variable (classification : PicardZeroLineBundleClassificationStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})

include classification stability in
/-- The normalized classification of the shear pullback. -/
theorem exists_shearBundle_iso {T : Over S} (L : RigidifiedFamily B T)
    (hL : IsPicardZeroFamily B L) :
    ∃ φ : relativeOver B T ⟶ dualScheme B hB,
      Nonempty (shearBundle B L ≅ LineBundle.tensor preservation (poincarePullback B hB φ)
        ((LineBundle.pullback ((relativeProjection B.X.hom).app (relativeOver B T))).obj
          ((RigidifiedLineBundle.forget _).obj L))) := by
  obtain ⟨φ, ⟨e⟩⟩ := classification preservation B hB (relativeOver B T) (shearBundle B L)
    (isGeometricallyPicardZero_shear B stability L hL _ _)
  exact ⟨φ, ⟨e ≪≫ LineBundle.tensorIso preservation (Iso.refl _)
    ((LineBundle.pullback _).mapIso
      (LineBundle.pullbackCompEqIso _ _ (unitSection_shear B T) _ ≪≫
        (LineBundle.pullbackId _).app _))⟩⟩

variable {B hB}

/-- Restricting a classification of the shear pullback along a map whose restriction of
the family is trivial. -/
def shearRestrictIso {T : Over S} {L : RigidifiedFamily B T}
    {φ : relativeOver B T ⟶ dualScheme B hB}
    (e : shearBundle B L ≅ LineBundle.tensor preservation (poincarePullback B hB φ)
      ((LineBundle.pullback ((relativeProjection B.X.hom).app (relativeOver B T))).obj
        ((RigidifiedLineBundle.forget _).obj L)))
    {V : Over S} (h : V ⟶ relativeOver B T)
    (t : (LineBundle.pullback h.left).obj ((RigidifiedLineBundle.forget _).obj L) ≅
      LineBundle.trivial V.left) :
    (LineBundle.pullback ((relativeSpace B.X.hom).map h)).obj (shearBundle B L) ≅
      poincarePullback B hB (h ≫ φ) :=
  (LineBundle.pullback _).mapIso e ≪≫ LineBundle.pullbackTensorObjIso preservation _ _ _ ≪≫
    LineBundle.tensorIso preservation (poincarePullbackComp B hB h φ)
      (LineBundle.pullbackCompEqIso _ _ ((relativeProjection B.X.hom).naturality h) _ ≪≫
        (LineBundle.pullbackCompEqIso _ _ rfl _).symm ≪≫
        (LineBundle.pullback _).mapIso t ≪≫ LineBundle.pullbackTrivialIso _) ≪≫
    LineBundle.tensorTrivialIso preservation _

/-- Restricting along the unit section identifies the family with a pullback of the
Poincaré bundle. -/
def unitPointIso {T : Over S} {L : RigidifiedFamily B T}
    {φ : relativeOver B T ⟶ dualScheme B hB}
    (e : shearBundle B L ≅ LineBundle.tensor preservation (poincarePullback B hB φ)
      ((LineBundle.pullback ((relativeProjection B.X.hom).app (relativeOver B T))).obj
        ((RigidifiedLineBundle.forget _).obj L))) :
    (RigidifiedLineBundle.forget _).obj L ≅ poincarePullback B hB (unitPoint B T ≫ φ) :=
  ((LineBundle.pullbackId _).app _).symm ≪≫
    (LineBundle.pullbackCompEqIso _ _ (by
      rw [relativeSpace_map_shear, unitPoint_fst, unitPoint_snd, shear_one,
        CategoryTheory.Functor.map_id]) _).symm ≪≫
    shearRestrictIso preservation e (unitPoint B T) (rigidificationIso L)

variable (B) in
include stability in
/-- Over an algebraically closed field, shearing a Picard-zero family by a point does not
change the isomorphism class of its pullback. -/
theorem nonempty_shear_iso (K : Type u) [Field K] [IsAlgClosed K]
    {s : Spec (CommRingCat.of K) ⟶ S} {T : Over S} (L : RigidifiedFamily B T)
    (hL : IsPicardZeroFamily B L) (a : Over.mk s ⟶ T) (c : Over.mk s ⟶ B.X) :
    Nonempty ((LineBundle.pullback (shear B a c)).obj ((RigidifiedLineBundle.forget _).obj L) ≅
      (LineBundle.pullback ((relativeSpace B.X.hom).map a)).obj
        ((RigidifiedLineBundle.forget _).obj L)) := by
  have hF := stability S B (Over.mk s) T a L hL
  have hT := isTranslationInvariant_of_isGeometricallyPicardZero K ((baseChange s).obj B) hF
  obtain ⟨t⟩ := hT (pointSection B c)
  exact ⟨LineBundle.isoOfPullbackIso (relativeSpaceSymmetry B.X.hom (Over.mk s)).inv
    (shearTranslationIso B a c _ ≪≫ t)⟩

/-- Every line bundle on the spectrum of a field, viewed over `S`, is trivial. -/
lemma nonempty_iso_trivial_overMk (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (F : LineBundle (Over.mk s).left) : Nonempty (F ≅ LineBundle.trivial (Over.mk s).left) :=
  LineBundle.nonempty_iso_trivial_of_unique (X := Spec (CommRingCat.of K)) F

include stability in
/-- At a geometric point of `T ×_S B`, the classifying map of the shear pullback agrees
with its value at the unit point of the same fibre. -/
theorem comp_unitPoint_eq_of_algClosed {T : Over S} {L : RigidifiedFamily B T}
    (hL : IsPicardZeroFamily B L) {φ : relativeOver B T ⟶ dualScheme B hB}
    (e : shearBundle B L ≅ LineBundle.tensor preservation (poincarePullback B hB φ)
      ((LineBundle.pullback ((relativeProjection B.X.hom).app (relativeOver B T))).obj
        ((RigidifiedLineBundle.forget _).obj L)))
    (K : Type u) [Field K] [IsAlgClosed K]
    (x : Spec (CommRingCat.of K) ⟶ (relativeOver B T).left) :
    x ≫ φ.left = x ≫ pullback.fst T.hom B.X.hom ≫ (unitPoint B T).left ≫ φ.left := by
  let U : Over S := Over.mk (x ≫ (relativeOver B T).hom)
  let u : U ⟶ relativeOver B T := Over.homMk x rfl
  let u2 : U ⟶ relativeOver B T := u ≫ relativeFst B T ≫ unitPoint B T
  have h2fst : u2 ≫ relativeFst B T = u ≫ relativeFst B T := by
    simp only [u2, Category.assoc, unitPoint_fst, Category.comp_id]
  have h2snd : u2 ≫ relativeSnd B T = 1 := by
    simp only [u2, Category.assoc, unitPoint_snd, MonObj.comp_one]
  have hshear : (relativeSpace B.X.hom).map u2 ≫ shear B (relativeFst B T) (relativeSnd B T) =
      (relativeSpace B.X.hom).map (u ≫ relativeFst B T) := by
    rw [relativeSpace_map_shear, h2fst, h2snd, shear_one]
  obtain ⟨t1⟩ := nonempty_iso_trivial_overMk K (x ≫ (relativeOver B T).hom)
    ((LineBundle.pullback u.left).obj ((RigidifiedLineBundle.forget _).obj L))
  obtain ⟨t2⟩ := nonempty_iso_trivial_overMk K (x ≫ (relativeOver B T).hom)
    ((LineBundle.pullback u2.left).obj ((RigidifiedLineBundle.forget _).obj L))
  obtain ⟨d⟩ := nonempty_shear_iso B stability K L hL (u ≫ relativeFst B T)
    (u ≫ relativeSnd B T)
  let carrier : poincarePullback B hB (u ≫ φ) ≅ poincarePullback B hB (u2 ≫ φ) :=
    (shearRestrictIso preservation e u t1).symm ≪≫
      LineBundle.pullbackCompEqIso _ _ (relativeSpace_map_shear B u _ _) _ ≪≫ d ≪≫
      (LineBundle.pullbackCompEqIso _ _ hshear _).symm ≪≫
      shearRestrictIso preservation e u2 t2
  have key : u ≫ φ = u2 ≫ φ := by
    apply dualPointClass_injective stability B hB U
    apply Subtype.ext
    exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso preservation
      ((relativeProjection B.X.hom).app U)
      (relativeSection_projection B.X.hom (unitSection B) (unitSection_comp B) U) carrier)
  have h := congrArg (fun k ↦ k.left) key
  simpa only [u2, u, Over.comp_left, Over.homMk_left, relativeFst_left, Category.assoc]
    using h

include stability in
/-- Rigidity: the classifying map of the shear pullback factors through the projection
to the parameter scheme. -/
theorem eq_relativeFst_unitPoint_comp
    (globalFunctions : Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions.{u})
    {T : Over S} {L : RigidifiedFamily B T}
    (hL : IsPicardZeroFamily B L) {φ : relativeOver B T ⟶ dualScheme B hB}
    (e : shearBundle B L ≅ LineBundle.tensor preservation (poincarePullback B hB φ)
      ((LineBundle.pullback ((relativeProjection B.X.hom).app (relativeOver B T))).obj
        ((RigidifiedLineBundle.forget _).obj L))) :
    φ = relativeFst B T ≫ unitPoint B T ≫ φ := by
  have hp : ∀ V : T.left.Opens, IsIso ((pullback.fst T.hom B.X.hom).app V) :=
    globalFunctions _ _ _ inferInstance inferInstance inferInstance
  have hpts : ∀ x : (relativeOver B T).left, φ.left x =
      ((unitPoint B T).left ≫ φ.left) (pullback.fst T.hom B.X.hom x) := by
    intro x
    let κ := (relativeOver B T).left.residueField x
    let x' : Spec (CommRingCat.of (AlgebraicClosure κ)) ⟶ (relativeOver B T).left :=
      Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ))) ≫
        (relativeOver B T).left.fromSpecResidueField x
    have hx : x' default = x := by
      simp only [x', Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply x _
    have key := comp_unitPoint_eq_of_algClosed preservation stability hL e
      (AlgebraicClosure κ) x'
    calc φ.left x = φ.left (x' default) := by rw [hx]
      _ = (x' ≫ φ.left) default := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (x' ≫ pullback.fst T.hom B.X.hom ≫ (unitPoint B T).left ≫ φ.left) default := by
        rw [key]
      _ = ((unitPoint B T).left ≫ φ.left) (pullback.fst T.hom B.X.hom (x' default)) := by
        simp only [Scheme.Hom.comp_apply]
      _ = ((unitPoint B T).left ≫ φ.left) (pullback.fst T.hom B.X.hom x) := by rw [hx]
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, relativeFst_left]
  exact Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions _ _ _
    (pullback.fst T.hom B.X.hom) (unitPoint B T).left φ.left
    (relativeSection_projection B.X.hom (unitSection B) (unitSection_comp B) T) hp hpts

end Langlands.AbelianScheme
