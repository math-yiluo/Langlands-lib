import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareDirectImageStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleHigherProjectionFormulaStatement
import Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement

/-! # Higher direct images of the Mumford coefficient along the parameter projection -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

/-- Tensoring with a zero module sheaf gives a zero module sheaf. -/
lemma isZero_tensorObj_of_isZero_right {X : Scheme.{u}} (M : X.Modules) {Z : X.Modules}
    (hZ : IsZero Z) : IsZero (tensorObj M Z) := by
  have hZv : IsZero ((Scheme.Modules.toPresheafOfModules X).obj Z) :=
    (Scheme.Modules.toPresheafOfModules X).map_isZero hZ
  have hP : IsZero (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      M.val Z.val) := by
    rw [IsZero.iff_id_eq_zero]
    apply PresheafOfModules.hom_ext
    intro U
    have hZU : IsZero (Z.val.obj U) := (PresheafOfModules.evaluation _ U).map_isZero hZv
    have hT : IsZero ((PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
        M.val Z.val).obj U) := by
      let M' : ModuleCat (X.presheaf.obj U) := M.val.obj U
      let Z' : ModuleCat (X.presheaf.obj U) := Z.val.obj U
      have : Subsingleton Z' := ModuleCat.isZero_iff_subsingleton.mp hZU
      have h : Subsingleton (TensorProduct (X.presheaf.obj U) M' Z') := inferInstance
      exact ModuleCat.isZero_iff_subsingleton.mpr h
    exact hT.eq_of_src _ _
  have : (sheafify X).IsLeftAdjoint := (sheafifyAdjunction X).isLeftAdjoint
  exact IsZero.of_iso ((sheafify X).map_isZero hP) (tensorSheafificationIso M Z)

end Langlands.Scheme.Modules

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

section Geometry

variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)

/-- The map `A ×_S A ⟶ A ×_S D` which is `f` on the parameter factor `pullback.fst` and the
identity on the `A`-factor `pullback.snd`, with values in the conventional total space of the
Poincaré bundle. -/
def mumfordDualPoincareMap (f : A.X ⟶ dualScheme A hA) :
    pullback A.X.hom A.X.hom ⟶ pullback A.X.hom (dualScheme A hA).hom :=
  pullback.lift (pullback.snd A.X.hom A.X.hom) (pullback.fst A.X.hom A.X.hom ≫ f.left)
    (by rw [Category.assoc, Over.w f, pullback.condition])

/-- Composed with the symmetry of the product, this map is the relative-space map of `f`. -/
lemma mumfordDualPoincareMap_symmetry (f : A.X ⟶ dualScheme A hA) :
    mumfordDualPoincareMap A hA f ≫ (relativeSpaceSymmetry A.X.hom (dualScheme A hA)).inv =
      (relativeSpace A.X.hom).map f := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    erw [pullbackSymmetry_inv_comp_fst]
    erw [pullback.lift_snd, pullback.lift_fst]
  · rw [Category.assoc]
    erw [pullbackSymmetry_inv_comp_snd]
    erw [pullback.lift_fst, pullback.lift_snd]

/-- The parameter-first self-product is the base change of the Poincaré projection
`A ×_S D ⟶ D` along `f`. -/
lemma mumfordDualPoincareMap_isPullback (f : A.X ⟶ dualScheme A hA) :
    IsPullback (mumfordDualPoincareMap A hA f) (pullback.fst A.X.hom A.X.hom)
      ((baseChange (dualScheme A hA).hom).obj A).X.hom f.left := by
  have t : IsPullback (pullback.fst A.X.hom (dualScheme A hA).hom)
      (pullback.snd A.X.hom (dualScheme A hA).hom) A.X.hom (dualScheme A hA).hom :=
    IsPullback.of_hasPullback _ _
  have s : IsPullback (pullback.snd A.X.hom A.X.hom) (pullback.fst A.X.hom A.X.hom)
      A.X.hom A.X.hom :=
    (IsPullback.of_hasPullback A.X.hom A.X.hom).flip
  have h1 : mumfordDualPoincareMap A hA f ≫ pullback.fst A.X.hom (dualScheme A hA).hom =
      pullback.snd A.X.hom A.X.hom := pullback.lift_fst _ _ _
  have h2 : f.left ≫ (dualScheme A hA).hom = A.X.hom := Over.w f
  have s' : IsPullback (mumfordDualPoincareMap A hA f ≫
      pullback.fst A.X.hom (dualScheme A hA).hom) (pullback.fst A.X.hom A.X.hom) A.X.hom
      (f.left ≫ (dualScheme A hA).hom) := by
    rw [h1, h2]
    exact s
  exact IsPullback.of_right s' (pullback.lift_snd _ _ _) t

/-- The pullback `Λ` of the Poincaré bundle along `mumfordDualPoincareMap`. -/
def mumfordDualPoincarePullback (f : A.X ⟶ dualScheme A hA) :
    LineBundle (pullback A.X.hom A.X.hom) :=
  (LineBundle.pullback (mumfordDualPoincareMap A hA f)).obj (poincareLineBundle A hA)

/-- `Λ` is the line bundle underlying the relative pullback of the Poincaré family along `f`. -/
def mumfordDualPoincarePullbackIso (f : A.X ⟶ dualScheme A hA) :
    mumfordDualPoincarePullback A hA f ≅
      (RigidifiedLineBundle.forget (mumfordSection A)).obj
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          f).obj (poincareFamily A hA)) :=
  LineBundle.pullbackCompEqIso _ _ (mumfordDualPoincareMap_symmetry A hA f) _

end Geometry

section Coefficient

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (L : LineBundle A.X.left) (B : LineBundle S)
variable (evaluationB :
  tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S)
variable (M : LineBundle A.X.left)
variable (evaluation :
  tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
variable (square : MumfordBundlePicardZeroStatement.{u}) (hA : HasDualScheme A)

set_option quotPrecheck false in
/-- The normalized line bundle `N` underlying the normalization of `L`. -/
local notation "NB" => (RigidifiedLineBundle.forget (unitSection A)).obj
  (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A) L B evaluationB)

/-- Coefficient rewrite: `m^* N ⊗ snd^* M ≅ fst^* N ⊗ Λ` on the parameter-first self-product,
for the actual Mumford map `f` of `N`. -/
theorem mumfordDual_coefficient_iso (f : A.X ⟶ dualScheme A hA)
    (hf : f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation
      square hA) :
    Nonempty (LineBundle.tensor preservation
        ((LineBundle.pullback (mumfordAddition A)).obj NB)
        ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj M) ≅
      LineBundle.tensor preservation
        ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj NB)
        (mumfordDualPoincarePullback A hA f)) := by
  subst hf
  have hΛ := LineBundle.isoClass_eq_of_iso (preservation := preservation)
    (mumfordDualPoincarePullbackIso A hA _ ≪≫
      (RigidifiedLineBundle.forget _).mapIso
        (mumfordSchemeMapOfLineBundlePullbackIso preservation A L B evaluationB M evaluation
          square hA))
  rw [mumfordFamilyOfLineBundle_forget] at hΛ
  have hNM : LineBundle.isoClass preservation (LineBundle.tensor preservation NB M) = 1 :=
    (LineBundle.isoClass_eq_of_iso (M := LineBundle.trivial A.X.left)
      (ObjectProperty.isoMk _ evaluation)).trans (LineBundle.isoClass_trivial preservation)
  have hfst := congrArg
    (LineBundle.pullbackHom preservation (pullback.fst A.X.hom A.X.hom)) hNM
  rw [map_one, LineBundle.pullbackHom_isoClass,
    LineBundle.isoClass_eq_of_iso (LineBundle.pullbackTensorObjIso preservation _ _ _),
    LineBundle.isoClass_tensor] at hfst
  apply LineBundle.isoClass_eq_iff.mp
  rw [LineBundle.isoClass_tensor, LineBundle.isoClass_tensor, hΛ]
  change LineBundle.isoClass (X := pullback A.X.hom A.X.hom) preservation
        ((LineBundle.pullback (mumfordAddition A)).obj NB) *
      LineBundle.isoClass preservation
        ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj M) =
    LineBundle.isoClass preservation
      ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj NB) *
    (LineBundle.isoClass (X := pullback A.X.hom A.X.hom) preservation
        ((LineBundle.pullback (mumfordAddition A)).obj NB) *
      LineBundle.isoClass preservation
        ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj M) *
      LineBundle.isoClass preservation
        ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj M))
  calc _ = (LineBundle.isoClass preservation
        ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj NB) *
      LineBundle.isoClass preservation
        ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj M)) *
      (LineBundle.isoClass (X := pullback A.X.hom A.X.hom) preservation
        ((LineBundle.pullback (mumfordAddition A)).obj NB) *
      LineBundle.isoClass preservation
        ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj M)) := by
        rw [hfst, one_mul]
    _ = _ := by ac_rfl

end Coefficient

section DirectImages

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (K : Type u) [Field K] [IsAlgClosed K]
variable (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
variable (L : LineBundle A.X.left) (B : LineBundle (Spec (CommRingCat.of K)))
variable (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
    structureSheaf (Spec (CommRingCat.of K)))
variable (M : LineBundle A.X.left)
variable (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
variable (square : MumfordBundlePicardZeroStatement.{u})

/-- Conditional on the Poincaré direct images, flat base change and the higher projection
formula: along the parameter projection, `Rⁿ p_* Q = 0` for `n ≠ g` and
`R^g p_* Q ≅ N ⊗ f^* (e_D)_* 𝒪`, where `Q = m^* N ⊗ snd^* M`. -/
theorem mumfordDual_higherDirectImage
    (poincare : AlgClosedFieldPoincareDirectImageStatement.{u})
    (flatBaseChange : FlatHigherDirectImageBaseChangeStatement.{u})
    (projection : LineBundleHigherProjectionFormulaStatement.{u})
    (f : A.X ⟶ dualScheme A hA)
    (hf : f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation
      square hA)
    (hflat : Flat f.left) (g : ℕ) (hg : A.HasRelativeDimension g) :
    (∀ n : ℕ, n ≠ g →
      IsZero ((higherDirectImage (pullback.fst A.X.hom A.X.hom) n).obj
        (tensorObj
          ((Scheme.Modules.pullback (mumfordAddition A)).obj
            (LineBundle.normalize preservation A.X.hom (unitSection A)
              (unitSection_comp A) L B evaluationB).obj.carrier)
          ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)))) ∧
    Nonempty ((higherDirectImage (pullback.fst A.X.hom A.X.hom) g).obj
        (tensorObj
          ((Scheme.Modules.pullback (mumfordAddition A)).obj
            (LineBundle.normalize preservation A.X.hom (unitSection A)
              (unitSection_comp A) L B evaluationB).obj.carrier)
          ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)) ≅
      tensorObj
        (LineBundle.normalize preservation A.X.hom (unitSection A)
          (unitSection_comp A) L B evaluationB).obj.carrier
        ((Scheme.Modules.pullback f.left).obj
          ((Scheme.Modules.pushforward (dualOrigin A hA).left).obj
            (structureSheaf (Spec (CommRingCat.of K)))))) := by
  obtain ⟨e₁⟩ := mumfordDual_coefficient_iso preservation A L B evaluationB M evaluation
    square hA f hf
  obtain ⟨vanishing, ⟨top⟩⟩ := poincare K A hA g hg
  set p := pullback.fst A.X.hom A.X.hom
  set NB := (RigidifiedLineBundle.forget (unitSection A)).obj
    (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A) L B
      evaluationB)
  set Λ := mumfordDualPoincarePullback A hA f
  -- `Rⁿ p_* Q ≅ N ⊗ Rⁿ p_* Λ` by the coefficient rewrite and the projection formula.
  have twist : ∀ n : ℕ, Nonempty ((higherDirectImage p n).obj
      (tensorObj
        ((Scheme.Modules.pullback (mumfordAddition A)).obj NB.obj)
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)) ≅
      tensorObj NB.obj ((higherDirectImage p n).obj Λ.obj)) := by
    intro n
    obtain ⟨e₂⟩ := projection _ _ p NB Λ.obj n
    exact ⟨(higherDirectImage p n).mapIso ((LineBundle.forget _).mapIso e₁) ≪≫ e₂.symm⟩
  -- `Rⁿ p_* Λ ≅ f^* Rⁿ q_* P` by flat base change.
  have base : ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback f.left).obj
      ((higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom n).obj
        (poincareLineBundle A hA).obj) ≅ (higherDirectImage p n).obj Λ.obj) := by
    intro n
    have hqc : QuasiCompact ((baseChange (dualScheme A hA).hom).obj A).X.hom := inferInstance
    have hsep : IsSeparated ((baseChange (dualScheme A hA).hom).obj A).X.hom := inferInstance
    exact flatBaseChange _ _ _ _ _ f.left p (mumfordDualPoincareMap A hA f)
      (mumfordDualPoincareMap_isPullback A hA f) hqc hsep hflat
      (poincareLineBundle A hA).obj (LineBundle.isQuasicoherent (poincareLineBundle A hA)) n
  refine ⟨fun n hn ↦ ?_, ?_⟩
  · obtain ⟨e₃⟩ := twist n
    obtain ⟨e₄⟩ := base n
    refine IsZero.of_iso ?_ e₃
    apply isZero_tensorObj_of_isZero_right
    exact IsZero.of_iso ((Scheme.Modules.pullback f.left).map_isZero (vanishing n hn)) e₄.symm
  · obtain ⟨e₃⟩ := twist g
    obtain ⟨e₄⟩ := base g
    exact ⟨e₃ ≪≫ (Langlands.Scheme.Modules.tensorFunctor _).mapIso
      ((Iso.refl NB.obj).prod (e₄.symm ≪≫ (Scheme.Modules.pullback f.left).mapIso top))⟩

end DirectImages

end Langlands.AbelianScheme
