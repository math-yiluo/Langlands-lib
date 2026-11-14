import Langlands.AlgebraicGeometry.Picard.TwoAxisCarrierIsoAbelian
import Langlands.AlgebraicGeometry.Picard.TwoAxisNormalizedBaseChangeExtension
import Langlands.AlgebraicGeometry.Picard.ValuationRingTwoAxisExtensionProof
import Langlands.AlgebraicGeometry.Picard.CartesianSelfProduct
import Langlands.AlgebraicGeometry.Picard.DiscreteValuativeClosedIrreducibleImagesStatement

/-! # Surjectivity of two-axis class restriction over valuation rings -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

namespace TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme TwoAxisFamily

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- If every two-axis-trivial bundle at `T'` is the pullback of a two-axis-trivial bundle
at `T` along the actual product map, then class restriction along `h` is surjective. -/
theorem classesPullback_surjective_of_extension {T' T : Over S} (h : T' ⟶ T)
    (hext : ∀ D : LineBundle (mumfordProduct (abelian A T')).left,
      Nonempty ((Scheme.Modules.pullback (mumfordSection (abelian A T'))).obj D.obj ≅
        structureSheaf (abelian A T').X.left) →
      Nonempty ((Scheme.Modules.pullback (twoAxisSecond (abelian A T'))).obj D.obj ≅
        structureSheaf (abelian A T').X.left) →
      ∃ E : LineBundle (mumfordProduct (abelian A T)).left,
        Nonempty ((Scheme.Modules.pullback (mumfordSection (abelian A T))).obj E.obj ≅
          structureSheaf (abelian A T).X.left) ∧
        Nonempty ((Scheme.Modules.pullback (twoAxisSecond (abelian A T))).obj E.obj ≅
          structureSheaf (abelian A T).X.left) ∧
        Nonempty ((Scheme.Modules.pullback (productMap A h)).obj E.obj ≅ D.obj)) :
    Function.Surjective (classesPullback A h) := by
  intro c
  induction c using Quotient.inductionOn with
  | h D' =>
    obtain ⟨E, hα, hβ, ⟨ψ⟩⟩ := hext ⟨D'.obj.carrier, D'.property⟩
      ⟨D'.obj.rigidification.first.symm⟩ ⟨D'.obj.rigidification.second.symm⟩
    obtain ⟨ρ⟩ := nonempty_twoAxisRigidification (abelian A T) E hα hβ
    refine ⟨Quotient.mk _ (ofLineBundle E ρ), ?_⟩
    obtain ⟨φ⟩ := nonempty_iso_of_carrierIso (abelian A T')
      (L := (relativePullback A h).obj (ofLineBundle E ρ)) (M := D') ψ
    exact Quotient.sound ⟨φ⟩

section Comparison

variable {T : Over S} {W : Scheme.{u}} (b : W ⟶ T.left)

/-- The test-scheme map given by `b`, from the composite test object to `T`. -/
abbrev compTestHom : Over.mk (b ≫ T.hom) ⟶ T := Over.homMk b

/-- The carrier at the composite test object is the iterated base change. -/
def compCarrierIso :
    (abelian A (Over.mk (b ≫ T.hom))).X.left ≅
      ((baseChange b).obj (abelian A T)).X.left where
  hom := pullback.lift (carrierMap A (compTestHom b))
    (abelian A (Over.mk (b ≫ T.hom))).X.hom (carrierMap_snd A (compTestHom b))
  inv := pullback.lift
    (pullback.fst (abelian A T).X.hom b ≫ pullback.fst A.X.hom T.hom)
    (pullback.snd (abelian A T).X.hom b) (by
      have h₁ : pullback.fst A.X.hom T.hom ≫ A.X.hom =
          (abelian A T).X.hom ≫ T.hom := pullback.condition
      have h₂ : pullback.fst (abelian A T).X.hom b ≫ (abelian A T).X.hom =
          pullback.snd (abelian A T).X.hom b ≫ b := pullback.condition
      rw [Category.assoc, h₁, reassoc_of% h₂]
      rfl)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        carrierMap_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      rfl
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, carrierMap_fst, Category.id_comp]
      · have h₂ : pullback.fst (abelian A T).X.hom b ≫ (abelian A T).X.hom =
            pullback.snd (abelian A T).X.hom b ≫ b := pullback.condition
        have h₃ := carrierMap_snd A (compTestHom (T := T) b)
        simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
        change _ ≫ carrierMap A (compTestHom b) ≫ (abelian A T).X.hom = _
        rw [h₃]
        change (pullback.lift _ _ _ ≫ pullback.snd A.X.hom (b ≫ T.hom)) ≫ b = _
        rw [pullback.lift_snd, ← h₂]
        rfl
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma compCarrierIso_hom_fst :
    (compCarrierIso A b).hom ≫ pullback.fst (abelian A T).X.hom b =
      carrierMap A (compTestHom b) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma compCarrierIso_hom_snd :
    (compCarrierIso A b).hom ≫ ((baseChange b).obj (abelian A T)).X.hom =
      (abelian A (Over.mk (b ≫ T.hom))).X.hom :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma compCarrierIso_inv_snd :
    (compCarrierIso A b).inv ≫ (abelian A (Over.mk (b ≫ T.hom))).X.hom =
      ((baseChange b).obj (abelian A T)).X.hom := by
  rw [Iso.inv_comp_eq, compCarrierIso_hom_snd]

lemma unitSection_compCarrierIso :
    unitSection (abelian A (Over.mk (b ≫ T.hom))) ≫ (compCarrierIso A b).hom =
      unitSection ((baseChange b).obj (abelian A T)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, compCarrierIso_hom_fst, unit_naturality]
    exact (unit_fst (abelian A T) (Over.mk b)).symm
  · rw [Category.assoc]
    change unitSection _ ≫ (compCarrierIso A b).hom ≫
        ((baseChange b).obj (abelian A T)).X.hom =
      unitSection ((baseChange b).obj (abelian A T)) ≫
        ((baseChange b).obj (abelian A T)).X.hom
    rw [compCarrierIso_hom_snd, unitSection_comp, unitSection_comp]
    rfl

lemma unitSection_compCarrierIso_inv :
    unitSection ((baseChange b).obj (abelian A T)) ≫ (compCarrierIso A b).inv =
      unitSection (abelian A (Over.mk (b ≫ T.hom))) := by
  rw [← unitSection_compCarrierIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The self-product comparison from the iterated base change to the composite test. -/
abbrev compProductInv :
    (mumfordProduct ((baseChange b).obj (abelian A T))).left ⟶
      (mumfordProduct (abelian A (Over.mk (b ≫ T.hom)))).left :=
  cartesianMumfordProductMap _ _ (compCarrierIso A b).inv (𝟙 W)
    (by rw [compCarrierIso_inv_snd]; exact (Category.comp_id _).symm)

/-- The self-product comparison from the composite test to the iterated base change. -/
abbrev compProductHom :
    (mumfordProduct (abelian A (Over.mk (b ≫ T.hom)))).left ⟶
      (mumfordProduct ((baseChange b).obj (abelian A T))).left :=
  cartesianMumfordProductMap _ _ (compCarrierIso A b).hom (𝟙 W)
    (by rw [compCarrierIso_hom_snd]; exact (Category.comp_id _).symm)

lemma compProductHom_baseChangeMap :
    compProductHom A b ≫ mumfordProductBaseChangeMap (abelian A T) b =
      productMap A (compTestHom b) := by
  have e1 : mumfordProductBaseChangeMap (abelian A T) b ≫
      pullback.fst (abelian A T).X.hom (abelian A T).X.hom =
        pullback.fst ((baseChange b).obj (abelian A T)).X.hom
          ((baseChange b).obj (abelian A T)).X.hom ≫ pullback.fst (abelian A T).X.hom b :=
    pullback.lift_fst _ _ _
  have e2 : mumfordProductBaseChangeMap (abelian A T) b ≫
      pullback.snd (abelian A T).X.hom (abelian A T).X.hom =
        pullback.snd ((baseChange b).obj (abelian A T)).X.hom
          ((baseChange b).obj (abelian A T)).X.hom ≫ pullback.fst (abelian A T).X.hom b :=
    pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, productMap_fst, e1, cartesianSelfProductMap_fst_assoc,
      compCarrierIso_hom_fst]
  · rw [Category.assoc, productMap_snd, e2, cartesianSelfProductMap_snd_assoc,
      compCarrierIso_hom_fst]

lemma compProductHom_inv :
    compProductHom A b ≫ compProductInv A b = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [compProductHom, compProductInv, cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_fst, cartesianSelfProductMap_fst_assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · simp only [compProductHom, compProductInv, cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_snd, cartesianSelfProductMap_snd_assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]

/-- The two self-product comparisons for the composite test object are mutually inverse:
the composite in the order not covered by `compProductHom_inv`. -/
lemma compProductInv_hom :
    compProductInv A b ≫ compProductHom A b = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [compProductHom, compProductInv, cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_fst, cartesianSelfProductMap_fst_assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · simp only [compProductHom, compProductInv, cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_snd, cartesianSelfProductMap_snd_assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- An extension property for the iterated base change along `b` gives the extension
property, with trivial total-space axes, along the test-scheme map `compTestHom b`. -/
theorem extension_compTestHom
    (hb : ∀ D : LineBundle (mumfordProduct ((baseChange b).obj (abelian A T))).left,
      Nonempty ((Scheme.Modules.pullback
        (mumfordSection ((baseChange b).obj (abelian A T)))).obj D.obj ≅
          structureSheaf ((baseChange b).obj (abelian A T)).X.left) →
      Nonempty ((Scheme.Modules.pullback
        (twoAxisSecond ((baseChange b).obj (abelian A T)))).obj D.obj ≅
          structureSheaf ((baseChange b).obj (abelian A T)).X.left) →
      ∃ E : LineBundle (mumfordProduct (abelian A T)).left,
        Nonempty (((LineBundle.pullback
          (mumfordProductBaseChangeMap (abelian A T) b)).obj E).obj ≅ D.obj))
    (D : LineBundle (mumfordProduct (abelian A (Over.mk (b ≫ T.hom)))).left)
    (hα : Nonempty ((Scheme.Modules.pullback
      (mumfordSection (abelian A (Over.mk (b ≫ T.hom))))).obj D.obj ≅
        structureSheaf (abelian A (Over.mk (b ≫ T.hom))).X.left))
    (hβ : Nonempty ((Scheme.Modules.pullback
      (twoAxisSecond (abelian A (Over.mk (b ≫ T.hom))))).obj D.obj ≅
        structureSheaf (abelian A (Over.mk (b ≫ T.hom))).X.left)) :
    ∃ E : LineBundle (mumfordProduct (abelian A T)).left,
      Nonempty ((Scheme.Modules.pullback (mumfordSection (abelian A T))).obj E.obj ≅
        structureSheaf (abelian A T).X.left) ∧
      Nonempty ((Scheme.Modules.pullback (twoAxisSecond (abelian A T))).obj E.obj ≅
        structureSheaf (abelian A T).X.left) ∧
      Nonempty ((Scheme.Modules.pullback (productMap A (compTestHom b))).obj E.obj ≅
        D.obj) := by
  obtain ⟨α⟩ := hα
  obtain ⟨β⟩ := hβ
  have hu : unitSection ((baseChange b).obj (abelian A T)) ≫ (compCarrierIso A b).inv =
      𝟙 W ≫ unitSection (abelian A (Over.mk (b ≫ T.hom))) := by
    rw [Category.id_comp]
    exact unitSection_compCarrierIso_inv A b
  have h₁ : mumfordSection ((baseChange b).obj (abelian A T)) ≫ compProductInv A b =
      (compCarrierIso A b).inv ≫ mumfordSection (abelian A (Over.mk (b ≫ T.hom))) :=
    mumfordSection_cartesianMumfordProductMap _ _ _ _ _ hu
  have h₂ : twoAxisSecond ((baseChange b).obj (abelian A T)) ≫ compProductInv A b =
      (compCarrierIso A b).inv ≫ twoAxisSecond (abelian A (Over.mk (b ≫ T.hom))) :=
    twoAxisSecond_cartesianMumfordProductMap _ _ _ _ _ hu
  let D'' : LineBundle (mumfordProduct ((baseChange b).obj (abelian A T))).left :=
    (LineBundle.pullback (compProductInv A b)).obj D
  let α'' : (Scheme.Modules.pullback
      (mumfordSection ((baseChange b).obj (abelian A T)))).obj D''.obj ≅
        structureSheaf ((baseChange b).obj (abelian A T)).X.left :=
    (Scheme.Modules.pullbackComp _ (compProductInv A b)).app D.obj ≪≫
      (Scheme.Modules.pullbackCongr h₁).app D.obj ≪≫
      ((Scheme.Modules.pullbackComp (compCarrierIso A b).inv _).app D.obj).symm ≪≫
      (Scheme.Modules.pullback (compCarrierIso A b).inv).mapIso α ≪≫
      pullbackUnitIso (compCarrierIso A b).inv
  let β'' : (Scheme.Modules.pullback
      (twoAxisSecond ((baseChange b).obj (abelian A T)))).obj D''.obj ≅
        structureSheaf ((baseChange b).obj (abelian A T)).X.left :=
    (Scheme.Modules.pullbackComp _ (compProductInv A b)).app D.obj ≪≫
      (Scheme.Modules.pullbackCongr h₂).app D.obj ≪≫
      ((Scheme.Modules.pullbackComp (compCarrierIso A b).inv _).app D.obj).symm ≪≫
      (Scheme.Modules.pullback (compCarrierIso A b).inv).mapIso β ≪≫
      pullbackUnitIso (compCarrierIso A b).inv
  obtain ⟨E, ⟨e⟩⟩ := hb D'' ⟨α''⟩ ⟨β''⟩
  let data := twoAxisTrivialExtensionOfExtension (abelian A T) b E D'' e α'' β''
  refine ⟨data.bundle, ⟨data.first⟩, ⟨data.second⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackCongr (compProductHom_baseChangeMap A b).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp (compProductHom A b)
      (mumfordProductBaseChangeMap (abelian A T) b)).app _).symm ≪≫
    (Scheme.Modules.pullback (compProductHom A b)).mapIso data.restrictionIso ≪≫
    (Scheme.Modules.pullbackComp (compProductHom A b) (compProductInv A b)).app D.obj ≪≫
    (Scheme.Modules.pullbackCongr (compProductHom_inv A b)).app D.obj ≪≫
    (Scheme.Modules.pullbackId _).app D.obj

end Comparison

/-- Over any valuation ring mapping to the base, class restriction from the valuation
ring to its supplied fraction field is surjective. -/
theorem classesPullback_surjective_valuationRing (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (i₂ : Spec (CommRingCat.of R) ⟶ S) :
    Function.Surjective (classesPullback A
      (compTestHom (T := Over.mk i₂) (Spec.map (CommRingCat.ofHom (algebraMap R K))))) := by
  apply classesPullback_surjective_of_extension
  intro D hα hβ
  apply extension_compTestHom A _ _ D hα hβ
  intro D'' hα'' hβ''
  exact valuationRingTwoAxisExtension R K (abelian A (Over.mk i₂)) D'' hα'' hβ''

/-- Every representing scheme of the two-axis class presheaf satisfies the existence part
of the valuative criterion, for all valuation rings. -/
theorem valuativeExistence_of_representableBy {Y : Scheme.{u}} (q : Y ⟶ S)
    (e : (classPresheaf A).RepresentableBy (Over.mk q)) :
    ValuativeCriterion.Existence q := by
  intro sq
  let φ := Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
  let g : Over.mk (φ ≫ sq.i₂) ⟶ Over.mk q := Over.homMk sq.i₁ sq.commSq.w
  obtain ⟨c₀, hc₀⟩ := classesPullback_surjective_valuationRing A sq.R sq.K sq.i₂
    (e.homEquiv g)
  let l : Over.mk sq.i₂ ⟶ Over.mk q := e.homEquiv.symm c₀
  have key : compTestHom (T := Over.mk sq.i₂) φ ≫ l = g := by
    apply e.homEquiv.injective
    rw [e.homEquiv_comp, Equiv.apply_symm_apply]
    exact hc₀
  exact ⟨⟨{ l := l.left
            fac_left := congrArg CommaMorphism.left key
            fac_right := Over.w l }⟩⟩

/-- In particular, the discrete valuative existence condition holds. -/
theorem discreteValuativeExistence_of_representableBy {Y : Scheme.{u}} (q : Y ⟶ S)
    (e : (classPresheaf A).RepresentableBy (Over.mk q)) :
    DiscreteValuativeCriterion.Existence q :=
  DiscreteValuativeCriterion.of_valuativeCriterionExistence q
    (valuativeExistence_of_representableBy A q e)

end TwoAxisRigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
