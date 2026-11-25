/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit

/-! # The one-section Koszul localization colimit

Source: Stacks Project, More on Algebra, Tag 0913.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
private theorem scalar_localization_colimit {R : Type u} [CommRing R] (s : R) :
    let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
      (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))
    ∃ e : colimit D ≅ ModuleCat.of R (Localization.Away s),
      ∀ (m : ℕ) (a : R), e.hom ((colimit.ι D m) a) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ (m + 1) := by
  dsimp only
  obtain ⟨κ, hκ⟩ := ModuleCat.localization_away_colimit s R
  let e := IsLocalizedModule.iso (Submonoid.powers s)
    (Algebra.linearMap R (Localization.Away s))
  have he (a : R) (n : ℕ) :
      e (LocalizedModule.mk (S := Submonoid.powers s) a ⟨s ^ n, ⟨n, rfl⟩⟩) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ n := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit
      (S := Localization.Away s) s n).mul_left_cancel
    calc
      _ = e ((s ^ n) • LocalizedModule.mk (S := Submonoid.powers s)
          a ⟨s ^ n, ⟨n, rfl⟩⟩) := by rw [map_smul, Algebra.smul_def, map_pow]
      _ = algebraMap R _ a := by
        rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s),
          LocalizedModule.mk_cancel]
        exact IsLocalizedModule.iso_mk_one _ _ a
      _ = _ := by rw [mul_left_comm, ← mul_pow,
        IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  let v : Localization.Away s ≃ₗ[R] Localization.Away s :=
    { toFun := fun x ↦ x * IsLocalization.Away.invSelf s
      invFun := fun x ↦ x * algebraMap R _ s
      left_inv := by intro x; dsimp only; rw [mul_assoc, mul_comm _ (algebraMap R _ s),
        IsLocalization.Away.mul_invSelf, mul_one]
      right_inv := by intro x; dsimp only; rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
      map_add' := by intros; exact add_mul _ _ _
      map_smul' := by intros; simp only [Algebra.smul_def, RingHom.id_apply, mul_assoc] }
  refine ⟨(κ.trans (e.trans v)).toModuleIso, ?_⟩
  intro m a
  change v (e (κ ((colimit.ι (Functor.ofSequence (X := fun _ : ℕ ↦
    ModuleCat.of R R) (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))) m) a))) = _
  rw [hκ, he]
  exact (mul_assoc _ _ _).trans (congrArg (algebraMap R _ a * ·) (pow_succ _ m).symm)

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

private abbrev sectionValue
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) : O.obj.obj X := s.val X

private abbrev localizationInv
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    ringedSectionLocalizationCarrier O s X :=
  IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X)

private theorem localization_map_inv
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    ringedSectionLocalizationMap O s g
      (localizationInv O s X) =
        localizationInv O s Y := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (R := O.obj.obj Y) (S := ringedSectionLocalizationCarrier O s Y)
      (sectionValue O s Y)).mul_left_cancel
  have hc (a : O.obj.obj X) :
      ringedSectionLocalizationMap O s g (algebraMap _ _ a) =
        algebraMap _ _ (O.obj.map g a) := by
    exact IsLocalization.Away.lift_eq _ _ a
  calc
    _ = ringedSectionLocalizationMap O s g
        (algebraMap _ _ (sectionValue O s X) * localizationInv O s X) := by
      rw [map_mul, hc, show O.obj.map g (sectionValue O s X) =
          sectionValue O s Y from s.property g]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf (sectionValue O s Y)).symm

private def fractionMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    PresheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj ⟶
      ringedSectionLocalizationPresheaf O s :=
  (ringedSectionLocalizationPresheaf O s).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ localizationInv O s X ^ n)
      (fun {_ _} g ↦ by
        change ringedSectionLocalizationMap O s g _ = _
        rw [map_pow, localization_map_inv]))

private theorem fractionMap_apply
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ)
    (X : Cᵒᵖ) (a : O.obj.obj X) :
    (fractionMap O s n).app X a =
      algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O s X) a *
        localizationInv O s X ^ n := by
  change a • localizationInv O s X ^ n = _
  exact Algebra.smul_def a _

private theorem scalar_apply
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) (a : O.obj.obj X) :
    (ringedKoszulScalar O s).asHom.val.app X a = a * sectionValue O s X := by
  change a • sectionValue O s X = _
  rfl

private theorem fractionMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (ringedKoszulScalar O s).asHom.val ≫ fractionMap O s (n + 1) = fractionMap O s n := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change O.obj.obj X at a
  change (fractionMap O s (n + 1)).app X ((ringedKoszulScalar O s).asHom.val.app X a) =
    (fractionMap O s n).app X a
  rw [fractionMap_apply, scalar_apply, fractionMap_apply, map_mul, pow_succ]
  calc
    _ = (algebraMap _ _ a * localizationInv O s X ^ n) *
        (algebraMap _ _ (sectionValue O s X) * localizationInv O s X) := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

private def localizationPresheafCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ (ringedKoszulScalar O s).asHom) ⋙ SheafOfModules.forget _) where
  pt := ringedSectionLocalizationPresheaf O s
  ι := NatTrans.ofSequence (fun n ↦ fractionMap O s (n + 1)) (by
    intro n
    change ((SheafOfModules.forget _).map
      ((Functor.ofSequence (fun _ ↦ (ringedKoszulScalar O s).asHom)).map _)) ≫ _ = _ ≫ 𝟙 _
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact fractionMap_step O s (n + 1))

private def localizationPresheafCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationPresheafCocone O s) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro X
  let R := O.obj.obj X
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
    (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R (sectionValue O s X)))
  let c := (PresheafOfModules.evaluation _ X).mapCocone
    (localizationPresheafCocone O s)
  let F := (Functor.ofSequence (fun _ ↦ (ringedKoszulScalar O s).asHom) ⋙
    SheafOfModules.forget _) ⋙ PresheafOfModules.evaluation _ X
  let t : D ⟶ F := NatTrans.ofSequence (fun _ ↦ 𝟙 (ModuleCat.of R R)) (by
    intro n
    simp only [F, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change O.obj.obj X at a
    change (sectionValue O s X) * a = (ringedKoszulScalar O s).asHom.val.app X a
    rw [scalar_apply, mul_comm])
  let et : D ≅ F := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro i j f; exact t.naturality f)
  let e := Classical.choose (scalar_localization_colimit (sectionValue O s X))
  have he := Classical.choose_spec (scalar_localization_colimit (sectionValue O s X))
  apply (IsColimit.precomposeHomEquiv et c).toFun
  apply IsColimit.ofIsoColimit (colimit.isColimit D)
  refine Cocone.ext e ?_
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  dsimp only [et, c, Cocone.precompose, localizationPresheafCocone,
    Functor.mapCocone, NatIso.ofComponents, NatTrans.ofSequence] at *
  change e.hom ((colimit.ι D m) a) = (fractionMap O s (m + 1)).app X a
  rw [he, fractionMap_apply]

private def localizationSheafMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalization O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (fractionMap O s n ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app _)

private theorem localizationSheafMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (ringedKoszulScalar O s).asHom ≫ localizationSheafMap O s (n + 1) =
      localizationSheafMap O s n := by
  apply SheafOfModules.hom_ext
  change (ringedKoszulScalar O s).asHom.val ≫ (fractionMap O s (n + 1) ≫ _) = _
  rw [← Category.assoc, fractionMap_step]
  rfl

private def localizationSheafCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ (ringedKoszulScalar O s).asHom)) where
  pt := ringedSectionLocalization O s
  ι := NatTrans.ofSequence (fun n ↦ localizationSheafMap O s (n + 1)) (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    change (ringedKoszulScalar O s).asHom ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact localizationSheafMap_step O s (n + 1))

private def localizationSheafCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationSheafCocone O s) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  let hc := localizationPresheafCoconeIsColimit O s
  let U := SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  refine { desc := fun t ↦ (adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))
           fac := ?_
           uniq := ?_ }
  · intro t n
    apply U.map_injective
    change (fractionMap O s (n + 1) ≫ adj.unit.app _) ≫
      U.map ((adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))) = _
    rw [Category.assoc]
    erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    exact hc.fac (U.mapCocone t) n
  · intro t m hm
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change fractionMap O s (n + 1) ≫ (adj.homEquiv _ _ m) = _
    rw [Adjunction.homEquiv_unit, ← Category.assoc]
    exact congrArg (fun f ↦ U.map f) (hm n)

private theorem localizationSheafMap_zero
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    localizationSheafMap O s 0 = ringedSectionLocalizationUnit O s := by
  unfold localizationSheafMap ringedSectionLocalizationUnit
  congr 2

private theorem localizationSheafMap_pow
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (ringedKoszulScalar O s ^ n).asHom ≫ localizationSheafMap O s n =
      ringedSectionLocalizationUnit O s := by
  induction n with
  | zero => simpa using localizationSheafMap_zero O s
  | succ n ih =>
    rw [pow_succ', End.mul_asHom, Category.assoc, localizationSheafMap_step, ih]

private def factorMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedKoszulFactor O s m ⟶ ringedLocalizationTwoTerm O s :=
  HomologicalComplex.mkHomFromDouble (by decide : (ComplexShape.up ℤ).Rel 0 1)
    (by decide)
    (eqToHom (ringedLocalizationTwoTermX_zero O s).symm)
    (localizationSheafMap O s (m + 1) ≫
      eqToHom (ringedLocalizationTwoTermX_one O s).symm)
    (by
      change eqToHom _ ≫ CochainComplex.of.d _ _ (0 : ℤ) 1 = _
      erw [CochainComplex.of_d]
      simp only [ringedLocalizationTwoTermD, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      change ringedSectionLocalizationUnit O s =
        (ringedKoszulScalar O s ^ (m + 1)).asHom ≫ localizationSheafMap O s (m + 1)
      exact (localizationSheafMap_pow O s (m + 1)).symm)
    (by
      intro n hn
      have hn' : n = 2 := by simpa using hn.symm
      subst n
      change _ ≫ CochainComplex.of.d _ _ (1 : ℤ) 2 = 0
      erw [CochainComplex.of_d]
      simp [ringedLocalizationTwoTermD])

private theorem factorMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedKoszulFactorStep O s m ≫ factorMap O s (m + 1) = factorMap O s m := by
  apply HomologicalComplex.from_double_hom_ext
  · simp [ringedKoszulFactorStep, ringedKoszulFactorStepF, factorMap, Category.assoc]
  · simp [ringedKoszulFactorStep, ringedKoszulFactorStepF, factorMap,
      Category.assoc, localizationSheafMap_step]

private def factorCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) : Cocone (ringedKoszulFactors O s) where
  pt := ringedLocalizationTwoTerm O s
  ι := NatTrans.ofSequence (factorMap O s) (by
    intro m
    rw [show (ringedKoszulFactors O s).map _ = ringedKoszulFactorStep O s m from
      Functor.ofSequence_map_homOfLE_succ _ m, Functor.const_obj_map]
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact factorMap_step O s m)

private def factorCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) : IsColimit (factorCocone O s) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  by_cases h0 : n = 0
  · subst n
    let A := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let E := HomologicalComplex.eval
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
      (ComplexShape.up ℤ) (0 : ℤ)
    let F := ringedKoszulFactors O s ⋙ E
    let t : F ⟶ (Functor.const ℕ).obj A := NatTrans.ofSequence
      (fun m ↦ (HomologicalComplex.doubleXIso₀ (ringedKoszulScalar O s ^ (m + 1)).asHom
        (by decide : (ComplexShape.up ℤ).Rel 0 1)).hom) (by
        intro m
        simp only [F, E, Functor.comp_map, ringedKoszulFactors,
          Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        simp [ringedKoszulFactorStep, ringedKoszulFactorStepF, Category.assoc])
    let e : F ≅ (Functor.const ℕ).obj A := NatIso.ofComponents
      (fun m ↦ HomologicalComplex.doubleXIso₀ (ringedKoszulScalar O s ^ (m + 1)).asHom
        (by decide : (ComplexShape.up ℤ).Rel 0 1)) (by
        intro i j f
        exact t.naturality f)
    let d : Cocone ((Functor.const ℕ).obj A) := Cocone.mk A (𝟙 _)
    have hd : IsColimit d := isColimitConstCocone _ _
    apply IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e d).symm hd)
    refine Cocone.ext (eqToIso (ringedLocalizationTwoTermX_zero O s).symm) ?_
    intro m
    simp [e, d, factorCocone, factorMap]
  · by_cases h1 : n = 1
    · subst n
      let S := Functor.ofSequence (X := fun _ : ℕ ↦
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
          (fun _ ↦ (ringedKoszulScalar O s).asHom)
      let E := HomologicalComplex.eval
        (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (ComplexShape.up ℤ) (1 : ℤ)
      let F := ringedKoszulFactors O s ⋙ E
      let t : F ⟶ S := NatTrans.ofSequence
        (fun m ↦ (HomologicalComplex.doubleXIso₁ (ringedKoszulScalar O s ^ (m + 1)).asHom
          (by decide : (ComplexShape.up ℤ).Rel 0 1) (by decide)).hom) (by
          intro m
          simp only [F, E, S, Functor.comp_map, ringedKoszulFactors,
            Functor.ofSequence_map_homOfLE_succ]
          simp [ringedKoszulFactorStep, ringedKoszulFactorStepF, Category.assoc])
      let e : F ≅ S := NatIso.ofComponents
        (fun m ↦ HomologicalComplex.doubleXIso₁ (ringedKoszulScalar O s ^ (m + 1)).asHom
          (by decide : (ComplexShape.up ℤ).Rel 0 1) (by decide)) (by
          intro i j f
          exact t.naturality f)
      apply IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv e (localizationSheafCocone O s)).symm
          (localizationSheafCoconeIsColimit O s))
      refine Cocone.ext (eqToIso (ringedLocalizationTwoTermX_one O s).symm) ?_
      intro m
      simp [e, localizationSheafCocone, factorCocone, factorMap]
    · have hz : IsZero ((ringedLocalizationTwoTerm O s).X n) := by
        change IsZero (ringedLocalizationTwoTermX O s n)
        simp only [ringedLocalizationTwoTermX, ite_eq_right h0, ite_eq_right h1]
        exact Limits.isZero_zero _
      refine { desc := fun _ ↦ 0
               fac := ?_
               uniq := ?_ }
      · intro t m
        exact (HomologicalComplex.isZero_double_X (ringedKoszulScalar O s ^ (m + 1)).asHom
          (by decide : (ComplexShape.up ℤ).Rel 0 1) n h0 h1).eq_of_src _ _
      · intro t m hm
        exact hz.eq_of_src _ _

/-- The fraction cocone of the one-section Koszul system is a colimit and preserves
its degree-zero augmentation.
Source: Stacks Project, More on Algebra, Tag 0913.
(auxiliary; not a blueprint node).

Proof: in degree zero use the identity cocone on the constant ring module.
In degree one send a section a at stage m to a/s^(m+1). The identity
(sa)/s^(m+2)=a/s^(m+1) proves transition compatibility, while
s^(m+1)a/s^(m+1)=a proves compatibility with the differential. Sectionwise the
fraction maps exhibit localization as the filtered colimit of multiplication by s:
every fraction occurs and an element vanishes exactly when some power of s kills it.
Sheafification preserves this colimit. Outside degrees zero and one use the zero
cocone. Evaluation jointly reflects colimits of complexes, so these degreewise
colimits give the asserted complex colimit. The map in degree zero is the identity,
which proves the augmentation equation. This includes s=0 and s a zero divisor. -/
theorem exists_ringedKoszulFactor_colimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    ∃ ι : ringedKoszulFactors O s ⟶
        (Functor.const ℕ).obj (ringedLocalizationTwoTerm O s),
      Nonempty (IsColimit (Cocone.mk (ringedLocalizationTwoTerm O s) ι)) ∧
        ∀ m, ι.app m ≫ ringedLocalizationTwoTermAugmentation O s =
          ringedKoszulFactorProjection O s m := by
  refine ⟨(factorCocone O s).ι, ⟨factorCoconeIsColimit O s⟩, ?_⟩
  intro m
  change factorMap O s m ≫ ringedLocalizationTwoTermAugmentation O s =
    ringedKoszulFactorProjection O s m
  apply HomologicalComplex.from_double_hom_ext
  · simp [factorMap, ringedLocalizationTwoTermAugmentation,
      ringedLocalizationTwoTermAugmentationF, ringedKoszulFactorProjection,
      ringedKoszulFactorProjectionF]
  · simp [factorMap, ringedLocalizationTwoTermAugmentation,
      ringedLocalizationTwoTermAugmentationF, ringedKoszulFactorProjection,
      ringedKoszulFactorProjectionF]

end CategoryTheory
