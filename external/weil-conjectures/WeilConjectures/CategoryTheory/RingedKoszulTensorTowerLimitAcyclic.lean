/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import all WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Inverse-limit acyclicity of the Koszul tower on a K-injective complex

Source: Stacks Project, sites-cohomology.tex, Tags 0A0A and 0941.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
private theorem koszulDiagram_above (m : ℕ) (n : ℤ) (hn : (r : ℤ) < n) :
    IsZero (((ringedKoszulDiagram O r b).obj m).X n) := by
  induction r generalizing n with
  | zero =>
    exact HomologicalComplex.isZero_single_obj_X _ _ _ n (ne_of_gt hn)
  | succ r ih =>
    exact ((biprod_isZero_iff _ _).2
      ⟨ih (fun i ↦ b i.succ) n (by omega),
        ih (fun i ↦ b i.succ) (n - 1) (by omega)⟩).of_iso
          (koszulTensorXIso O (b 0) m _ n)

private theorem koszulDual_bounded (m : ℕ) :
    ∃ a z : ℤ, ∀ n : ℤ, n < a ∨ z < n →
      IsZero (((ringedKoszulDualTower O r b).obj (op m)).X n) := by
  refine ⟨-(r : ℤ), 0, fun n hn ↦ ?_⟩
  have hz : IsZero (((ringedKoszulDiagram O r b).obj m).X (-n)) := by
    rcases hn with hn | hn
    · exact koszulDiagram_above O r b m (-n) (by omega)
    · exact koszulDiagram_nonneg O r b m (-n) (by omega)
  exact ((((SheafOfModules.homFunctor O).flip.obj (SheafOfModules.unit _)).map_isZero
    hz.op)).of_iso (homSingleXIso O _ n)

private theorem koszulDual_split (m : ℕ) (n : ℤ) :
    ∃ N : ℕ,
      ∃ i : (((ringedKoszulDualTower O r b).obj (op m)).X n) ⟶
        ∏ᶜ (fun _ : Fin N ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)),
      ∃ p : (∏ᶜ (fun _ : Fin N ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) ⟶
        (((ringedKoszulDualTower O r b).obj (op m)).X n), i ≫ p = 𝟙 _ := by
  classical
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalClosed (R := O)
  obtain ⟨S, hS, ⟨e⟩⟩ := koszulDiagram_finiteFree O r b m (-n)
  let := hS
  let U : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let d : (((ringedKoszulDualTower O r b).obj (op m)).X n) ≅
      SheafOfModules.free.{u} (R :=
        (sheafCompose J (forget₂ CommRingCat RingCat)).obj O) S :=
    homSingleXIso O _ n ≪≫
      ((SheafOfModules.homFunctor O).flip.obj U).mapIso e.symm.op ≪≫
        SheafOfModules.homObjFreeUnitIso.{u} (R := O) S
  let e' : (((ringedKoszulDualTower O r b).obj (op m)).X n) ≅
      ∏ᶜ (fun _ : Fin (Fintype.card S) ↦ U) :=
    d ≪≫ (biproduct.isoCoproduct (fun _ : S ↦ U)).symm ≪≫
      biproduct.isoProduct _ ≪≫ (Pi.reindex (Fintype.equivFin S).symm (fun _ : S ↦ U)).symm
  exact ⟨Fintype.card S, e'.hom, e'.inv, e'.hom_inv_id⟩

private theorem koszulTensor_level_isKInjective (I : ringedSiteComplex O)
    [I.IsKInjective] (m : ℕ) :
    CochainComplex.IsKInjective
      ((ringedKoszulTensorTowerComplex O r b I).asFunctor.obj (op m)) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  have h := CochainComplex.isKInjective_mapBifunctor_of_bounded_splitFree
    I ((ringedKoszulDualTower O r b).obj (op m))
    (koszulDual_bounded O r b m) (koszulDual_split O r b m)
  have : CochainComplex.IsKInjective (((ringedKoszulTensor O).obj I).obj
      ((ringedKoszulDualTower O r b).obj (op m))) := h
  let e : (((ringedKoszulTensor O).obj I).obj
      ((ringedKoszulDualTower O r b).obj (op m))) ≅
      (ringedKoszulTensorTowerComplex O r b I).asFunctor.obj (op m) :=
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _) (by
      intro n k hnk
      obtain rfl := (show n + 1 = k from hnk)
      change 𝟙 _ ≫ ((ringedKoszulTensorTowerComplex O r b I).d n (n + 1)).app
        (op m) = _ ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id, ringedKoszulTensorTowerComplex,
        CochainComplex.of_d]
      rfl)
  exact CochainComplex.isKInjective_of_iso e

section RoosCriterion

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasCountableProducts A]
  [HasCountableProducts (DerivedCategory.{w} A)]

private theorem productComparison_isIso (K : ℕ → CochainComplex A ℤ)
    [∀ n, (K n).IsKInjective] :
    IsIso (piComparison DerivedCategory.Q.{w} K) := by
  obtain ⟨_, ⟨hp⟩⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit K
  let e := (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor K)).uniqueUpToIso
    (limit.isLimit (Discrete.functor K))
  have hp' := IsLimit.ofIsoLimit hp ((Cone.functoriality _ _).mapIso e)
  have hf : IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ K))
      (fun n ↦ DerivedCategory.Q.map (Pi.π K n))) :=
    (Fan.isLimitMapConeEquiv DerivedCategory.Q K (limit.cone _)) hp'
  have he : piComparison DerivedCategory.Q.{w} K =
      (hf.conePointUniqueUpToIso (productIsProduct _)).hom := by
    apply Pi.hom_ext
    intro n
    exact (piComparison_comp_π _ _ n).trans
      (hf.conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨n⟩).symm
  rw [he]
  infer_instance

private theorem productMap_quasiIso_of_levels
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) [QuasiIso f]
    [∀ n : ℕ, CochainComplex.IsKInjective (X.asFunctor.obj (op n))]
    [∀ n : ℕ, CochainComplex.IsKInjective (Y.asFunctor.obj (op n))] :
    QuasiIso (ExactProductsRoos.product.map f) := by
  let K : ℕ → CochainComplex A ℤ := fun n ↦ X.asFunctor.obj (op n)
  let K' : ℕ → CochainComplex A ℤ := fun n ↦ Y.asFunctor.obj (op n)
  let a : ∀ n : ℕ, K n ⟶ K' n := fun n ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)
  have (n : ℕ) : QuasiIso (a n) :=
    (HomologicalComplex.quasiIso_iff_evaluation f).mp inferInstance (op n)
  have : IsIso (piComparison DerivedCategory.Q.{w} K) := productComparison_isIso K
  have : IsIso (piComparison DerivedCategory.Q.{w} K') := productComparison_isIso K'
  have he : DerivedCategory.Q.{w}.map (ExactProductsRoos.product.map f) ≫
      piComparison DerivedCategory.Q K' =
      piComparison DerivedCategory.Q K ≫ Limits.Pi.map (fun n ↦ DerivedCategory.Q.map (a n)) := by
    apply Pi.hom_ext
    intro n
    calc
      _ = DerivedCategory.Q.map (Limits.Pi.map a ≫ Pi.π K' n) := by
        rw [Category.assoc, piComparison_comp_π, ← Functor.map_comp]
      _ = DerivedCategory.Q.map (Pi.π K n ≫ a n) :=
        congrArg (fun g : (∏ᶜ K) ⟶ K' n ↦ DerivedCategory.Q.map g)
          (Limits.Pi.map_π a n)
      _ = _ := by
        rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc,
          piComparison_comp_π, ← Functor.map_comp]
  have hc : IsIso (DerivedCategory.Q.{w}.map (ExactProductsRoos.product.map f) ≫
      piComparison DerivedCategory.Q K') := by
    rw [he]
    infer_instance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso A _).mp
    (IsIso.of_isIso_comp_right _ (piComparison DerivedCategory.Q K'))

private theorem fibreMap_quasiIso_of_levels
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) [QuasiIso f]
    [∀ n : ℕ, CochainComplex.IsKInjective (X.asFunctor.obj (op n))]
    [∀ n : ℕ, CochainComplex.IsKInjective (Y.asFunctor.obj (op n))] :
    QuasiIso (ExactProductsRoos.fibre.map f) := by
  have := productMap_quasiIso_of_levels f
  have hc : QuasiIso (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
      (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩) (ExactProductsRoos.arrowMap f)) := by
    rw [ExactProductsRoos.coneArrowMap_eq]
    exact ExactProductsRoos.coneMap_quasiIso _ _ (ExactProductsRoos.arrowMap f)
  exact (CochainComplex.quasiIso_shift_iff _ _).2 hc

variable [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A)]

private theorem comparison_isIso_of_roos
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : ExactProductsRoos.ordinary ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (hη : ∀ K, CochainComplex.IsKInjective K → IsIso (η.app K))
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [∀ n : ℕ, CochainComplex.IsKInjective (X.asFunctor.obj (op n))]
    [QuasiIso (ExactProductsRoos.comparison.app X)] : IsIso (η.app X) := by
  let K := (CochainComplex.kInjectiveResolutionFunctor.{u} (ℕᵒᵖ ⥤ A)).obj X
  let q : X ⟶ K := (CochainComplex.toKInjectiveResolution.{u} (ℕᵒᵖ ⥤ A)).app X
  have : QuasiIso q :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} (ℕᵒᵖ ⥤ A) X).2
  have (n : ℕ) : CochainComplex.IsKInjective (K.asFunctor.obj (op n)) :=
    tower_evaluation_isKInjective A K (op n)
  have := fibreMap_quasiIso_of_levels q
  have := ExactProductsRoos.comparison_quasiIso K
  have hsq := ExactProductsRoos.comparison.naturality q
  have hl : IsIso (DerivedCategory.Q.{w}.map
      (ExactProductsRoos.ordinary.map q) ≫
        DerivedCategory.Q.map (ExactProductsRoos.comparison.app K)) := by
    rw [← Functor.map_comp, hsq, Functor.map_comp]
    infer_instance
  have := IsIso.of_isIso_comp_right
    (DerivedCategory.Q.{w}.map (ExactProductsRoos.ordinary.map q))
    (DerivedCategory.Q.map (ExactProductsRoos.comparison.app K))
  have := hη K inferInstance
  have hn := η.naturality q
  have hiso : IsIso (η.app X ≫ RF.map (DerivedCategory.Q.map q)) := by
    change IsIso (η.app X ≫ (DerivedCategory.Q ⋙ RF).map q)
    rw [← hn]
    change IsIso (DerivedCategory.Q.map (ExactProductsRoos.ordinary.map q) ≫ η.app K)
    infer_instance
  exact IsIso.of_isIso_comp_right (η.app X) (RF.map (DerivedCategory.Q.map q))

end RoosCriterion

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- The ordinary-to-derived inverse-limit comparison is invertible on the actual
Koszul tensor tower of a K-injective coefficient complex.

Source: Stacks Project, sites-cohomology.tex, Tags 0A0A and 0941,
lemma-colim-and-lim-of-duals and lemma-derived-limit-is-ok;
derived.tex, Tag 0949, lemma-colim-hocolim.
(auxiliary; not a blueprint node).

Proof: finite Koszul evaluation identifies the tower with Hom(P_m,I). Its ordinary
limit is Hom(colim P_m,I). The telescope-to-colimit quasi-isomorphism becomes a
quasi-isomorphism after Hom(-,I), and Hom of the telescope is the shifted cone of
one minus shift on the termwise product of Hom(P_m,I). Finite split-perfect tensor
preserves K-injectivity, and termwise products of K-injectives compute derived
products. The Roos calculation for the strict tower therefore identifies the image
of the ordinary limit with its derived inverse limit. To check that this is the
specified comparison, resolve the strict tower by a K-injective tower. Naturality
of D.comparison gives its map on the resolution; the Roos construction commutes
with that map and with the ordinary-limit inclusion. On the resolved tower the
comparison is invertible by D.comparison_isIso, so the square proves the claim.
Equivalently one may first replace I by a homotopy-equivalent termwise-injective
K-injective complex; Hom of the telescope is then the usual exact-product Roos
calculation. No termwise injectivity is assumed of the given I. The empty list is
the constant tower, and the same argument covers zero or invertible generators. -/
theorem ringedKoszulTensorTower_limit_comparison_isIso
    (D : RingedKoszulLimitPresentation O r b) (I : ringedSiteComplex O)
    [I.IsKInjective] :
    IsIso (D.comparison.app (ringedKoszulTensorTowerComplex O r b I)) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A) := tower_grothendieck A
  let : HasCountableProducts (DerivedCategory.{w} A) :=
    ⟨fun _ _ ↦ DerivedCategory.hasLimitsOfShape_discrete A _⟩
  have (n : ℕ) :
      CochainComplex.IsKInjective
        ((ringedKoszulTensorTowerComplex O r b I).asFunctor.obj (op n)) :=
    koszulTensor_level_isKInjective O r b I n
  have := quasiIso_ringedKoszul_roosComparison O r b I
  exact comparison_isIso_of_roos D.inverseLimit D.comparison D.comparison_isIso _

end CategoryTheory
