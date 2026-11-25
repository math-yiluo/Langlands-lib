/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-! # Finite Koszul evaluation on the strict inverse tower

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A, lemma-colim-and-lim-of-duals.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

section

variable (O : Sheaf J CommRingCat.{u})

set_option hygiene false in
local notation "𝒜" => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

private noncomputable instance ringedKoszulFiniteHomTowerInst1
    : MonoidalPreadditive 𝒜 := (SheafOfModules.tensorClosed O).1.some

private noncomputable instance ringedKoszulFiniteHomTowerInst2 : IsGrothendieckAbelian.{u} 𝒜 :=
  SheafOfModules.isGrothendieckAbelian _

private noncomputable instance ringedKoszulFiniteHomTowerInst3 : HasColimitsOfSize.{0, 0} 𝒜 :=
  hasColimitsOfSizeShrink.{0, 0, u, u} 𝒜

private noncomputable instance ringedKoszulFiniteHomTowerInst4
    : MonoidalClosed (ringedSiteComplex O) where
  closed P :=
    { rightAdj := CochainComplex.internalHom P
      adj := CochainComplex.tensorHomAdjunction P }

open MonoidalCategory MonoidalClosed

private theorem factor_dualizable
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    IsDualizable (ringedKoszulFactor O s m) := by
  let P := ringedKoszulFactor O s m
  have hzero (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ 1) : IsZero (P.X n) :=
    HomologicalComplex.isZero_double_X _ _ n h₀ h₁
  let : P.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact hzero n (by omega) (by omega)
  let : P.IsStrictlyLE 1 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact hzero n (by omega) (by omega)
  apply CochainComplex.isDualizable_of_isStrictlyGE_of_isStrictlyLE (K := P) 0 1
  intro n
  by_cases h₀ : n = 0
  · subst n
    exact isDualizable_unit.of_iso (HomologicalComplex.doubleXIso₀ _ _).symm
  · by_cases h₁ : n = 1
    · subst n
      exact isDualizable_unit.of_iso
        (HomologicalComplex.doubleXIso₁ _ _ (by decide)).symm
    · exact CategoryTheory.IsZero.isDualizable (hzero n h₀ h₁)

private theorem koszul_dualizable (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    IsDualizable ((ringedKoszulDiagram O r b).obj m) := by
  induction r with
  | zero => exact isDualizable_unit
  | succ r ih =>
    exact (factor_dualizable O (b 0) m).tensorObj (ih (fun i ↦ b i.succ))

private theorem internal_pre_π {P Q : ringedSiteComplex O} (f : P ⟶ Q)
    (M : ringedSiteComplex O) (n p q : ℤ) (h : p + n = q) :
    ((pre f).app M).f n ≫ CochainComplex.internalHomπ P M n p q h =
      CochainComplex.internalHomπ Q M n p q h ≫ (pre (f.f p)).app (M.X q) := by
  have hp : (pre f).app M = CochainComplex.internalHomEquiv P M _
      (f ▷ _ ≫ (CochainComplex.tensorHomAdjunction Q).counit.app M) := by
    rw [← CochainComplex.tensorHomAdjunction_homEquiv]
    change (pre f).app M = curry (f ▷ (ihom Q).obj M ≫ (ihom.ev Q).app M)
    rw [← uncurry_pre f M, curry_uncurry]
  rw [hp]
  change (CochainComplex.internalHomEquiv P M _
    (f ▷ _ ≫ (CochainComplex.tensorHomAdjunction Q).counit.app M)).f n ≫ _ = _
  rw [CochainComplex.internalHomEquiv_f_π, HomologicalComplex.comp_f]
  dsimp only [CochainComplex.internalHom_obj]
  erw [← Category.assoc, CochainComplex.Monoidal.ι_whiskerRight, Category.assoc,
    CochainComplex.tensorHomAdjunction_counit_app,
    CochainComplex.ιTensorObj_internalHomEquiv_symm_f]
  simp only [HomologicalComplex.id_f, Category.id_comp]
  rw [← curry_pre_app, curry_uncurry]

private theorem comparison_pre {P Q : ringedSiteComplex O} (f : P ⟶ Q)
    (M : ringedSiteComplex O) :
    ((homComplexFunctor (R := O)).map f.op).app M ≫
        (homComplexIsoInternalHomObj P M).hom =
      (homComplexIsoInternalHomObj Q M).hom ≫ (pre f).app M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.internalHomObj_hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Category.assoc,
    homComplexIsoInternalHomObj_hom_f_π_assoc,
    homComplexIsoInternalHomObj_hom_f_π, Linear.comp_units_smul,
    internal_pre_π, Linear.units_smul_comp]
  congr 1
  have hm := homComplexFunctor_map_f_π f (𝟙 M) n p q h
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at hm
  exact hm.trans (congrArg (fun g ↦ homComplexπ (R := O) Q M n p q h ≫ g)
    (SheafOfModules.pre_app (R := O) (f.f p) (M.X q)).symm)

private theorem evaluation_pre {P Q : ringedSiteComplex O} (f : P ⟶ Q)
    (M : ringedSiteComplex O) :
    ihomUnitTensorToIhom Q M ≫ (pre f).app M =
      (pre f).app (𝟙_ (ringedSiteComplex O)) ▷ M ≫ ihomUnitTensorToIhom P M := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, id_tensor_pre_app_comp_ev,
    whiskerLeft_ihomUnitTensorToIhom_ev, whisker_exchange_assoc,
    whiskerLeft_ihomUnitTensorToIhom_ev, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, id_tensor_pre_app_comp_ev, comp_whiskerRight_assoc,
    associator_inv_naturality_left_assoc]

private noncomputable def finiteEvaluation (P M : ringedSiteComplex O) :
    M ⊗ homComplex (R := O) P (ringedSiteRingComplex O) ⟶ homComplex (R := O) P M :=
  (β_ M _).hom ≫
    (homComplexIsoInternalHomObj P (ringedSiteRingComplex O)).hom ▷ M ≫
      ihomUnitTensorToIhom P M ≫ (homComplexIsoInternalHomObj P M).inv

private theorem finiteEvaluation_isIso (P M : ringedSiteComplex O)
    (hP : IsDualizable P) : IsIso (finiteEvaluation O P M) := by
  obtain ⟨_⟩ := hP
  let := BraidedCategory.exactPairing_swap P Pᘁ
  let := isIso_ihomUnitTensorToIhom Pᘁ P M
  unfold finiteEvaluation
  infer_instance

private theorem finiteEvaluation_naturality {P Q : ringedSiteComplex O}
    (f : P ⟶ Q) (M : ringedSiteComplex O) :
    M ◁ ((homComplexFunctor (R := O)).map f.op).app (ringedSiteRingComplex O) ≫
        finiteEvaluation O P M =
      finiteEvaluation O Q M ≫ ((homComplexFunctor (R := O)).map f.op).app M := by
  have he := comparison_pre O f (ringedSiteRingComplex O)
  have hm := comparison_pre O f M
  have hm' : (homComplexIsoInternalHomObj Q M).inv ≫
        ((homComplexFunctor (R := O)).map f.op).app M =
      (pre f).app M ≫ (homComplexIsoInternalHomObj P M).inv := by
    rw [← cancel_epi (homComplexIsoInternalHomObj Q M).hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg
        (fun g ↦ g ≫ (homComplexIsoInternalHomObj P M).inv) hm
  unfold finiteEvaluation
  simp only [Category.assoc]
  erw [BraidedCategory.braiding_naturality_right_assoc, ← comp_whiskerRight_assoc,
    he, comp_whiskerRight_assoc,
    ← reassoc_of% (evaluation_pre O f M), ← hm']
  rfl

private noncomputable def towerEvaluation (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    ((ringedKoszulTensorTower O r b).obj M) ⟶
      (ringedKoszulDiagram O r b).op ⋙ (homComplexFunctor (R := O)).flip.obj M where
  app m := finiteEvaluation O ((ringedKoszulDiagram O r b).obj m.unop) M
  naturality {_m _k} f := finiteEvaluation_naturality O
    ((ringedKoszulDiagram O r b).map f.unop) M

private noncomputable def towerTransposeIso (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    (ringedKoszulTensorTower O r b).obj M ≅
      (ringedKoszulTensorTowerComplex O r b M).asFunctor :=
  NatIso.ofComponents (fun m ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ Iso.refl _) (by
      intro n k h
      have hk : n + 1 = k := h
      subst k
      simp [ringedKoszulTensorTowerComplex, CochainComplex.of_d])) (by
        intro m k f
        apply HomologicalComplex.hom_ext
        intro n
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        simp only [Category.comp_id, Category.id_comp]
        rfl)

private theorem finiteHomTower (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    Nonempty ((ringedKoszulDiagram O r b).op ⋙
        (homComplexFunctor (R := O)).flip.obj M ≅
      (ringedKoszulTensorTowerComplex O r b M).asFunctor) := by
  let (m : ℕᵒᵖ) : IsIso ((towerEvaluation O r b M).app m) :=
    finiteEvaluation_isIso O _ M (koszul_dualizable O r b m.unop)
  let : IsIso (towerEvaluation O r b M) := NatIso.isIso_of_isIso_app _
  exact ⟨(asIso (towerEvaluation O r b M)).symm ≪≫ towerTransposeIso O r b M⟩

end

/-- Finite Koszul evaluation identifies the Hom tower with the actual tensor tower,
including every transition map. This involves ordinary complexes and arbitrary
coefficients, and does not assert a quasi-isomorphism or a limit comparison.

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A,
lemma-colim-and-lim-of-duals; more-algebra.tex, Tag 0913.
(auxiliary; not a blueprint node).

Proof: the positive one-generator complex has two rank-one terms. Evaluation
identifies the Hom from either term with the corresponding coefficient term.
For an ordered tensor of r such complexes, expand the finite sums indexed by
subsets of Fin r and evaluate on each rank-one term. In coefficient degree q
and source degree p, include the total-complex sign so that the two differential
terms agree with d(f)=d_I f-(-1)^degree(f) f d_P. Finite sums are also products,
so these component identifications assemble into an invertible chain map from
Hom(P_m,I) to I tensor Hom(P_m,O[0]). Evaluation is natural in the source complex:
precomposition by P_m -> P_(m+1) agrees with tensoring its dual transition map.
Consequently the chain isomorphisms form a natural isomorphism of inverse towers.
The empty list uses evaluation for O[0] and the ordinary tensor unitor. Zero or
invertible generators require no separate argument because evaluation uses no
inversion of a generator. -/
theorem exists_ringedKoszul_finiteHomTower_iso
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (I : ringedSiteComplex O) :
    Nonempty ((ringedKoszulDiagram O r b).op ⋙
        (homComplexFunctor (R := O)).flip.obj I ≅
      (ringedKoszulTensorTowerComplex O r b I).asFunctor) := by
  exact finiteHomTower O r b I

end CategoryTheory
