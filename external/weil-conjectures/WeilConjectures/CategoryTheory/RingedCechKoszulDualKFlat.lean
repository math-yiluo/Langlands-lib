/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import all WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
-- Reuse the private product-projection and internal-Hom zero lemmas.

/-! K-flatness of the finite dual Koszul tower terms.
Source: Stacks Project, More on Algebra, Tag 0913.
(auxiliary; not a blueprint node).
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

-- Only the two supported rows contribute to a total-complex term.
set_option synthInstance.maxSize 2048 in
private noncomputable def totalTwoXIso
    {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]
    [HasBinaryBiproducts A]
    (K : HomologicalComplex₂ A (.up ℤ) (.up ℤ)) [K.HasTotal (.up ℤ)]
    (hz : ∀ p q : ℤ, p ≠ 0 → p ≠ 1 → IsZero ((K.X p).X q)) (n : ℤ) :
    (K.total (.up ℤ)).X n ≅ (K.X 0).X n ⊞ (K.X 1).X (n - 1) := by
  classical
  let f (p q : ℤ) (h : p + q = n) :
      (K.X p).X q ⟶ (K.X 0).X n ⊞ (K.X 1).X (n - 1) :=
    if hp : p = 0 then
      (K.XXIsoOfEq _ _ _ hp (by omega)).hom ≫ biprod.inl
    else if hp : p = 1 then
      (K.XXIsoOfEq _ _ _ hp (by omega)).hom ≫ biprod.inr
    else 0
  let a := K.totalDesc (c₁₂ := .up ℤ) f
  let v := biprod.desc (K.ιTotal (.up ℤ) 0 n n (by simp))
    (K.ιTotal (.up ℤ) 1 (n - 1) n (by change 1 + (n - 1) = n; omega))
  refine ⟨a, v, ?_, ?_⟩
  · apply HomologicalComplex₂.total.hom_ext
    intro p q h
    change p + q = n at h
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
    by_cases hp : p = 0
    · subst p
      have hq : q = n := by omega
      subst q
      simp [f, v]
    · by_cases hp' : p = 1
      · subst p
        have hq : q = n - 1 := by omega
        subst q
        simp [f, v]
      · exact (hz p q hp hp').eq_of_src _ _
  · apply biprod.hom_ext'
    · simp [v, a, f, HomologicalComplex₂.ι_totalDesc]
    · simp [v, a, f, HomologicalComplex₂.ι_totalDesc]

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

-- The two nonzero terms of a Koszul factor are both the tensor unit.
set_option synthInstance.maxSize 2048 in
open MonoidalCategory in
private noncomputable def koszulTensorXIso
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (P : ringedSiteComplex O) (n : ℤ) :
    (((ringedKoszulTensor O).obj (ringedKoszulFactor O s m)).obj P).X n ≅
      P.X n ⊞ P.X (n - 1) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let K := (((curriedTensor A).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj (ringedKoszulFactor O s m)).obj P
  have hz (p q : ℤ) (h₀ : p ≠ 0) (h₁ : p ≠ 1) : IsZero ((K.X p).X q) := by
    exact ((curriedTensor A).flip.obj (P.X q)).map_isZero
      (HomologicalComplex.isZero_double_X _ _ p h₀ h₁)
  change (K.total (.up ℤ)).X n ≅ _
  exact totalTwoXIso K hz n ≪≫ biprod.mapIso
    ((HomologicalComplex.doubleXIso₀ _ _ ⊗ᵢ Iso.refl (P.X n)) ≪≫ λ_ _)
    ((HomologicalComplex.doubleXIso₁ _ _ (by decide) ⊗ᵢ Iso.refl (P.X (n - 1))) ≪≫ λ_ _)

set_option synthInstance.maxSize 2048 in
private theorem koszulDiagram_nonneg (m : ℕ) (n : ℤ) (hn : n < 0) :
    IsZero (((ringedKoszulDiagram O r b).obj m).X n) := by
  induction r generalizing n with
  | zero =>
    exact HomologicalComplex.isZero_single_obj_X _ _ _ n (ne_of_lt hn)
  | succ r ih =>
    exact ((biprod_isZero_iff _ _).2
      ⟨ih (fun i ↦ b i.succ) n hn, ih (fun i ↦ b i.succ) (n - 1) (by omega)⟩).of_iso
        (koszulTensorXIso O (b 0) m _ n)

set_option synthInstance.maxSize 2048 in
private theorem koszulDiagram_finiteFree (m : ℕ) (n : ℤ) :
    ∃ (I : Type u) (_ : Fintype I),
      Nonempty (((ringedKoszulDiagram O r b).obj m).X n ≅
        SheafOfModules.free (R :=
          (sheafCompose J (forget₂ CommRingCat RingCat)).obj O) I) := by
  induction r generalizing n with
  | zero =>
    by_cases hn : n = 0
    · subst n
      refine ⟨PUnit.{u + 1}, inferInstance, ⟨?_⟩⟩
      exact HomologicalComplex.singleObjXSelf (.up ℤ) 0 _ ≪≫
        (coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit _)).symm
    · refine ⟨PEmpty.{u + 1}, inferInstance, ⟨?_⟩⟩
      have hz : IsZero (SheafOfModules.free (R :=
          (sheafCompose J (forget₂ CommRingCat RingCat)).obj O) PEmpty.{u + 1}) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply Sigma.hom_ext
        intro i
        exact PEmpty.elim i
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn).iso hz
  | succ r ih =>
    obtain ⟨I, hI, ⟨eI⟩⟩ := ih (fun i ↦ b i.succ) n
    obtain ⟨T, hT, ⟨eT⟩⟩ := ih (fun i ↦ b i.succ) (n - 1)
    let := hI
    let := hT
    refine ⟨I ⊕ T, inferInstance, ⟨?_⟩⟩
    exact koszulTensorXIso O (b 0) m _ n ≪≫ biprod.mapIso eI eT ≪≫
      biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso I T

-- In Hom(P, O[0])^n, only the product factor indexed by -n survives.
set_option synthInstance.maxSize 2048 in
private noncomputable def homSingleXIso (P : ringedSiteComplex O) (n : ℤ) :
    (homComplex (R := O) P (ringedSiteRingComplex O)).X n ≅
      SheafOfModules.homObj (R := O) (P.X (-n))
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) := by
  classical
  let π := Classical.choose (homComplex_projections_exists (R := O))
  have hc := ((Classical.choose_spec
    (homComplex_projections_exists (R := O))).1 P (ringedSiteRingComplex O) n).some
  have hz (p : ℤ) (hp : p ≠ -n) :
      IsZero (SheafOfModules.homObj (R := O) (P.X p)
        ((ringedSiteRingComplex O).X (p + n))) := by
    apply homObj_isZero_right O
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ (p + n) (by omega)
  have : IsIso (π P (ringedSiteRingComplex O) n (-n) (-n + n) rfl) :=
    fan_projection_isIso _ hc (-n) hz
  let e : (ringedSiteRingComplex O).X (-n + n) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
    eqToIso (congrArg (ringedSiteRingComplex O).X (neg_add_cancel n)) ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 _
  exact asIso (π P (ringedSiteRingComplex O) n (-n) (-n + n) rfl) ≪≫
    ((SheafOfModules.homFunctor O).obj (op (P.X (-n)))).mapIso e

set_option synthInstance.maxSize 2048 in
private theorem koszulDual_flat (m : ℕ) (n : ℤ) :
    SheafOfModules.IsFlat (((ringedKoszulDualTower O r b).obj (op m)).X n) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalClosed (R := O)
  obtain ⟨I, hI, ⟨e⟩⟩ := koszulDiagram_finiteFree O r b m (-n)
  let := hI
  let d : ((ringedKoszulDualTower O r b).obj (op m)).X n ≅
      SheafOfModules.free (R :=
        (sheafCompose J (forget₂ CommRingCat RingCat)).obj O) I :=
    homSingleXIso O _ n ≪≫
      ((SheafOfModules.homFunctor O).flip.obj (SheafOfModules.unit _)).mapIso e.symm.op ≪≫
        SheafOfModules.homObjFreeUnitIso I
  have hf : ObjectProperty.flat (SheafOfModules.free (R :=
      (sheafCompose J (forget₂ CommRingCat RingCat)).obj O) I) := by
    apply ObjectProperty.flat_coproduct (fun _ : I ↦ SheafOfModules.unit _)
    intro i
    exact ObjectProperty.prop_unit _
  exact ((ObjectProperty.flat).prop_of_iso d.symm hf).tensorRight

set_option synthInstance.maxSize 2048 in
/-- Every finite dual Koszul complex is K-flat.  The proof uses its bounded finite
filtration with finite free graded pieces and the bounded-above flat K-flat criterion.
(auxiliary; not a blueprint node).
Proof: use the bounded finite filtration by finite free graded pieces and apply the
bounded-above flat K-flat criterion. -/
theorem ringed_cech_koszul_dual_tower_isKFlat :
    ∀ m : ℕ, CochainComplex.IsKFlatTensor
      ((ringedKoszulDualTower O r b).obj (op m)) := by
  intro m
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨0, fun n hn ↦ ?_⟩
    exact ((((SheafOfModules.homFunctor O).flip.obj (SheafOfModules.unit _)).map_isZero
      (koszulDiagram_nonneg O r b m (-n) (by omega)).op)).of_iso
        (homSingleXIso O _ n)
  · exact koszulDual_flat O r b m

end CategoryTheory
