/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.Basic
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Left resolutions: the associated cochain complexes

Supplement to `Mathlib.Algebra.Homology.LeftResolution.Basic`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory.Abelian

open Category Limits Preadditive ZeroObject

variable {A C : Type*} [Category* C] [Category* A] {ι : C ⥤ A}

namespace LeftResolution

variable (Λ : LeftResolution ι) (X : A)
  [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

variable {X}


variable [HasZeroObject C]

noncomputable def cochainComplexFunctor : A ⥤ CochainComplex C ℤ :=
  Λ.chainComplexFunctor ⋙ ComplexShape.embeddingDownNat.extendFunctor _

variable (X)

noncomputable abbrev cochainComplex : CochainComplex C ℤ := Λ.cochainComplexFunctor.obj X

set_option backward.defeqAttrib.useBackward true in
noncomputable def cochainComplexXZeroIso : (Λ.cochainComplex X).X 0 ≅ Λ.F.obj X :=
  (Λ.chainComplex X).extendXIso _ (by dsimp) ≪≫ Λ.chainComplexXZeroIso X

set_option backward.defeqAttrib.useBackward true in
noncomputable def cochainComplexXNegOneIso :
    (Λ.cochainComplex X).X (-1) ≅ Λ.F.obj (kernel (Λ.π.app X)) :=
  (Λ.chainComplex X).extendXIso _ (by dsimp) ≪≫ Λ.chainComplexXOneIso X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma cochainComplex_d_neg_one_zero :
    ι.map ((cochainComplex Λ X).d (-1) 0) = ι.map (cochainComplexXNegOneIso Λ X).hom ≫
      Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι (Λ.π.app X) ≫
        ι.map (cochainComplexXZeroIso Λ X).inv := by
  dsimp [cochainComplex, cochainComplexFunctor, chainComplexFunctor,
    cochainComplexXNegOneIso]
  rw [(Λ.chainComplex X).extend_d_eq ComplexShape.embeddingDownNat (i := 1) (j := 0)
      (by simp) (by simp), ι.map_comp, ι.map_comp, map_chainComplex_d_1_0,
      ι.map_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc, ← ι.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def cochainComplexπ :
    (ι.mapHomologicalComplex _).obj (Λ.cochainComplex X) ⟶
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X :=
  HomologicalComplex.mkHomToSingle (ι.map (Λ.cochainComplexXZeroIso X).hom ≫ Λ.π.app X) (by
    rintro i hi
    dsimp at hi
    obtain rfl : i = -1 := by omega
    dsimp
    rw [cochainComplex_d_neg_one_zero, assoc, assoc, assoc, ← ι.map_comp_assoc,
      Iso.inv_hom_id, ι.map_id, id_comp, kernel.condition, comp_zero, comp_zero])

set_option backward.defeqAttrib.useBackward true in
lemma cochainComplexπ_f_0 :
    (Λ.cochainComplexπ X).f 0 = ι.map (Λ.cochainComplexXZeroIso X).hom ≫ Λ.π.app X ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv := by
  simp [cochainComplexπ ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable def cochainComplexNatTransπ :
    Λ.cochainComplexFunctor ⋙ ι.mapHomologicalComplex _ ⟶
      HomologicalComplex.single A (ComplexShape.up ℤ) 0 where
  app _ := Λ.cochainComplexπ _
  naturality X Y f := by
    ext
    dsimp [cochainComplexFunctor, cochainComplexπ, cochainComplexXZeroIso, chainComplexFunctor]
    simp only [Functor.map_comp, assoc, HomologicalComplex.mkHomToSingle_f,
      Functor.mapHomologicalComplex_obj_X]
    rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by dsimp)]
    dsimp
    rw [← ι.map_comp_assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
      HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]
    erw [← Λ.π.naturality_assoc f]
    dsimp
    rw [← ι.map_comp_assoc, assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
      ι.map_comp, ι.map_comp, assoc, assoc]

instance : (Λ.cochainComplex X).IsStrictlyLE 0 where
  isZero i hi := by
    dsimp [cochainComplex, cochainComplexFunctor]
    apply HomologicalComplex.isZero_extend_X
    intro j
    simpa using hi j

set_option backward.defeqAttrib.useBackward true in
instance : CochainComplex.IsGE
    ((ι.mapHomologicalComplex _).obj (Λ.cochainComplex X)) 0 where
  exactAt i hi := by
    apply HomologicalComplex.ExactAt.of_iso _
      ((ComplexShape.embeddingDownNat.mapExtendFunctorNatIso ι).symm.app (Λ.chainComplex X))
    dsimp
    obtain ⟨j, hj⟩ : ∃ (j : ℕ), (ComplexShape.embeddingDownNat).f (j + 1) = i := by
      have : i ≤ -1 := by
        by_contra!
        obtain ⟨k, hk⟩ := @Int.eq_ofNat_of_zero_le (a := i) (by omega)
        exact hi k (by dsimp; omega)
      obtain ⟨j, hj⟩ := Int.le.dest this
      exact ⟨j, by dsimp; omega⟩
    rw [HomologicalComplex.extend_exactAt_iff _ _ hj]
    apply exactAt_map_chainComplex_succ

open CochainComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : QuasiIsoAt (Λ.cochainComplexπ X) 0 := by
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.quasiIso_iff_of_zeros' _ _ (by rfl) (by rfl)]; swap
  · apply (ι.map_isZero (isZero_of_isStrictlyLE _ 0 _ (by omega))).eq_of_tgt
  let S := ShortComplex.mk (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _) (Λ.π.app X) (by simp)
  have hS : S.Exact := by
    rw [S.exact_iff_epi_kernel_lift,
      show kernel.lift S.g S.f S.zero = Λ.π.app (kernel (Λ.π.app X)) by
        rw [← cancel_mono (kernel.ι _), kernel.lift_ι]]
    infer_instance
  refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨hS, by infer_instance⟩
  refine ShortComplex.isoMk (ι.mapIso (Λ.cochainComplexXNegOneIso X))
    (ι.mapIso (Λ.cochainComplexXZeroIso X))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X) ?_ ?_
  · dsimp
    rw [cochainComplex_d_neg_one_zero, assoc, assoc, assoc, ← ι.map_comp,
      Iso.inv_hom_id, ι.map_id]
    dsimp
    rw [comp_id]
  · simp [cochainComplexπ_f_0, S]

instance : QuasiIso (Λ.cochainComplexπ X) where
  quasiIsoAt i := by
    by_cases hi : i = 0
    · subst hi
      infer_instance
    · rw [quasiIsoAt_iff_exactAt]
      · exact HomologicalComplex.exactAt_single_obj _ _ _ _ hi
      · by_cases hi' : 0 < i
        · exact exactAt_of_isLE _ 0 _ hi'
        · exact exactAt_of_isGE _ 0 _ (by omega)

set_option backward.defeqAttrib.useBackward true in
instance : QuasiIso (Λ.cochainComplexNatTransπ.app X) := by
  dsimp
  infer_instance

end LeftResolution

end CategoryTheory.Abelian
