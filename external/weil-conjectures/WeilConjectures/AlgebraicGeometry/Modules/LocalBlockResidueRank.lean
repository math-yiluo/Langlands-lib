/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.LinearAlgebra.MatrixRankFieldExtension

/-! # Residue rank of a local block form -/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem matrix_comp {X : Scheme.{u}} {I J K : Type u}
    [Fintype J] [DecidableEq J] [Finite K] [DecidableEq K]
    (p : free (R := X.ringCatSheaf) I ⟶ free J) (q : free J ⟶ free K) :
    freeMatrix (p ≫ q) = freeMatrix q * freeMatrix p := by
  classical
  let _ := Fintype.ofFinite K
  ext k i
  change freeSectionsEquiv K
    (Hom.app q ⊤ (Hom.app p ⊤ (Hom.app (ιFree i) ⊤ (1 : Γ(X, ⊤))))) k = _
  rw [freeSectionsEquiv_app]
  rfl

private theorem matrix_rank_conjugate {X : Scheme.{u}} {I J K L : Type u}
    [Fintype I] [Finite J] [DecidableEq J]
    [Fintype K] [Finite L] [DecidableEq L]
    {F : Type u} [Field F] (ρ : Γ(X, ⊤) →+* F)
    (p : free (R := X.ringCatSheaf) I ⟶ free J)
    (s : free (R := X.ringCatSheaf) I ≅ free K)
    (t : free (R := X.ringCatSheaf) J ≅ free L) :
    ((freeMatrix (s.inv ≫ p ≫ t.hom)).map ρ).rank =
      ((freeMatrix p).map ρ).rank := by
  classical
  let _ := Fintype.ofFinite J
  let _ := Fintype.ofFinite L
  have hle {A B C D : Type u}
      [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
      (l : free (R := X.ringCatSheaf) A ⟶ free B)
      (q : free B ⟶ free C) (r : free C ⟶ free D) :
      ((freeMatrix (l ≫ q ≫ r)).map ρ).rank ≤ ((freeMatrix q).map ρ).rank := by
    rw [matrix_comp, matrix_comp, Matrix.map_mul, Matrix.map_mul]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  apply le_antisymm (hle s.inv p t.hom)
  have h := hle s.hom (s.inv ≫ p ≫ t.hom) t.inv
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using h

private theorem block_rank {F : Type u} [Field F] {I J K L : Type u}
    [Finite I] [Fintype J] [Finite K] [Fintype L]
    (A : Matrix I J F) (B : Matrix K L F) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow J L F F
  let d := LinearEquiv.sumArrowLequivProdArrow I K F F
  have h : (Matrix.fromBlocks A 0 0 B).mulVecLin =
      d.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap B.mulVecLin) ∘ₗ e.toLinearMap := by
    ext z i
    cases i <;> simp [Matrix.fromBlocks_mulVec, e, d] <;> rfl
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq,
    LinearMap.range_prodMap]
  let E : (A.mulVecLin.range.prod B.mulVecLin.range) ≃ₗ[F]
      A.mulVecLin.range × B.mulVecLin.range :=
    { toFun := fun v ↦ (⟨v.1.1, v.2.1⟩, ⟨v.1.2, v.2.2⟩)
      invFun := fun v ↦ ⟨(v.1.1, v.2.1), v.1.2, v.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  rw [E.finrank_eq, Module.finrank_prod]
  rfl

private noncomputable def sumFreeIso {X : Scheme.{u}} (I J : Type u) :
    free (R := X.ringCatSheaf) (I ⊕ J) ≅ free I ⊞ free J :=
  ((biprod.isoCoprod _ _) ≪≫ freeSumIso I J).symm

private theorem sumFreeIso_inl {X : Scheme.{u}} {I J : Type u} (i : I) :
    ιFree i ≫ (biprod.inl : free (R := X.ringCatSheaf) I ⟶ free I ⊞ free J) ≫
      (sumFreeIso I J).inv = ιFree (Sum.inl i) := by
  simp [sumFreeIso, biprod_isoCoprod_hom, inl_freeSumIso_hom,
    ιFree_freeMap]

private theorem sumFreeIso_inr {X : Scheme.{u}} {I J : Type u} (i : J) :
    ιFree i ≫ (biprod.inr : free (R := X.ringCatSheaf) J ⟶ free I ⊞ free J) ≫
      (sumFreeIso I J).inv = ιFree (Sum.inr i) := by
  simp [sumFreeIso, biprod_isoCoprod_hom, inr_freeSumIso_hom,
    ιFree_freeMap]

private theorem sumFreeIso_ι {X : Scheme.{u}} {I J : Type u} (i : I ⊕ J) :
    ιFree i ≫ (sumFreeIso (X := X) I J).hom =
      Sum.elim
        (fun k ↦ ιFree k ≫ (biprod.inl : free (R := X.ringCatSheaf) I ⟶ free I ⊞ free J))
        (fun k ↦ ιFree k ≫ (biprod.inr : free (R := X.ringCatSheaf) J ⟶ free I ⊞ free J)) i := by
  cases i with
  | inl i =>
    apply (cancel_mono (sumFreeIso (X := X) I J).inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Sum.elim_inl, Sum.elim_inr] using
      (sumFreeIso_inl (X := X) (J := J) i).symm
  | inr i =>
    apply (cancel_mono (sumFreeIso (X := X) I J).inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Sum.elim_inl, Sum.elim_inr] using
      (sumFreeIso_inr (X := X) (I := I) i).symm

private theorem sumFreeIso_π {X : Scheme.{u}} {I J : Type u}
    [DecidableEq I] [DecidableEq J] (i : I ⊕ J) :
    (sumFreeIso (X := X) I J).inv ≫ freeπ i =
      Sum.elim
        (fun k ↦ (biprod.fst : free (R := X.ringCatSheaf) I ⊞ free J ⟶ free I) ≫ freeπ k)
        (fun k ↦ (biprod.snd : free (R := X.ringCatSheaf) I ⊞ free J ⟶ free J) ≫ freeπ k) i := by
  apply biprod.hom_ext'
  all_goals
    apply free_hom_ext
    intro k
    cases i <;> simp [reassoc_of% (sumFreeIso_inl (X := X) k),
      reassoc_of% (sumFreeIso_inr (X := X) k), ιFree_freeπ]

private theorem matrix_block {X : Scheme.{u}} {I J K L : Type u}
    [DecidableEq K] [DecidableEq L]
    (f : free (R := X.ringCatSheaf) I ⟶ free K) (g : free J ⟶ free L) :
    freeMatrix ((sumFreeIso I J).hom ≫ biprod.map f g ≫ (sumFreeIso K L).inv) =
      Matrix.fromBlocks (freeMatrix f) 0 0 (freeMatrix g) := by
  ext i k
  simp only [freeMatrix, Matrix.of_apply, Category.assoc]
  rw [sumFreeIso_π (X := X) (I := K) (J := L) i]
  rw [reassoc_of% (sumFreeIso_ι (X := X) k)]
  cases i <;> cases k <;> simp [Matrix.fromBlocks, Category.assoc] <;> rfl

private theorem matrix_id {X : Scheme.{u}} {I : Type u} [DecidableEq I] :
    freeMatrix (𝟙 (free (R := X.ringCatSheaf) I)) = 1 := by
  ext k i
  simp [freeMatrix, freeπ_app_ιFree_app, Matrix.one_apply, eq_comm]

private theorem matrix_rank_iso {X : Scheme.{u}} {I : Type u}
    [Fintype I] [DecidableEq I] {F : Type u} [Field F] (ρ : Γ(X, ⊤) →+* F)
    (f : free (R := X.ringCatSheaf) I ⟶ free I) [IsIso f] :
    ((freeMatrix f).map ρ).rank = Fintype.card I := by
  have hp : (freeMatrix f).map ρ * (freeMatrix (inv f)).map ρ = 1 := by
    rw [← Matrix.map_mul, ← matrix_comp, IsIso.inv_hom_id, matrix_id]
    exact Matrix.map_one _ ρ.map_zero ρ.map_one
  apply le_antisymm (Matrix.rank_le_card_width _)
  have h := Matrix.rank_mul_le_left ((freeMatrix f).map ρ) ((freeMatrix (inv f)).map ρ)
  simpa only [hp, Matrix.rank_one] using h

private theorem rank_map_ulift {K L : Type u} [Field K] [Field L]
    (ρ : K →+* L) {m n : ℕ}
    (A : Matrix (ULift.{u} (Fin m)) (ULift.{u} (Fin n)) K) :
    (A.map ρ).rank = A.rank := by
  have h := (Matrix.rank_map_field_extension ρ
    (A.submatrix Equiv.ulift.symm Equiv.ulift.symm)).1
  change ((A.map ρ).submatrix Equiv.ulift.symm Equiv.ulift.symm).rank =
    (A.submatrix Equiv.ulift.symm Equiv.ulift.symm).rank at h
  simpa only [Matrix.rank_submatrix] using h

/-- The residue rank of a local block form is the size of its invertible block plus
that of its complementary block. -/
theorem local_block_residue_rank
    {Y Z : Scheme.{u}} {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ) (U : Z.Opens)
    (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (m - a))))
    (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a))))
    (f : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin a)) ⟶
      free (ULift.{u} (Fin a))) [IsIso f]
    (δ : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (m - a))) ⟶
      free (ULift.{u} (Fin (n - a))))
    (hform : (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
      eS.hom ≫ biprod.map f δ ≫ eT.inv)
    (x : U.toScheme) : ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map
        (Y.Γevaluation (j.base x.1))).rank =
      a + ((freeMatrix δ).map (U.toScheme.Γevaluation x)).rank := by
  classical
  let A := freeMatrix (eM.inv ≫ φ ≫ eN.hom)
  let F := restrictFunctor U.ι
  let eMP := (Modules.pullback j).mapIso eM ≪≫ pullbackFreeIso j (ULift.{u} (Fin m))
  let eNP := (Modules.pullback j).mapIso eN ≪≫ pullbackFreeIso j (ULift.{u} (Fin n))
  let eMU := F.mapIso eMP ≪≫ restrictFreeIso U.ι (ULift.{u} (Fin m))
  let eNU := F.mapIso eNP ≪≫ restrictFreeIso U.ι (ULift.{u} (Fin n))
  let ψ := F.map ((Modules.pullback j).map φ)
  have hlocal : freeMatrix (eMU.inv ≫ ψ ≫ eNU.hom) = A.map (U.ι ≫ j).appTop := by
    have hrestrict {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
        {I J : Type u} [DecidableEq J] (q : free (R := X.ringCatSheaf) I ⟶ free J) :
        freeMatrix ((restrictFreeIso g I).inv ≫ (restrictFunctor g).map q ≫
          (restrictFreeIso g J).hom) = (freeMatrix q).map g.appTop := by
      rw [restrictFreeIso, restrictFreeIso]
      simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.app_inv, Iso.app_hom]
      rw [← (restrictFunctorIsoPullback g).inv.naturality_assoc]
      simp only [Iso.inv_hom_id_app_assoc]
      exact freeMatrix_pullback g q
    calc
      _ = (freeMatrix (eMP.inv ≫ (Modules.pullback j).map φ ≫ eNP.hom)).map
          U.ι.appTop := by
        rw [← hrestrict U.ι]
        simp only [eMU, eNU, ψ, F, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
          Functor.mapIso_hom, Functor.map_comp, Category.assoc]
      _ = (A.map j.appTop).map U.ι.appTop := by
        congr 1
        dsimp only [eMP, eNP, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
          Functor.mapIso_hom]
        simp only [Category.assoc, ← Functor.map_comp_assoc]
        exact freeMatrix_pullback j (eM.inv ≫ φ ≫ eN.hom)
      _ = _ := rfl
  let ρ := (U.toScheme.Γevaluation x).hom
  have heval : ((A.map (U.ι ≫ j).appTop).map ρ) =
      (A.map (Y.Γevaluation (j.base x.1))).map ((U.ι ≫ j).residueFieldMap x) := by
    ext i k
    exact (Scheme.Γevaluation_naturality_apply (U.ι ≫ j) x (A i k)).symm
  have hrank : ((freeMatrix (eMU.inv ≫ ψ ≫ eNU.hom)).map ρ).rank =
      (A.map (Y.Γevaluation (j.base x.1))).rank := by
    rw [hlocal, heval]
    exact rank_map_ulift ((U.ι ≫ j).residueFieldMap x).hom _
  let s := eMU.symm ≪≫ eS ≪≫
    (sumFreeIso (ULift.{u} (Fin a)) (ULift.{u} (Fin (m - a)))).symm
  let t := eNU.symm ≪≫ eT ≪≫
    (sumFreeIso (ULift.{u} (Fin a)) (ULift.{u} (Fin (n - a)))).symm
  have hblock : s.inv ≫ (eMU.inv ≫ ψ ≫ eNU.hom) ≫ t.hom =
      (sumFreeIso _ _).hom ≫ biprod.map f δ ≫ (sumFreeIso _ _).inv := by
    dsimp only [s, t, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [show ψ = eS.hom ≫ biprod.map f δ ≫ eT.inv from hform]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  calc
    (A.map (Y.Γevaluation (j.base x.1))).rank =
        ((freeMatrix (eMU.inv ≫ ψ ≫ eNU.hom)).map ρ).rank := hrank.symm
    _ = ((freeMatrix (s.inv ≫ (eMU.inv ≫ ψ ≫ eNU.hom) ≫ t.hom)).map ρ).rank :=
      (matrix_rank_conjugate ρ _ s t).symm
    _ = ((Matrix.fromBlocks (freeMatrix f) 0 0 (freeMatrix δ)).map ρ).rank := by
      rw [hblock, matrix_block]
    _ = ((freeMatrix f).map ρ).rank + ((freeMatrix δ).map ρ).rank := by
      rw [Matrix.fromBlocks_map]
      simp only [Matrix.map_zero, map_zero]
      exact block_rank _ _
    _ = a + ((freeMatrix δ).map (U.toScheme.Γevaluation x)).rank := by
      rw [matrix_rank_iso ρ f]
      simp only [Fintype.card_ulift, Fintype.card_fin]
      rfl


end AlgebraicGeometry.Scheme.Modules
