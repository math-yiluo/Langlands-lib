/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Logic.Equiv.Fintype

@[expose] public section
universe u
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

-- Extend a selected list to a full basis, without assuming a positive rank.
private theorem coordinate_equiv {a m : ℕ} (f : Fin a → ULift.{u} (Fin m))
    (hf : Function.Injective f) :
    ∃ e : ULift.{u} (Fin a) ⊕ ULift.{u} (Fin (m - a)) ≃ ULift.{u} (Fin m),
      ∀ i, e (Sum.inl i) = f i.down := by
  classical
  have ha : a ≤ m := by simpa using Fintype.card_le_of_injective f hf
  let e₀ : ULift.{u} (Fin a) ⊕ ULift.{u} (Fin (m - a)) ≃ ULift.{u} (Fin m) :=
    Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin a ↦ e₀ (Sum.inl (ULift.up i))) f
    (by intro i k h; simpa using e₀.injective h) hf
  exact ⟨e₀.trans σ, fun i ↦ hσ i.down⟩

-- Split the reordered free sheaf into its selected and complementary coordinates.
private noncomputable def coordinateIso {X : Scheme.{u}} {I J K : Type u}
    (e : I ⊕ J ≃ K) : free (R := X.ringCatSheaf) K ≅ free I ⊞ free J :=
  ((biprod.isoCoprod _ _) ≪≫ freeSumIso I J ≪≫
    (freeFunctor (R := X.ringCatSheaf)).mapIso e.toIso).symm

private theorem coordinateIso_inl {X : Scheme.{u}} {I J K : Type u}
    (e : I ⊕ J ≃ K) (i : I) :
    ιFree i ≫ (biprod.inl : free (R := X.ringCatSheaf) I ⟶ free I ⊞ free J) ≫
      (coordinateIso (X := X) e).inv = ιFree (e (Sum.inl i)) := by
  simp only [coordinateIso, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom,
    biprod_isoCoprod_hom, biprod.inl_desc_assoc,
    inl_freeSumIso_hom_assoc, freeFunctor_map, ιFree_freeMap_assoc, ιFree_freeMap]
  rfl

private theorem coordinateIso_inr {X : Scheme.{u}} {I J K : Type u}
    (e : I ⊕ J ≃ K) (i : J) :
    ιFree i ≫ (biprod.inr : free (R := X.ringCatSheaf) J ⟶ free I ⊞ free J) ≫
      (coordinateIso (X := X) e).inv = ιFree (e (Sum.inr i)) := by
  simp only [coordinateIso, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom,
    biprod_isoCoprod_hom, biprod.inr_desc_assoc,
    inr_freeSumIso_hom_assoc, freeFunctor_map, ιFree_freeMap_assoc, ιFree_freeMap]
  rfl

private theorem coordinateIso_fst {X : Scheme.{u}} {I J K : Type u}
    [DecidableEq I] [DecidableEq K] (e : I ⊕ J ≃ K) (i : I) :
    (coordinateIso (X := X) e).hom ≫ biprod.fst ≫ freeπ i = freeπ (e (Sum.inl i)) := by
  apply (cancel_epi (coordinateIso (X := X) e).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply biprod.hom_ext'
  · apply free_hom_ext
    intro k
    simp [reassoc_of% (coordinateIso_inl (X := X) e k),
      ιFree_freeπ, e.injective.eq_iff]
  · apply free_hom_ext
    intro k
    simp [reassoc_of% (coordinateIso_inr (X := X) e k),
      ιFree_freeπ, e.injective.eq_iff]

private theorem freeMatrix_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    {I J : Type u} [DecidableEq J] (φ : free (R := X.ringCatSheaf) I ⟶ free J) :
    freeMatrix ((restrictFreeIso g I).inv ≫ (restrictFunctor g).map φ ≫
      (restrictFreeIso g J).hom) = (freeMatrix φ).map g.appTop := by
  rw [restrictFreeIso, restrictFreeIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.app_inv, Iso.app_hom]
  rw [← (restrictFunctorIsoPullback g).inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  exact freeMatrix_pullback g φ

private theorem freeMatrix_coordinateIso {X : Scheme.{u}} {I J K L H : Type u}
    [DecidableEq I] [DecidableEq L]
    (eS : I ⊕ K ≃ J) (eT : I ⊕ H ≃ L)
    (φ : free (R := X.ringCatSheaf) J ⟶ free L) :
    freeMatrix ((biprod.inl : free (R := X.ringCatSheaf) I ⟶ free I ⊞ free K) ≫
      (coordinateIso eS).inv ≫ φ ≫
      (coordinateIso eT).hom ≫ biprod.fst) =
        (freeMatrix φ).submatrix (fun i ↦ eT (Sum.inl i)) (fun i ↦ eS (Sum.inl i)) := by
  ext i k
  simp only [freeMatrix, Matrix.of_apply, Matrix.submatrix_apply, Category.assoc,
    reassoc_of% (coordinateIso_inl (X := X) eS k)]
  rw [coordinateIso_fst eT i]

private theorem minor_indices_injective {X : Scheme.{u}} {a m n : ℕ}
    (A : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin m)) Γ(X, ⊤))
    (rows : Fin a → ULift.{u} (Fin n)) (cols : Fin a → ULift.{u} (Fin m))
    (x : X) (hx : x ∈ X.basicOpen (A.submatrix rows cols).det) :
    Function.Injective rows ∧ Function.Injective cols := by
  classical
  have hd : (A.submatrix rows cols).det ≠ 0 := by
    intro h
    simp [h, Scheme.basicOpen_zero] at hx
  constructor
  · intro i k h
    by_contra hik
    apply hd
    apply Matrix.det_zero_of_row_eq hik
    ext l
    exact congrArg (fun r ↦ A r (cols l)) h
  · intro i k h
    by_contra hik
    apply hd
    exact Matrix.det_zero_of_column_eq hik (fun l ↦ congrArg (A (rows l)) h)

/-- Local coordinate decompositions identify the leading determinant with the
restriction of the selected minor, and that restriction is a unit. -/
theorem exists_local_invertible_minor_block_data
    {Y Z : Scheme.{u}} {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ) (z : Z)
    (rows : Fin a → ULift.{u} (Fin n)) (cols : Fin a → ULift.{u} (Fin m))
    (hminor : j.base z ∈
      Y.basicOpen ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).submatrix rows cols).det) :
    ∃ U : Z.Opens, z ∈ U ∧
      ∃ (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (m - a))))
        (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a)))),
        (freeMatrix (X := U.toScheme) (I := ULift.{u} (Fin a))
          (J := ULift.{u} (Fin a)) (biprod.inl ≫ eS.inv ≫
          (restrictFunctor U.ι).map ((Modules.pullback j).map φ) ≫
          eT.hom ≫ biprod.fst)).det =
            (U.ι ≫ j).appTop
              ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).submatrix rows cols).det ∧
        IsUnit ((U.ι ≫ j).appTop
          ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).submatrix rows cols).det) := by
  classical
  let A := freeMatrix (eM.inv ≫ φ ≫ eN.hom)
  obtain ⟨hr, hc⟩ := minor_indices_injective A rows cols (j.base z) hminor
  obtain ⟨p, hp⟩ := coordinate_equiv cols hc
  obtain ⟨q, hq⟩ := coordinate_equiv rows hr
  let δ := (A.submatrix rows cols).det
  let U : Z.Opens := Z.basicOpen (j.appTop δ)
  have hz : z ∈ U := by
    change z ∈ Z.basicOpen (j.appTop δ)
    rw [← Scheme.preimage_basicOpen_top]
    exact hminor
  have hunit : IsUnit ((U.ι ≫ j).appTop δ) := by
    change IsUnit (U.ι.appTop (j.appTop δ))
    exact Z.isUnit_ι_appTop_basicOpen (j.appTop δ)
  let F := restrictFunctor U.ι
  let eMP := (Modules.pullback j).mapIso eM ≪≫ pullbackFreeIso j (ULift.{u} (Fin m))
  let eNP := (Modules.pullback j).mapIso eN ≪≫ pullbackFreeIso j (ULift.{u} (Fin n))
  let eMU := F.mapIso eMP ≪≫ restrictFreeIso U.ι (ULift.{u} (Fin m))
  let eNU := F.mapIso eNP ≪≫ restrictFreeIso U.ι (ULift.{u} (Fin n))
  let ψ := F.map ((Modules.pullback j).map φ)
  have hlocal : freeMatrix (eMU.inv ≫ ψ ≫ eNU.hom) = A.map (U.ι ≫ j).appTop := by
    calc
      _ = (freeMatrix (eMP.inv ≫ (Modules.pullback j).map φ ≫ eNP.hom)).map
          U.ι.appTop := by
        rw [← freeMatrix_restrict U.ι]
        simp only [eMU, eNU, ψ, F, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
          Functor.mapIso_hom, Functor.map_comp, Category.assoc]
      _ = (A.map j.appTop).map U.ι.appTop := by
        congr 1
        dsimp only [eMP, eNP, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
          Functor.mapIso_hom]
        simp only [Category.assoc, ← Functor.map_comp_assoc]
        exact freeMatrix_pullback j (eM.inv ≫ φ ≫ eN.hom)
      _ = _ := rfl
  refine ⟨U, hz, eMU ≪≫ coordinateIso (X := U.toScheme) p,
    eNU ≪≫ coordinateIso (X := U.toScheme) q, ?_, hunit⟩
  change (freeMatrix (X := U.toScheme) (I := ULift.{u} (Fin a))
    (J := ULift.{u} (Fin a)) (biprod.inl ≫ (eMU ≪≫ coordinateIso (X := U.toScheme) p).inv ≫ ψ ≫
    (eNU ≪≫ coordinateIso (X := U.toScheme) q).hom ≫ biprod.fst)).det = (U.ι ≫ j).appTop δ
  have hcoord := freeMatrix_coordinateIso (X := U.toScheme) p q (eMU.inv ≫ ψ ≫ eNU.hom)
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc] at hcoord ⊢
  rw [hcoord, hlocal]
  simp only [hp, hq]
  change (((A.submatrix rows cols).map (U.ι ≫ j).appTop).submatrix
    (Equiv.ulift : ULift.{u} (Fin a) ≃ Fin a)
    (Equiv.ulift : ULift.{u} (Fin a) ≃ Fin a)).det = (U.ι ≫ j).appTop δ
  rw [Matrix.det_submatrix_equiv_self]
  exact ((U.ι ≫ j).appTop.hom.map_det (A.submatrix rows cols)).symm

end AlgebraicGeometry.Scheme.Modules
