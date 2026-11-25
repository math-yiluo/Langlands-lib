/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexScalarAugmentation
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Localization.BaseChange

/-! # Scalar extension of explicit ordered localization coordinates

Source: Stacks Project, Tag 0ALZ and Tag 00DK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings BigOperators
namespace AlgebraicGeometry

private def localizationTensorIso {A B : CommRingCat.{u}} (φ : A →+* B)
    (g : A) (k : B) (hk : φ g = k) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of A (Localization.Away g)) ≃ₗ[B]
      Localization.Away k := by
  letI : Algebra A B := φ.toAlgebra
  let : IsLocalization.Away (algebraMap A B g) (Localization.Away k) := by
    change IsLocalization.Away (φ g) (Localization.Away k)
    rw [hk]
    infer_instance
  exact (IsLocalization.algEquiv (Submonoid.powers (algebraMap A B g))
    (B ⊗[A] Localization.Away g) (Localization.Away k)).toLinearEquiv

private def localizationScalarMap {A B : CommRingCat.{u}} (φ : A →+* B)
    (g : A) (k : B) (hk : φ g = k) : Localization.Away g →+* Localization.Away k := by
  letI : Algebra A B := φ.toAlgebra
  let : IsLocalization.Away (algebraMap A B g) (Localization.Away k) := by
    change IsLocalization.Away (φ g) (Localization.Away k)
    rw [hk]
    infer_instance
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap A B g))
    (B ⊗[A] Localization.Away g) (Localization.Away k)
  exact ((e.restrictScalars A).toAlgHom.comp Algebra.TensorProduct.includeRight).toRingHom

private theorem localizationScalarMap_algebraMap {A B : CommRingCat.{u}}
    (φ : A →+* B) (g : A) (k : B) (hk : φ g = k) (a : A) :
    localizationScalarMap φ g k hk (algebraMap A (Localization.Away g) a) =
      algebraMap B (Localization.Away k) (φ a) := by
  let : Algebra A B := φ.toAlgebra
  let : IsLocalization.Away (algebraMap A B g) (Localization.Away k) := by
    change IsLocalization.Away (φ g) (Localization.Away k)
    rw [hk]
    infer_instance
  change ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B g))
    (B ⊗[A] Localization.Away g) (Localization.Away k)).restrictScalars A
    |>.toAlgHom.comp Algebra.TensorProduct.includeRight)
      (algebraMap A (Localization.Away g) a) = _
  rw [AlgHom.commutes]
  rfl

private def pointIso {A : CommRingCat.{u}} {M N : RingSiteModules A}
    (e : M.val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) : M ≅ N where
  hom := ringComplexPointLift _ _ e.toLinearMap
  inv := ringComplexPointLift _ _ e.symm.toLinearMap
  hom_inv_id := by
    apply ringComplex_point_hom_ext
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply ringComplex_point_hom_ext
    ext x
    exact e.apply_symm_apply x

private def scalarPointIso {A B : CommRingCat.{u}} (φ : A →+* B)
    (M : RingSiteModules A) (N : RingSiteModules B)
    (e : (ModuleCat.extendScalars φ).obj (M.val.obj (op ⟨PUnit.unit⟩)) ≃ₗ[B]
      N.val.obj (op ⟨PUnit.unit⟩)) : (ringComplexExtension φ).obj M ≅ N :=
  pointIso ((ringComplexExtensionSections φ M).toLinearEquiv.symm.trans e)

private theorem scalarPointIso_one_tmul {A B : CommRingCat.{u}} (φ : A →+* B)
    (M : RingSiteModules A) (N : RingSiteModules B)
    (e : (ModuleCat.extendScalars φ).obj (M.val.obj (op ⟨PUnit.unit⟩)) ≃ₗ[B]
      N.val.obj (op ⟨PUnit.unit⟩)) (x : M.val.obj (op ⟨PUnit.unit⟩)) :
    (scalarPointIso φ M N e).hom.val.app (op ⟨PUnit.unit⟩)
      ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
        (ringSiteMap φ) M).presheaf).app (op ⟨PUnit.unit⟩)
          ((1 : B) ⊗ₜ[A, φ] x)) = e ((1 : B) ⊗ₜ[A, φ] x) := by
  let z := (1 : B) ⊗ₜ[A, φ] x
  change e ((ringComplexExtensionSections φ M).inv
    ((ringComplexExtensionSections φ M).hom z)) = e z
  exact congrArg e (ConcreteCategory.congr_hom
    (ringComplexExtensionSections φ M).hom_inv_id z)

/-- Scalar extension identifies two explicit ordered localization complexes for a list
and its image. This is an augmented cochain isomorphism, with no derived-category,
K-flatness, ideal, replacement complex, or change-of-generators assumption.
Source: Stacks Project, dualizing.tex, Tag 0ALZ; algebra.tex, Tag 00DK.
(auxiliary; not a blueprint node).

Proof: in degree zero use multiplication B tensor_A A to B. In degree q+1, tensor
commutes with the finite product indexed by increasing (q+1)-tuples. On its t-factor
use B tensor_A A[1/product(f(t i))] = B[1/product(phi(f(t i)))]. This is the localization
base-change isomorphism; it sends b tensor a/g^n to b*phi(a)/phi(g)^n, and its inverse
sends b/phi(g)^n to b tensor 1/g^n. Use the supplied linear coordinate isomorphisms to
transport these maps to the terms of the complexes. The bottom-topology sheafification
unit identifies tensor sections with the actual scalar-extension sheaf. Negative terms
are zero. For the first differential the fraction map carries phi(a) to its localization.
For the positive differentials the face maps commute with these fraction maps: both
composites are the unique algebra map out of the corresponding localization. Tensor
linearity then preserves the finite alternating sum and its integer signs. Thus the
term isomorphisms form a cochain isomorphism. In degree zero their multiplication map
is precisely the scalar augmentation; other target degrees are zero. This proves the
augmentation equation. Finite empty products here are zero modules, so an empty list
works; the localization identities also apply at zero generators and over zero rings. -/
theorem ringComplex_ordered_scalar_iso
    (A B : CommRingCat.{u}) (φ : A →+* B) (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (RingSiteModules A) ℤ) (a : C ⟶ ringComplexSingle A)
    (e₀ : (C.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
    (e : ∀ q : ℕ, (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
    (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
      Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
        Localization.Away (∏ i, f (t i)))
    (hneg : ∀ n : ℤ, n < 0 → IsZero (C.X n))
    (hd₀ : ∀ (x : (C.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
      e 0 ((C.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
        algebraMap A (Localization.Away (∏ i, f (t i))) (e₀ x))
    (hd : ∀ (q : ℕ) (x : (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
      (t : Fin (q + 2) ↪o Fin r),
      e (q + 1) ((C.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
        (op ⟨PUnit.unit⟩) x) t =
          ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
            l q t j (e q x ((Fin.succAboveOrderEmb j).trans t)))
    (ha : ∀ x : (C.X 0).val.obj (op ⟨PUnit.unit⟩),
      ringComplexAugmentationValue a x = e₀ x)
    (D : CochainComplex (RingSiteModules B) ℤ) (b : D ⟶ ringComplexSingle B)
    (e₀' : (D.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[B] B)
    (e' : ∀ q : ℕ, (D.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[B]
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, (φ ∘ f) (t i))))
    (l' : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
      Localization.Away (∏ i, (φ ∘ f) (t (Fin.succAboveOrderEmb j i))) →ₐ[B]
        Localization.Away (∏ i, (φ ∘ f) (t i)))
    (hneg' : ∀ n : ℤ, n < 0 → IsZero (D.X n))
    (hd₀' : ∀ (x : (D.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
      e' 0 ((D.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
        algebraMap B (Localization.Away (∏ i, (φ ∘ f) (t i))) (e₀' x))
    (hd' : ∀ (q : ℕ) (x : (D.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
      (t : Fin (q + 2) ↪o Fin r),
      e' (q + 1) ((D.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
        (op ⟨PUnit.unit⟩) x) t =
          ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
            l' q t j (e' q x ((Fin.succAboveOrderEmb j).trans t)))
    (ha' : ∀ x : (D.X 0).val.obj (op ⟨PUnit.unit⟩),
      ringComplexAugmentationValue b x = e₀' x)
    : ∃ β : ringComplexExtensionComplex φ C ≅ D,
      β.hom ≫ b = ringComplexScalarAugmentation φ a := by
  classical
  let : Algebra A B := φ.toAlgebra
  let g (q : ℕ) (t : Fin (q + 1) ↪o Fin r) : A := ∏ i, f (t i)
  let k (q : ℕ) (t : Fin (q + 1) ↪o Fin r) : B := ∏ i, (φ ∘ f) (t i)
  have hk (q : ℕ) (t : Fin (q + 1) ↪o Fin r) : φ (g q t) = k q t :=
    map_prod φ (fun i ↦ f (t i)) Finset.univ
  let E₀ : (ringComplexExtension φ).obj (C.X 0) ≅ D.X 0 :=
    scalarPointIso φ _ _
      (((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) e₀).trans
        (TensorProduct.AlgebraTensorModule.rid A B B)).trans e₀'.symm)
  let Epos (q : ℕ) : (ringComplexExtension φ).obj (C.X ((q : ℤ) + 1)) ≅
      D.X ((q : ℤ) + 1) :=
    scalarPointIso φ _ _
      (((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (e q)).trans
        ((TensorProduct.piRight A B B (fun t ↦ Localization.Away (g q t))).trans
          (LinearEquiv.piCongrRight
            (fun t ↦ localizationTensorIso φ (g q t) (k q t) (hk q t))))).trans
            (e' q).symm)
  have hE₀ (x : (C.X 0).val.obj (op ⟨PUnit.unit⟩)) :
      e₀' (E₀.hom.val.app (op ⟨PUnit.unit⟩)
        ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
          (ringSiteMap φ) (C.X 0)).presheaf).app (op ⟨PUnit.unit⟩)
            ((1 : B) ⊗ₜ[A, φ] x))) = φ (e₀ x) := by
    rw [show E₀ = scalarPointIso φ _ _ _ from rfl, scalarPointIso_one_tmul]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    change φ (e₀ x) * 1 = φ (e₀ x)
    exact mul_one _
  have hEpos (q : ℕ) (x : (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩)) :
      e' q ((Epos q).hom.val.app (op ⟨PUnit.unit⟩)
        ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
          (ringSiteMap φ) (C.X ((q : ℤ) + 1))).presheaf).app (op ⟨PUnit.unit⟩)
            ((1 : B) ⊗ₜ[A, φ] x))) =
          fun t ↦ localizationScalarMap φ (g q t) (k q t) (hk q t) (e q x t) := by
    rw [show Epos q = scalarPointIso φ _ _ _ from rfl, scalarPointIso_one_tmul]
    simp only [LinearEquiv.trans_apply]
    exact ((e' q).apply_symm_apply _).trans (by rfl)
  have hface (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)) :
      (localizationScalarMap φ (g (q + 1) t) (k (q + 1) t) (hk (q + 1) t)).comp
          (l q t j).toRingHom =
        (l' q t j).toRingHom.comp
          (localizationScalarMap φ (g q ((Fin.succAboveOrderEmb j).trans t))
            (k q ((Fin.succAboveOrderEmb j).trans t))
            (hk q ((Fin.succAboveOrderEmb j).trans t))) := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (∏ i, f (t (Fin.succAboveOrderEmb j i))))
    ext z
    change localizationScalarMap φ (g (q + 1) t) (k (q + 1) t) (hk (q + 1) t)
        (l q t j (algebraMap A _ z)) =
      l' q t j (localizationScalarMap φ (g q ((Fin.succAboveOrderEmb j).trans t))
        (k q ((Fin.succAboveOrderEmb j).trans t))
        (hk q ((Fin.succAboveOrderEmb j).trans t)) (algebraMap A _ z))
    calc
      _ = localizationScalarMap φ (g (q + 1) t) (k (q + 1) t) (hk (q + 1) t)
          (algebraMap A _ z) := congrArg _ ((l q t j).commutes z)
      _ = algebraMap B _ (φ z) :=
        localizationScalarMap_algebraMap φ (g (q + 1) t) (k (q + 1) t) (hk (q + 1) t) z
      _ = l' q t j (algebraMap B _ (φ z)) := ((l' q t j).commutes (φ z)).symm
      _ = _ := congrArg (l' q t j)
        (localizationScalarMap_algebraMap φ (g q ((Fin.succAboveOrderEmb j).trans t))
          (k q ((Fin.succAboveOrderEmb j).trans t))
          (hk q ((Fin.succAboveOrderEmb j).trans t)) z).symm
  let E (n : ℤ) : (ringComplexExtension φ).obj (C.X n) ≅ D.X n := by
    cases n with
    | ofNat n =>
      cases n with
      | zero => exact E₀
      | succ q => exact Epos q
    | negSucc q =>
      exact ((ringComplexExtension φ).map_isZero (hneg _ (by omega))).isoZero ≪≫
        (hneg' _ (by omega)).isoZero.symm
  have hcomm : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      (E i).hom ≫ D.d i j =
        ((ringComplexExtension φ).map (C.d i j)) ≫ (E j).hom := by
    intro i j hij
    have hj : j = i + 1 := hij.symm
    subst j
    by_cases hi : i < 0
    · exact ((ringComplexExtension φ).map_isZero (hneg i hi)).eq_of_src _ _
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hi)
      apply ringComplexExtension_hom_ext φ (C.X _) (D.X _)
      intro x
      change (D.d _ _).val.app (op ⟨PUnit.unit⟩)
          ((E _).hom.val.app (op ⟨PUnit.unit⟩) _) =
        (E _).hom.val.app (op ⟨PUnit.unit⟩)
          (((ringComplexExtension φ).map (C.d _ _)).val.app (op ⟨PUnit.unit⟩) _)
      rw [ringComplexExtension_map_one_tmul]
      cases n with
      | zero =>
        apply (e' 0).injective
        funext t
        change e' 0 ((D.d 0 1).val.app _ (E₀.hom.val.app _ _)) t =
          e' 0 ((Epos 0).hom.val.app _ _) t
        erw [hd₀', hE₀, hEpos]
        change _ = localizationScalarMap φ (g 0 t) (k 0 t) (hk 0 t)
          (e 0 ((C.d 0 1).val.app _ x) t)
        erw [hd₀, localizationScalarMap_algebraMap]
      | succ q =>
        apply (e' (q + 1)).injective
        funext t
        change e' (q + 1) ((D.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app _
            ((Epos q).hom.val.app _ _)) t =
          e' (q + 1) ((Epos (q + 1)).hom.val.app _ _) t
        erw [hd', hEpos, hEpos]
        change _ = localizationScalarMap φ (g (q + 1) t) (k (q + 1) t) (hk (q + 1) t)
          (e (q + 1) ((C.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app _ x) t)
        rw [hd]
        simp only [map_sum, map_zsmul]
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun z ↦ (-1 : ℤ) ^ j.val • z)
          (RingHom.congr_fun (hface q t j) (e q x ((Fin.succAboveOrderEmb j).trans t))).symm
  let β : ringComplexExtensionComplex φ C ≅ D :=
    HomologicalComplex.Hom.isoOfComponents E hcomm
  refine ⟨β, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    apply (cancel_mono
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit B)).hom).1
    apply ringComplexExtension_hom_ext φ (C.X 0) (ringComplexUnit B)
    intro x
    change ringComplexAugmentationValue b (E₀.hom.val.app _ _) =
      ringComplexAugmentationValue (ringComplexScalarAugmentation φ a) _
    rw [ha', hE₀, ringComplexScalarAugmentation_one_tmul, ha]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit B)
      n hn).eq_of_tgt _ _

end AlgebraicGeometry
