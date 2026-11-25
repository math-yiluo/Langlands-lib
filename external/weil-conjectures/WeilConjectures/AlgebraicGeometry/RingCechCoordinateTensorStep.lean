/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.AlgebraicGeometry.RingCechAlgebraicConeCoordinates
import WeilConjectures.AlgebraicGeometry.RingLocalizationTensorBlocks

/-! # Adjoining one localization factor to an ordered localization complex

Source: Stacks Project, algebraization.tex, Tags 0996 and 099D(d).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped BigOperators TensorProduct
namespace CategoryTheory

/-- A single two-term localization factor preserves the positive ordered coordinates
of an arbitrary nonnegative augmented complex with the tail's coordinates.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099D(d), the induction
adjoining the first factor in the tensor expansion.
(auxiliary; not a blueprint node).

Proof: write S=A[1/f(0)]. The first factor is A in degree zero, S in degree one,
and zero elsewhere. The total tensor in degree n is therefore the direct sum of
K^n and S tensor K^(n-1). Its degree-zero augmentation on the A tensor K^0
summand is the tail augmentation followed by multiplication, by ha. In positive degree,
apply the supplied tail coordinates to the two summands. Localization commutes
with finite sums, and multiplication of fractions identifies S tensor A[1/g]
with A[1/(f(0)*g)]. The inverse sends a/(f(0)*g)^k to
(1/f(0)^k) tensor (a/g^k); the localization universal property proves both
inverse identities, including when a denominator is zero. Partition the ordered
subsets of Fin(r+1) according to whether they contain zero: the first summand
indexes those avoiding zero, and the second indexes those containing zero.
These give mutually inverse linear maps onto the required finite product.
For the differential on the first summand, the tail differential gives all
faces except the face adjoining zero, which is the localization map coming
from the first factor's differential. On the second summand, the first factor
has degree one, so the tensor differential is minus the localized tail
differential. Deleting the initial zero shifts each remaining face index by
one, giving precisely that minus sign. Use localization uniqueness to identify
all transported algebra maps with the maps at the corresponding face products.
For the first differential, hd₀ and the degree-zero localization map give the
diagonal map from the actual tensor augmentation; for later differentials hd
gives the stated alternating sum. This claim constructs no degree-zero
equivalence and proves no negative-degree vanishing.
Finite direct sums are finite products. When r=0 the tail's positive coordinate
products are empty and therefore zero, leaving exactly the single two-term
factor. Zero rings, zero generators and repeated generators require no separate
choices and satisfy the same universal-property and subset formulas. -/
theorem ringCechCoordinates_tensor_step (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin (r + 1) → A)
    (K : CochainComplex (RingSiteModules A) ℤ) (a : K ⟶ ringComplexSingle A)
    (e₀ : (K.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
    (e : ∀ q : ℕ, (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i).succ)))
    (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
      Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i)).succ) →ₐ[A]
        Localization.Away (∏ i, f (t i).succ))
    (hneg : ∀ n : ℤ, n < 0 → CategoryTheory.Limits.IsZero (K.X n))
    (hd₀ : ∀ (x : (K.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
      e 0 ((K.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
        algebraMap A (Localization.Away (∏ i, f (t i).succ)) (e₀ x))
    (hd : ∀ (q : ℕ) (x : (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
      (t : Fin (q + 2) ↪o Fin r),
      e (q + 1) ((K.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
          (op ⟨PUnit.unit⟩) x) t =
        ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
          l q t j (e q x ((Fin.succAboveOrderEmb j).trans t)))
    (ha : ∀ x : (K.X 0).val.obj (op ⟨PUnit.unit⟩),
      ringComplexAugmentationValue a x = e₀ x) :
    let O := CochainComplex.onePointRingSheaf A
    letI : IsGrothendieckAbelian.{u} (RingSiteModules A) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    let s : (O.obj ⋙ forget CommRingCat).sections := ⟨fun _ ↦ f 0, fun _ ↦ rfl⟩
    let P := ringedLocalizationTwoTerm O s
    let L := HomologicalComplex.tensorObj P K
    let b : L ⟶ ringComplexSingle A :=
      HomologicalComplex.tensorHom (ringedLocalizationTwoTermAugmentation O s) a ≫
        (HomologicalComplex.leftUnitor (ringComplexSingle A)).hom
    ∃ (e : ∀ q : ℕ, (L.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
        ((t : Fin (q + 1) ↪o Fin (r + 1)) → Localization.Away (∏ i, f (t i))))
      (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin (r + 1)) (j : Fin (q + 2)),
        Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
          Localization.Away (∏ i, f (t i))),
      (∀ (x : (L.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin (r + 1)),
        e 0 ((L.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
          algebraMap A (Localization.Away (∏ i, f (t i)))
            (ringComplexAugmentationValue b x)) ∧
      (∀ (q : ℕ) (x : (L.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
        (t : Fin (q + 2) ↪o Fin (r + 1)),
        e (q + 1) ((L.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app (op ⟨PUnit.unit⟩) x) t =
          ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
            l q t j (e q x ((Fin.succAboveOrderEmb j).trans t))) := by
  classical
  let O := CochainComplex.onePointRingSheaf A
  let : IsGrothendieckAbelian.{u} (RingSiteModules A) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let s : (O.obj ⋙ forget CommRingCat).sections := ⟨fun _ ↦ f 0, fun _ ↦ rfl⟩
  let P := ringedLocalizationTwoTerm O s
  let L := HomologicalComplex.tensorObj P K
  let b : L ⟶ ringComplexSingle A :=
    HomologicalComplex.tensorHom (ringedLocalizationTwoTermAugmentation O s) a ≫
      (HomologicalComplex.leftUnitor (ringComplexSingle A)).hom
  let M (n : ℕ) : ModuleCat.{u} A := (K.X (n : ℤ)).val.obj (op ⟨PUnit.unit⟩)
  let N := ringCechTailTerm A r (fun i ↦ f i.succ)
  let S := Localization.Away (f 0)
  let C : ∀ n : ℕ, M n ≃ₗ[A] N n
    | 0 => e₀
    | q + 1 => e q
  let D (n : ℕ) : M n →ₗ[A] M (n + 1) :=
    ((K.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).val.app (op ⟨PUnit.unit⟩)).hom
  let d (n : ℕ) : N n →ₗ[A] N (n + 1) :=
    (C (n + 1)).toLinearMap.comp ((D n).comp (C n).symm.toLinearMap)
  have hc (n : ℕ) (x : M n) : d n (C n x) = C (n + 1) (D n x) := by
    simp only [d, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  have h₀ : ∀ (x : A) (t : Fin 1 ↪o Fin r),
      d 0 x t = algebraMap A (Localization.Away (∏ i, f (t i).succ)) x := by
    intro x t
    change e 0 ((K.d 0 1).val.app (op ⟨PUnit.unit⟩) (e₀.symm x)) t = _
    exact (hd₀ (e₀.symm x) t).trans
      (congrArg (algebraMap A (Localization.Away (∏ i, f (t i).succ)))
        (e₀.apply_symm_apply x))
  have hD : ∀ (q : ℕ) (x : N (q + 1)) (t : Fin (q + 2) ↪o Fin r),
      d (q + 1) x t = ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
        l q t j (x ((Fin.succAboveOrderEmb j).trans t)) := by
    intro q x t
    change e (q + 1) ((K.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
      (op ⟨PUnit.unit⟩) ((e q).symm x)) t = _
    have h := hd q ((e q).symm x) t
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h
  -- Project the witnesses without eliminating into the sheaf-tensor target.
  let hcoord := ringCechAlgebraicCone_coordinates A r f d l h₀ hD
  let E := hcoord.choose
  let l' := hcoord.choose_spec.choose
  have hE₀ := hcoord.choose_spec.choose_spec.1
  have hE := hcoord.choose_spec.choose_spec.2
  let hblocks := ringLocalizationTensor_blocks A (f 0) K a hneg
  let z := hblocks.choose
  let c := hblocks.choose_spec.choose
  have haz := hblocks.choose_spec.choose_spec.1
  have hc₀ := hblocks.choose_spec.choose_spec.2.1
  have hcs := hblocks.choose_spec.choose_spec.2.2
  let T (q : ℕ) := TensorProduct.congr (LinearEquiv.refl A S) (C q)
  let F (q : ℕ) := (c q).trans (((C (q + 1)).prodCongr (T q)).trans (E q))
  have ht (q : ℕ) (y : S ⊗[A] M q) :
      T (q + 1) (TensorProduct.map (LinearMap.id : S →ₗ[A] S) (D q) y) =
        TensorProduct.map (LinearMap.id : S →ₗ[A] S) (d q) (T q y) := by
    induction y using TensorProduct.inductionOn with
    | tmul s x =>
      simpa only [T, TensorProduct.map_tmul, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, LinearMap.id_apply] using
          congrArg (fun v ↦ s ⊗ₜ[A] v) (hc q x).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨F, l', ?_, ?_⟩
  · intro x t
    change F 0 ((L.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
      algebraMap A (Localization.Away (∏ i, f (t i))) (ringComplexAugmentationValue b x)
    calc
      F 0 ((L.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
          E 0 (C 1 (D 0 (z x)), T 0 (1 ⊗ₜ[A] z x)) t :=
        congrArg (fun v : M 1 × (S ⊗[A] M 0) ↦ E 0 (C 1 v.1, T 0 v.2) t) (hc₀ x)
      _ = E 0 (d 0 (C 0 (z x)), 1 ⊗ₜ[A] C 0 (z x)) t := by
        exact congrArg (fun w : N 1 ↦ E 0 (w, 1 ⊗ₜ[A] C 0 (z x)) t)
          (hc 0 (z x)).symm
      _ = algebraMap A (Localization.Away (∏ i, f (t i))) (e₀ (z x)) :=
        hE₀ (e₀ (z x)) t
      _ = algebraMap A (Localization.Away (∏ i, f (t i)))
          (ringComplexAugmentationValue b x) :=
        congrArg (algebraMap A (Localization.Away (∏ i, f (t i))))
          ((ha (z x)).symm.trans (haz x).symm)
  · intro q x t
    change F (q + 1) ((L.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
      (op ⟨PUnit.unit⟩) x) t = ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
        l' q t j (F q x ((Fin.succAboveOrderEmb j).trans t))
    let u := (c q x).1
    let v := (c q x).2
    calc
      F (q + 1) ((L.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
          (op ⟨PUnit.unit⟩) x) t =
          E (q + 1) (C (q + 2) (D (q + 1) u),
            T (q + 1) (1 ⊗ₜ[A] u - TensorProduct.map
              (LinearMap.id : S →ₗ[A] S) (D q) v)) t :=
        congrArg (fun w : M (q + 2) × (S ⊗[A] M (q + 1)) ↦
          E (q + 1) (C (q + 2) w.1, T (q + 1) w.2) t) (hcs q x)
      _ = E (q + 1) (d (q + 1) (C (q + 1) u),
          1 ⊗ₜ[A] C (q + 1) u - TensorProduct.map
            (LinearMap.id : S →ₗ[A] S) (d q) (T q v)) t := by
        apply congrArg (fun w : N (q + 2) × (S ⊗[A] N (q + 1)) ↦ E (q + 1) w t)
        apply Prod.ext (hc (q + 1) u).symm
        exact (map_sub (T (q + 1)) _ _).trans
          (congrArg₂ (fun a b : S ⊗[A] N (q + 1) ↦ a - b) rfl (ht q v))
      _ = ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
          l' q t j (F q x ((Fin.succAboveOrderEmb j).trans t)) :=
        hE q (C (q + 1) u) (T q v) t

end CategoryTheory
