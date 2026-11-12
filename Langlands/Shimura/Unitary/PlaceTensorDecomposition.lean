import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Scalar extension of an algebra to a completion, decomposed over the places above

Let `K/F` be an extension of number fields, `A` a `K`-algebra (possibly
noncommutative) and `𝔭` a finite place of `F`. Then
`F_𝔭 ⊗[F] A ≅ Π_{w ∣ 𝔭} K_w ⊗[K] A`, through `x ⊗ a ↦ (x ⊗ a)_w`, by the
published bijectivity of `F_𝔭 ⊗[F] K → Π_{w ∣ 𝔭} K_w`. On units this gives
`(F_𝔭 ⊗[F] A)ˣ ≅ Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ`.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

set_option autoImplicit false

universe u v w

namespace Langlands.Shimura.PlaceTensor

open Langlands.Global.AdelicFunctoriality

section Decomposition

variable {F : Type u} {K : Type v} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] (𝔭 : HeightOneSpectrum (𝓞 F))

/-- The completed tensor comparison `K ⊗[F] F_𝔭 ≃ Π_{w ∣ 𝔭} K_w`, as an isomorphism of
`K`-algebras: the published bijection `finiteTensorMap` after exchanging the factors. -/
def fieldTensorEquiv :
    K ⊗[F] 𝔭.adicCompletion F ≃ₐ[K] (Π w : FinitePlacesAbove K 𝔭, w.1.adicCompletion K) :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.comm F K (𝔭.adicCompletion F)).toRingEquiv.trans
      (RingEquiv.ofBijective (finiteTensorMap (L := K) 𝔭)
        ((completedTensorComparison F K).1 𝔭))))
    (fun k => by
      funext w
      change finiteTensorMap (L := K) 𝔭 ((1 : 𝔭.adicCompletion F) ⊗ₜ[F] k) w = _
      rw [finiteTensorMap_one_tmul]
      rfl)

@[simp] theorem fieldTensorEquiv_tmul (k : K) (x : 𝔭.adicCompletion F)
    (w : FinitePlacesAbove K 𝔭) :
    fieldTensorEquiv 𝔭 (k ⊗ₜ[F] x) w =
      FiniteExtension.completionMap 𝔭 w.1 x * algebraMap K (w.1.adicCompletion K) k :=
  finiteTensorMap_tmul 𝔭 x k w

variable (A : Type w) [Ring A] [Algebra F A] [Algebra K A] [IsScalarTower F K A]

/-- Scalar extension in two steps: `A ⊗[F] F_𝔭 ≃ A ⊗[K] (K ⊗[F] F_𝔭)`. -/
def towerEquiv : A ⊗[F] 𝔭.adicCompletion F ≃ₐ[K] A ⊗[K] (K ⊗[F] 𝔭.adicCompletion F) :=
  AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange F K K A (𝔭.adicCompletion F)).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by
      simp [Algebra.TensorProduct.tmul_mul_tmul]))

omit [NumberField K] in
@[simp] theorem towerEquiv_tmul (a : A) (x : 𝔭.adicCompletion F) :
    towerEquiv (K := K) 𝔭 A (a ⊗ₜ[F] x) = a ⊗ₜ[K] ((1 : K) ⊗ₜ[F] x) := rfl

open Classical in
/-- `F_𝔭 ⊗[F] A ≃ Π_{w ∣ 𝔭} K_w ⊗[K] A` as rings. -/
def placeTensorEquiv :
    𝔭.adicCompletion F ⊗[F] A ≃+* (Π w : FinitePlacesAbove K 𝔭, w.1.adicCompletion K ⊗[K] A) :=
  ((Algebra.TensorProduct.comm F (𝔭.adicCompletion F) A).toRingEquiv.trans
    ((towerEquiv (K := K) 𝔭 A).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[K] A)
        (fieldTensorEquiv (K := K) 𝔭)).toRingEquiv.trans
        ((Algebra.TensorProduct.piRight K K A
          (fun w : FinitePlacesAbove K 𝔭 => w.1.adicCompletion K)).toRingEquiv.trans
          (AlgEquiv.piCongrRight fun w : FinitePlacesAbove K 𝔭 =>
            Algebra.TensorProduct.comm K A (w.1.adicCompletion K)).toRingEquiv))))

theorem placeTensorEquiv_tmul (x : 𝔭.adicCompletion F) (a : A) (w : FinitePlacesAbove K 𝔭) :
    placeTensorEquiv 𝔭 A (x ⊗ₜ[F] a) w = FiniteExtension.completionMap 𝔭 w.1 x ⊗ₜ[K] a := by
  simp [placeTensorEquiv]

/-- On units: `(F_𝔭 ⊗[F] A)ˣ ≃ Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ`. -/
def placeUnitsEquiv :
    (𝔭.adicCompletion F ⊗[F] A)ˣ ≃*
      (Π w : FinitePlacesAbove K 𝔭, (w.1.adicCompletion K ⊗[K] A)ˣ) :=
  (Units.mapEquiv (placeTensorEquiv 𝔭 A).toMulEquiv).trans MulEquiv.piUnits

theorem placeUnitsEquiv_apply (g : (𝔭.adicCompletion F ⊗[F] A)ˣ)
    (w : FinitePlacesAbove K 𝔭) :
    ((placeUnitsEquiv 𝔭 A g w : (w.1.adicCompletion K ⊗[K] A)ˣ) :
        w.1.adicCompletion K ⊗[K] A) =
      placeTensorEquiv 𝔭 A g w := rfl

end Decomposition

section Split

variable {F : Type u} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 ℚ))

/-- If a number field `F` has at least `[F : ℚ]` finite places above the rational place `v`,
each completion of `F` above `v` has degree one over `ℚ_v`. -/
theorem finrank_completion_eq_one
    (hcard : Module.finrank ℚ F ≤ Fintype.card (FinitePlacesAbove F v))
    (𝔭 : FinitePlacesAbove F v) :
    Module.finrank (v.adicCompletion ℚ) (𝔭.1.adicCompletion F) = 1 := by
  classical
  have hfin : ∀ 𝔮 : FinitePlacesAbove F v,
      Module.Finite (v.adicCompletion ℚ) (𝔮.1.adicCompletion F) :=
    fun 𝔮 => FiniteExtension.local_finite v 𝔮.1
  let e := LinearEquiv.ofBijective (finiteTensorMap (L := F) v).toLinearMap
    ((completedTensorComparison ℚ F).1 v)
  have hsum : ∑ 𝔮 : FinitePlacesAbove F v,
      Module.finrank (v.adicCompletion ℚ) (𝔮.1.adicCompletion F) = Module.finrank ℚ F := by
    rw [← Module.finrank_pi_fintype, ← e.finrank_eq, Module.finrank_baseChange]
  have hpos : ∀ 𝔮 : FinitePlacesAbove F v,
      1 ≤ Module.finrank (v.adicCompletion ℚ) (𝔮.1.adicCompletion F) := fun 𝔮 =>
    Module.finrank_pos
  have hle : Module.finrank (v.adicCompletion ℚ) (𝔭.1.adicCompletion F) +
      (Fintype.card (FinitePlacesAbove F v) - 1) ≤ Module.finrank ℚ F := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ 𝔭)]
    gcongr
    calc Fintype.card (FinitePlacesAbove F v) - 1
        = ∑ 𝔮 ∈ Finset.univ.erase 𝔭, 1 := by
          simp [Finset.card_erase_of_mem]
      _ ≤ _ := Finset.sum_le_sum fun 𝔮 _ => hpos 𝔮
  have hcardpos : 1 ≤ Fintype.card (FinitePlacesAbove F v) := Fintype.card_pos_iff.mpr ⟨𝔭⟩
  have h𝔭 := hpos 𝔭
  omega

/-- Under the same hypothesis, the completion map `ℚ_v → F_𝔭` is bijective. -/
theorem completionMap_bijective_of_le_card
    (hcard : Module.finrank ℚ F ≤ Fintype.card (FinitePlacesAbove F v))
    (𝔭 : FinitePlacesAbove F v) :
    Function.Bijective (FiniteExtension.completionMap v 𝔭.1) :=
  Module.Free.bijective_algebraMap_of_finrank_eq_one (finrank_completion_eq_one v hcard 𝔭)

end Split

end Langlands.Shimura.PlaceTensor
