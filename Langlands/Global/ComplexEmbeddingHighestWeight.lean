import Langlands.Global.ComplexEmbeddingEnveloping
import Langlands.Representation.Archimedean.UpperVermaCharacter
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.PiTensorProduct

/-! Highest-weight characters in the actual totally complex archimedean center. -/

noncomputable section

open scoped Classical TensorProduct
open NumberField
open Langlands.Algebra Langlands.Algebra.LieEnvelopingEquiv
open Langlands.Archimedean Langlands.Archimedean.VermaGL Langlands.Archimedean.VermaShifted
open UniversalEnvelopingAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F] (n : ℕ)

local notation "J" => EmbeddingIndex F
local notation "CM" => Matrix (Fin n) (Fin n) ℂ
local notation "T" => (⨂[ℂ] _ : J, glU n)

variable (μ : EmbeddingIndex F → Fin n → ℂ)

private abbrev Factor (j : J) := LowerVerma n (fun i => μ j i.rev)

private abbrev WeightTensor := ⨂[ℂ] j : J, Factor F n μ j

private def factorGenerator (j : J) : Factor F n μ j := gen n (fun i => μ j i.rev)

private def weightVector : WeightTensor F n μ := PiTensorProduct.tprod ℂ (factorGenerator F n μ)

omit [IsTotallyComplex F] in
private theorem weightVector_ne_zero : weightVector F n μ ≠ 0 := by
  have h (j : J) : ∃ f : Factor F n μ j →ₗ[ℂ] ℂ, f (factorGenerator F n μ j) = 1 :=
    Module.Projective.exists_dual_eq_one ℂ (Langlands.Archimedean.VermaPBW.gen_ne_zero n _)
  choose f hf using h
  intro hv
  have hx := congrArg (PiTensorProduct.map f) hv
  simp only [weightVector, PiTensorProduct.map_tprod, map_zero, hf] at hx
  have hy := congrArg (PiTensorProduct.constantBaseRingEquiv (ι := J) (R := ℂ)) hx
  exact one_ne_zero (by simpa only [PiTensorProduct.constantBaseRingEquiv_tprod,
    Finset.prod_const_one, map_zero] using hy)

private def tensorAction : T →ₐ[ℂ] Module.End ℂ (WeightTensor F n μ) :=
  PiTensorProduct.liftAlgHom
    ((PiTensorProduct.mapMultilinear ℂ (Factor F n μ) (Factor F n μ)).compLinearMap
      (fun j => (upperAction n (μ j)).toLinearMap))
    (by
      change PiTensorProduct.map (fun j => upperAction n (μ j) 1) = 1
      simp only [map_one, PiTensorProduct.map_one])
    (by
      intro a b
      change PiTensorProduct.map (fun j => upperAction n (μ j) (a j * b j)) =
        PiTensorProduct.map (fun j => upperAction n (μ j) (a j)) *
          PiTensorProduct.map (fun j => upperAction n (μ j) (b j))
      simp only [map_mul]
      exact PiTensorProduct.map_mul (fun j : J => upperAction n (μ j) (a j))
        (fun j : J => upperAction n (μ j) (b j)))

omit [NumberField F] [IsTotallyComplex F] in
private theorem tensorAction_tprod (a : J → glU n) :
    tensorAction F n μ (PiTensorProduct.tprod ℂ a) =
      PiTensorProduct.map (fun j => upperAction n (μ j) (a j)) := by
  rw [tensorAction, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod]
  rfl

private def tensorBlockGenerator (j : J) : CM →ₗ⁅ℂ⁆ T :=
  (PiTensorProduct.singleAlgHom (R := ℂ) (A := fun _ : J => glU n) j).toLieHom.comp (ι ℂ)

omit [NumberField F] [IsTotallyComplex F] in
private theorem tensorBlockGenerator_bracket_zero {j k : J} (h : k ≠ j) (X Y : CM) :
    ⁅tensorBlockGenerator F n j X, tensorBlockGenerator F n k Y⁆ = 0 := by
  apply sub_eq_zero.mpr
  change Commute (PiTensorProduct.tprod ℂ (Pi.mulSingle j (ι ℂ X) : J → glU n))
    (PiTensorProduct.tprod ℂ (Pi.mulSingle k (ι ℂ Y) : J → glU n))
  apply Commute.tprod
  apply Commute.pi
  intro i
  by_cases hi : i = j
  · subst i
    rw [Pi.mulSingle_eq_of_ne h.symm]
    exact Commute.one_right _
  · rw [Pi.mulSingle_eq_of_ne hi]
    exact Commute.one_left _

private def tensorGenerator : (J → CM) →ₗ⁅ℂ⁆ T :=
  { (∑ j : J, (tensorBlockGenerator F n j).toLinearMap.comp
      (LinearMap.proj j : (J → CM) →ₗ[ℂ] CM)) with
    map_lie' := by
      intro X Y
      change (∑ j : J, (tensorBlockGenerator F n j).toLinearMap.comp
        (LinearMap.proj j : (J → CM) →ₗ[ℂ] CM)) ⁅X, Y⁆ =
          ⁅(∑ j : J, (tensorBlockGenerator F n j).toLinearMap.comp
              (LinearMap.proj j : (J → CM) →ₗ[ℂ] CM)) X,
            (∑ j : J, (tensorBlockGenerator F n j).toLinearMap.comp
              (LinearMap.proj j : (J → CM) →ₗ[ℂ] CM)) Y⁆
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
        LinearMap.proj_apply]
      change (∑ j : J, tensorBlockGenerator F n j ⁅X j, Y j⁆) =
        ⁅(∑ j : J, tensorBlockGenerator F n j (X j)),
          ∑ j : J, tensorBlockGenerator F n j (Y j)⁆
      rw [sum_lie_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [LieHom.map_lie, Finset.sum_eq_single j]
      · intro k _ hk
        exact tensorBlockGenerator_bracket_zero F n hk _ _
      · simp }

omit [IsTotallyComplex F] in
private theorem tensorGenerator_lieSingle (j : J) (X : CM) :
    tensorGenerator F n (ProductLieEnveloping.lieSingle (K := ℂ) j X) =
      tensorBlockGenerator F n j X := by
  change (∑ k : J, (tensorBlockGenerator F n k).toLinearMap.comp
    (LinearMap.proj k : (J → CM) →ₗ[ℂ] CM)) (ProductLieEnveloping.lieSingle (K := ℂ) j X) = _
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LinearMap.proj_apply, ProductLieEnveloping.lieSingle_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    let : DecidableEq J := Classical.decEq J
    have hzero : (Pi.single j X : J → CM) k = 0 :=
      Pi.single_eq_of_ne (M := fun _ : J => CM) hk X
    rw [hzero, map_zero]
  · simp

private def tensorEnveloping : EnvelopingAlgebra F n →ₐ[ℂ] T :=
  lift ℂ ((tensorGenerator F n).comp (complexEmbeddingLieCoordinates F n).toLieHom)

private theorem tensorEnveloping_inclusion (j : J) (a : glU n) :
    tensorEnveloping F n (complexEmbeddingEnvelopingInclusion F n j a) =
      PiTensorProduct.singleAlgHom (R := ℂ) (A := fun _ : J => glU n) j a := by
  have h : (tensorEnveloping F n).comp (complexEmbeddingEnvelopingInclusion F n j) =
      PiTensorProduct.singleAlgHom (R := ℂ) (A := fun _ : J => glU n) j := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro X
    change tensorEnveloping F n (LieEnvelopingEquiv.map (complexEmbeddingLieInclusion F n j)
      (ι ℂ X)) = _
    rw [map_generator, tensorEnveloping, lift_ι_apply]
    simp only [LieHom.comp_apply, LieEquiv.coe_coe, complexEmbeddingLieInclusion,
      LieEquiv.apply_symm_apply, tensorGenerator_lieSingle]
    rfl
  exact DFunLike.congr_fun h a

private def weightAction : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ (WeightTensor F n μ) :=
  (tensorAction F n μ).comp (tensorEnveloping F n)

private theorem weightAction_inclusion (j : J) (a : glU n) (c : ℂ)
    (h : upperAction n (μ j) a (factorGenerator F n μ j) = c • factorGenerator F n μ j) :
    weightAction F n μ (complexEmbeddingEnvelopingInclusion F n j a) (weightVector F n μ) =
      c • weightVector F n μ := by
  rw [weightAction, AlgHom.comp_apply, tensorEnveloping_inclusion]
  change tensorAction F n μ (PiTensorProduct.tprod ℂ (Pi.mulSingle j a : J → glU n)) _ = _
  rw [tensorAction_tprod, weightVector, PiTensorProduct.map_tprod]
  have he : (fun k : J => upperAction n (μ k) ((Pi.mulSingle j a : J → glU n) k)
      (factorGenerator F n μ k)) =
      Function.update (factorGenerator F n μ) j (c • factorGenerator F n μ j) := by
    funext k
    by_cases hk : k = j
    · subst k
      simpa only [Pi.mulSingle_eq_same, Function.update_self] using h
    · simp only [Pi.mulSingle_eq_of_ne hk, Function.update_of_ne hk, map_one, Module.End.one_apply]
  rw [he, MultilinearMap.map_update_smul, Function.update_eq_self]

private def centerWeightAction : EnvelopingCenter F n →ₐ[ℂ] Module.End ℂ (WeightTensor F n μ) :=
  (weightAction F n μ).comp (centerInclusion F n)

private theorem centerWeightAction_inclusion (j : J) (z : VermaGL.center n) :
    centerWeightAction F n μ (complexEmbeddingCenterInclusion F n j z) (weightVector F n μ) =
      upperCharacter n (μ j) z • weightVector F n μ := by
  rw [centerWeightAction, AlgHom.comp_apply, centerInclusion_apply, complexEmbeddingCenterInclusion_val]
  apply weightAction_inclusion
  exact upperCharacter_action n (μ j) (upperAction n (μ j)) (factorGenerator F n μ j)
    (fun _ _ hpq => upperAction_unitU_of_lt n (μ j) hpq) (upperAction_unitU_diag n (μ j)) z

private def weightEigenlineAlgebra : Subalgebra ℂ (EnvelopingCenter F n) where
  carrier := {z | ∃ c : ℂ, centerWeightAction F n μ z (weightVector F n μ) = c • weightVector F n μ}
  zero_mem' := ⟨0, by rw [map_zero, LinearMap.zero_apply, zero_smul]⟩
  one_mem' := ⟨1, by rw [map_one, Module.End.one_apply, one_smul]⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simp only [map_add, LinearMap.add_apply, ha, hb, add_smul]⟩
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simp only [map_mul, Module.End.mul_apply, hb, map_smul, ha,
      smul_smul, mul_comm b a]⟩
  algebraMap_mem' c := ⟨c, by rw [AlgHom.commutes, Module.algebraMap_end_apply]⟩

private theorem centerWeightAction_scalar (z : EnvelopingCenter F n) :
    ∃ c : ℂ, centerWeightAction F n μ z (weightVector F n μ) = c • weightVector F n μ := by
  have h : (⨆ j : J, (complexEmbeddingCenterInclusion F n j).range) ≤
      weightEigenlineAlgebra F n μ := by
    apply iSup_le
    intro j
    rintro _ ⟨c, rfl⟩
    exact ⟨_, centerWeightAction_inclusion F n μ j c⟩
  rw [iSup_complexEmbeddingCenterInclusion_range] at h
  exact h (show z ∈ (⊤ : Subalgebra ℂ _) by trivial)

private def weightValue (z : EnvelopingCenter F n) : ℂ :=
  Classical.choose (centerWeightAction_scalar F n μ z)

private theorem weightValue_spec (z : EnvelopingCenter F n) :
    centerWeightAction F n μ z (weightVector F n μ) = weightValue F n μ z • weightVector F n μ :=
  Classical.choose_spec (centerWeightAction_scalar F n μ z)

private theorem weightValue_eq (z : EnvelopingCenter F n) (c : ℂ)
    (h : centerWeightAction F n μ z (weightVector F n μ) = c • weightVector F n μ) :
    weightValue F n μ z = c :=
  smul_left_injective ℂ (weightVector_ne_zero F n μ) ((weightValue_spec F n μ z).symm.trans h)

/-- The actual global center character of an upper highest weight. -/
def globalHighestWeightCharacter : EnvelopingCenter F n →ₐ[ℂ] ℂ where
  toFun := weightValue F n μ
  map_zero' := weightValue_eq F n μ _ _ (by simp)
  map_one' := weightValue_eq F n μ _ _ (by rw [map_one, Module.End.one_apply, one_smul])
  map_add' x y := weightValue_eq F n μ _ _ (by
    simp only [map_add, LinearMap.add_apply, weightValue_spec F n μ, add_smul])
  map_mul' x y := weightValue_eq F n μ _ _ (by
    simp only [map_mul, Module.End.mul_apply, weightValue_spec F n μ, map_smul, smul_smul, mul_comm])
  commutes' c := weightValue_eq F n μ _ _ (by
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    rfl)

/-- The global highest-weight character restricts to the upper Verma character on each block. -/
@[simp] theorem globalHighestWeightCharacter_inclusion (j : J) (z : VermaGL.center n) :
    globalHighestWeightCharacter F n μ (complexEmbeddingCenterInclusion F n j z) =
      upperCharacter n (μ j) z :=
  weightValue_eq F n μ _ _ (centerWeightAction_inclusion F n μ j z)

private theorem weightAction_real (X : ArchimedeanMatrix F n) :
    weightAction F n μ (realGenerator F n X) (weightVector F n μ) =
      ∑ j : J, weightAction F n μ (complexEmbeddingEnvelopingInclusion F n j
        (ι ℂ ((embeddingComponent F j).mapMatrix X))) (weightVector F n μ) := by
  have h (j : J) : complexEmbeddingLieCoordinates F n
      (complexify F n ((realLieAlgebraToMatrix F n).symm X)) j =
      (embeddingComponent F j).mapMatrix X := by
    ext p q
    exact complexEmbeddingLieCoordinates_complexify F n X j p q
  simp only [weightAction, AlgHom.comp_apply, tensorEnveloping_inclusion]
  change tensorAction F n μ
    (lift ℂ ((tensorGenerator F n).comp (complexEmbeddingLieCoordinates F n).toLieHom)
      (ι ℂ (complexify F n ((realLieAlgebraToMatrix F n).symm X)))) _ = _
  rw [lift_ι_apply]
  simp only [LieHom.comp_apply, LieEquiv.coe_coe]
  change tensorAction F n μ
    ((∑ j : J, (tensorBlockGenerator F n j).toLinearMap.comp
      (LinearMap.proj j : (J → CM) →ₗ[ℂ] CM))
        (complexEmbeddingLieCoordinates F n (complexify F n ((realLieAlgebraToMatrix F n).symm X)))) _ = _
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, h, map_sum]
  rfl

private theorem weightAction_single (j : J) (p q : Fin n) (a c : ℂ)
    (h : upperAction n (μ j) (unitU n p q) (factorGenerator F n μ j) =
      c • factorGenerator F n μ j) :
    weightAction F n μ (complexEmbeddingEnvelopingInclusion F n j
      (ι ℂ (Matrix.single p q a))) (weightVector F n μ) = (a * c) • weightVector F n μ := by
  have hm : Matrix.single p q a = a • Matrix.single p q (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul, map_smul, LinearMap.smul_apply,
    weightAction_inclusion F n μ j _ c h, smul_smul]

private def weightModule : ModuleCat.{u} (EnvelopingAlgebra F n) :=
  letI : Module (EnvelopingAlgebra F n) (WeightTensor F n μ) :=
    Module.compHom _ (weightAction F n μ).toRingHom
  ModuleCat.of _ (WeightTensor F n μ)

private theorem weightAction_algebraMap (c : ℂ) :
    weightAction F n μ (algebraMap ℂ (EnvelopingAlgebra F n) c) (weightVector F n μ) =
      c • weightVector F n μ := by
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

/-- The external tensor of the upper Verma generators witnesses the published highest-weight predicate. -/
theorem isHighestWeightCharacter_globalHighestWeightCharacter :
    IsHighestWeightCharacter F n μ (globalHighestWeightCharacter F n μ) := by
  refine ⟨weightModule F n μ, weightVector F n μ, ⟨weightVector_ne_zero F n μ, ?_, ?_⟩, ?_⟩
  · intro d
    change weightAction F n μ (realGenerator F n (Matrix.diagonal d)) (weightVector F n μ) =
      weightAction F n μ (algebraMap ℂ _ (diagonalWeight F n μ d)) (weightVector F n μ)
    rw [weightAction_real, weightAction_algebraMap]
    simp only [diagonalWeight, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j _
    have hd : (embeddingComponent F j).mapMatrix (Matrix.diagonal d) =
        Matrix.diagonal (fun i => embeddingComponent F j (d i)) := by
      ext p q
      by_cases hpq : p = q <;> simp [AlgHom.mapMatrix, hpq]
    rw [hd, ← Matrix.sum_single_eq_diagonal]
    simp only [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [weightAction_single F n μ j p p _ _ (upperAction_unitU_diag n (μ j) p), mul_comm]
  · intro p q hpq a
    change weightAction F n μ (realGenerator F n (Matrix.single p q a)) (weightVector F n μ) = 0
    rw [weightAction_real]
    apply Finset.sum_eq_zero
    intro j _
    have h : (embeddingComponent F j).mapMatrix (Matrix.single p q a) =
        Matrix.single p q (embeddingComponent F j a) := by
      ext i k
      by_cases hi : p = i <;> by_cases hk : q = k <;>
        simp [AlgHom.mapMatrix, hi, hk]
    rw [h, weightAction_single F n μ j p q _ 0]
    · rw [mul_zero, zero_smul]
    · simpa only [factorGenerator, zero_smul] using upperAction_unitU_of_lt n (μ j) hpq
  · intro z
    change centerWeightAction F n μ z (weightVector F n μ) =
      weightAction F n μ (algebraMap ℂ _ (globalHighestWeightCharacter F n μ z)) (weightVector F n μ)
    rw [weightAction_algebraMap]
    exact weightValue_spec F n μ z

private theorem blockUnit_action_of_realUnit {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V) (v : V)
    (p q : Fin n) (b : J → ℂ)
    (h : ∀ a : mixedEmbedding.mixedSpace F,
      A (realGenerator F n (Matrix.single p q a)) v =
        (∑ k : J, b k * embeddingComponent F k a) • v)
    (j : J) :
    A (complexEmbeddingEnvelopingInclusion F n j (unitU n p q)) v = b j • v := by
  let E := complexEmbeddingLieCoordinates F n
  let entry (k : J) : ComplexLieAlgebra F n →ₗ[ℂ] ℂ :=
    (Matrix.entryLinearMap ℂ ℂ p q).comp ((LinearMap.proj k).comp E.toLinearMap)
  let P : ComplexLieAlgebra F n →ₗ[ℂ] ComplexLieAlgebra F n :=
    E.symm.toLinearMap.comp (LinearMap.pi fun k => (Matrix.singleLinearMap ℂ p q).comp (entry k))
  let c : ComplexLieAlgebra F n →ₗ[ℂ] ℂ := ∑ k : J, b k • entry k
  have hP (X : ComplexLieAlgebra F n) (k : J) : E (P X) k = Matrix.single p q (E X k p q) := by
    change E (E.symm _) k = _
    rw [LieEquiv.apply_symm_apply]
    rfl
  have hc (X : ComplexLieAlgebra F n) : c X = ∑ k : J, b k * E X k p q := by
    simp only [c, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  have hreal (X : RealLieAlgebra F n) :
      A (envelopingGenerator F n (P (complexify F n X))) v = c (complexify F n X) • v := by
    let M := realLieAlgebraToMatrix F n X
    have he (k : J) (i l : Fin n) : E (complexify F n X) k i l =
        embeddingComponent F k (M i l) := by
      dsimp only [M, E]
      simpa only [LinearEquiv.symm_apply_apply] using
        complexEmbeddingLieCoordinates_complexify F n (realLieAlgebraToMatrix F n X) k i l
    have hcut : P (complexify F n X) =
        complexify F n ((realLieAlgebraToMatrix F n).symm (Matrix.single p q (M p q))) := by
      apply E.injective
      funext k
      change E (P (complexify F n X)) k =
        E (complexify F n ((realLieAlgebraToMatrix F n).symm (Matrix.single p q (M p q)))) k
      rw [hP, he]
      ext i l
      rw [show E _ k i l = embeddingComponent F k (Matrix.single p q (M p q) i l) from
        complexEmbeddingLieCoordinates_complexify F n _ k i l]
      by_cases hi : p = i <;> by_cases hl : q = l <;> simp [hi, hl]
    rw [hcut, hc]
    simp_rw [he]
    exact h (M p q)
  have hall (X : ComplexLieAlgebra F n) : A (envelopingGenerator F n (P X)) v = c X • v := by
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      have hz : z ⊗ₜ[ℝ] X = z • complexify F n X := by
        rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hz]
      simp only [map_smul, LinearMap.smul_apply, hreal, smul_smul, smul_eq_mul]
    | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY, add_smul]
  let X := complexEmbeddingLieInclusion F n j (Matrix.single p q (1 : ℂ))
  let : DecidableEq J := Classical.decEq J
  have hX : E X = (Pi.single j (Matrix.single p q (1 : ℂ)) : J → CM) := by
    change E (E.symm (ProductLieEnveloping.lieSingle (K := ℂ) j _)) = _
    rw [LieEquiv.apply_symm_apply, ProductLieEnveloping.lieSingle_apply]
  have hPX : P X = X := by
    apply E.injective
    funext k
    change E (P X) k = E X k
    rw [hP, hX]
    by_cases hk : k = j
    · subst k
      simp
    · simp [hk]
  have hcX : c X = b j := by
    rw [hc, hX, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hx := hall X
  rw [hPX, hcX] at hx
  rw [complexEmbeddingEnvelopingInclusion, unitU, map_generator]
  exact hx

open scoped ModuleCat.Algebra in
/-- Every highest-weight witness gives the upper Verma character on each block. -/
theorem isHighestWeightCharacter_block
    (χ : EnvelopingCenter F n →ₐ[ℂ] ℂ) (hχ : IsHighestWeightCharacter F n μ χ)
    (j : J) (z : VermaGL.center n) :
    χ (complexEmbeddingCenterInclusion F n j z) = upperCharacter n (μ j) z := by
  obtain ⟨W, w, ⟨hw, hd, hu⟩, hz⟩ := hχ
  let A : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ W := Algebra.lsmul ℂ ℂ W
  let B := A.comp (complexEmbeddingEnvelopingInclusion F n j)
  have hu' (p q : Fin n) (hpq : p < q) : B (unitU n p q) w = 0 := by
    simpa only [B, AlgHom.comp_apply, zero_smul] using blockUnit_action_of_realUnit F n A w p q (fun _ => 0)
      (fun a => by
        simp only [zero_mul, Finset.sum_const_zero, zero_smul]
        exact hu p q hpq a) j
  have hd' (p : Fin n) : B (unitU n p p) w = μ j p • w := by
    apply blockUnit_action_of_realUnit F n A w p p (fun k => μ k p) _ j
    intro a
    have hdiag := hd (Pi.single p a)
    rw [Matrix.diagonal_single] at hdiag
    have he : diagonalWeight F n μ (Pi.single p a) = ∑ k : J, μ k p * embeddingComponent F k a := by
      unfold diagonalWeight
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_eq_single p]
      · simp
      · intro i _ hi
        simp [hi]
      · simp
    rw [he] at hdiag
    exact hdiag
  have hb := upperCharacter_action n (μ j) B w hu' hd' z
  have hg := hz (complexEmbeddingCenterInclusion F n j z)
  change A (complexEmbeddingCenterInclusion F n j z).val w =
    χ (complexEmbeddingCenterInclusion F n j z) • w at hg
  rw [complexEmbeddingCenterInclusion_val] at hg
  exact smul_left_injective ℂ hw (hg.symm.trans hb)

/-- The global highest-weight condition is equivalent to its block character restrictions. -/
theorem isHighestWeightCharacter_iff_block (χ : EnvelopingCenter F n →ₐ[ℂ] ℂ) :
    IsHighestWeightCharacter F n μ χ ↔
      ∀ j z, χ (complexEmbeddingCenterInclusion F n j z) = upperCharacter n (μ j) z := by
  refine ⟨isHighestWeightCharacter_block F n μ χ, fun h => ?_⟩
  have he : χ = globalHighestWeightCharacter F n μ :=
    complexEmbeddingCenter_hom_ext F n χ _ fun j z =>
      (h j z).trans (globalHighestWeightCharacter_inclusion F n μ j z).symm
  rw [he]
  exact isHighestWeightCharacter_globalHighestWeightCharacter F n μ

end Langlands.Global.ArchimedeanGL
