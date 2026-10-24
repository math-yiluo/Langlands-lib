import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Jacquet.Localization

/-! The finite external tensor product commutes with character-localized coinvariants. -/

noncomputable section

open Function
open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uR uI uG uV uW

variable {R : Type uR} [CommRing R] {ι : Type uI} [Fintype ι]
variable {H : ι → Type uG} [∀ i, Group (H i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The product of the given characters on the actual product subgroup. -/
def productCharacter (U : ∀ i, Subgroup (H i)) (θ : ∀ i, U i →* Rˣ) :
    Subgroup.pi Set.univ U →* Rˣ where
  toFun u := ∏ i, θ i ⟨u.val i, u.property i (Set.mem_univ i)⟩
  map_one' := by
    change (∏ i, θ i 1) = 1
    simp
  map_mul' u v := by
    change (∏ i, θ i (⟨u.val i, u.property i (Set.mem_univ i)⟩ *
      ⟨v.val i, v.property i (Set.mem_univ i)⟩)) = _
    simp only [map_mul, Finset.prod_mul_distrib]

@[simp] theorem productCharacter_apply (U : ∀ i, Subgroup (H i))
    (θ : ∀ i, U i →* Rˣ) (u : Subgroup.pi Set.univ U) :
    productCharacter U θ u = ∏ i, θ i ⟨u.val i, u.property i (Set.mem_univ i)⟩ := rfl

@[simp] theorem coe_productCharacter (U : ∀ i, Subgroup (H i))
    (θ : ∀ i, U i →* Rˣ) (u : Subgroup.pi Set.univ U) :
    (productCharacter U θ u : R) =
      ∏ i, (θ i ⟨u.val i, u.property i (Set.mem_univ i)⟩ : R) := by
  simp [productCharacter]

open Jacquet.Localization

variable (ρ : ∀ i, Representation R (H i) (V i))
variable (U : ∀ i, Subgroup (H i)) (θ : ∀ i, U i →* Rˣ)

/-- Tensoring the factor quotient maps satisfies the product character relation. -/
theorem map_mk_external (u : Subgroup.pi Set.univ U) (x : PiTensorProduct R V) :
    PiTensorProduct.map (fun i => mk (ρ i) (U i) (θ i)) (external ρ u x) =
      (productCharacter U θ u : R) •
        PiTensorProduct.map (fun i => mk (ρ i) (U i) (θ i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simp only [map_smul, external_tprod, PiTensorProduct.map_tprod]
    simp_rw [mk_apply_subgroup (ρ := ρ _) (U := U _) (θ := θ _)
      (u := ⟨u.val _, u.property _ (Set.mem_univ _)⟩)]
    rw [MultilinearMap.map_smul_univ, coe_productCharacter, smul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- The comparison map induced by the character quotient universal property. -/
def characterLocalizationToTensor :
    Coinvariants (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ) →ₗ[R]
      PiTensorProduct R (fun i => Coinvariants (ρ i) (U i) (θ i)) :=
  lift (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ)
    (PiTensorProduct.map (fun i => mk (ρ i) (U i) (θ i)))
    (map_mk_external ρ U θ)

@[simp] theorem characterLocalizationToTensor_mk_tprod (v : ∀ i, V i) :
    characterLocalizationToTensor ρ U θ
      (mk (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ)
        (PiTensorProduct.tprod R v)) =
      PiTensorProduct.tprod R (fun i => mk (ρ i) (U i) (θ i) (v i)) := by
  exact PiTensorProduct.map_tprod _ _

section MultilinearQuotient

variable {W : Type uW} [AddCommGroup W] [Module R W]
variable [dec : DecidableEq ι]

private theorem multilinear_quotient_congr (p : ∀ i, Submodule R (V i))
    (f : MultilinearMap R V W)
    (hf : ∀ v i, p i ≤ LinearMap.ker (f.toLinearMap v i))
    (a b : ∀ i, V i) (hab : ∀ i, (p i).mkQ (a i) = (p i).mkQ (b i)) :
    f a = f b := by
  have hstep (v : ∀ i, V i) (i : ι) :
      f (update v i (a i)) = f (update v i (b i)) :=
    congrArg ((p i).liftQ (f.toLinearMap v i) (hf v i)) (hab i)
  have h (s : Finset ι) : f (s.piecewise a b) = f b := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.piecewise_insert, hstep]
      rw [← Finset.piecewise_eq_of_notMem s a b hi, update_eq_self]
      exact ih
  simpa using h Finset.univ

/-- Internal simultaneous quotient descent, using the kernel condition in each slot. -/
private def multilinearQuotient (p : ∀ i, Submodule R (V i))
    (f : MultilinearMap R V W)
    (hf : ∀ v i, p i ≤ LinearMap.ker (f.toLinearMap v i)) :
    MultilinearMap R (fun i => V i ⧸ p i) W := by
  let F : (∀ i, V i ⧸ p i) → W := fun q =>
    Quotient.finLiftOn q f (fun a b hab =>
      multilinear_quotient_congr p f hf a b (fun i => Quotient.sound (hab i)))
  have hF (v : ∀ i, V i) : F (fun i => (p i).mkQ (v i)) = f v := by
    exact congrFun (congrFun (Quotient.finLiftOn_mk v) f) _
  have hupdate (v : ∀ i, V i) (i : ι) (x : V i) :
      update (fun j => (p j).mkQ (v j)) i ((p i).mkQ x) =
        fun j => (p j).mkQ (update v i x j) :=
    (funext (Function.apply_update (fun j z => (p j).mkQ z) v i x)).symm
  refine { toFun := F, map_update_add' := ?_, map_update_smul' := ?_ }
  · intro dec' q i x y
    have : dec' = dec := Subsingleton.elim _ _
    subst dec'
    choose v hv using fun i => (p i).mkQ_surjective (q i)
    obtain rfl : q = (fun i => (p i).mkQ (v i)) := (funext hv).symm
    obtain ⟨x, rfl⟩ := (p i).mkQ_surjective x
    obtain ⟨y, rfl⟩ := (p i).mkQ_surjective y
    rw [← map_add]
    simp only [hupdate, hF]
    exact f.map_update_add v i x y
  · intro dec' q i c x
    have : dec' = dec := Subsingleton.elim _ _
    subst dec'
    choose v hv using fun i => (p i).mkQ_surjective (q i)
    obtain rfl : q = (fun i => (p i).mkQ (v i)) := (funext hv).symm
    obtain ⟨x, rfl⟩ := (p i).mkQ_surjective x
    rw [← map_smul]
    simp only [hupdate, hF]
    exact f.map_update_smul v i c x

private theorem multilinearQuotient_mk (p : ∀ i, Submodule R (V i))
    (f : MultilinearMap R V W)
    (hf : ∀ v i, p i ≤ LinearMap.ker (f.toLinearMap v i)) (v : ∀ i, V i) :
    multilinearQuotient p f hf (fun i => (p i).mkQ (v i)) = f v := by
  exact congrFun (congrFun (Quotient.finLiftOn_mk v) f) _

end MultilinearQuotient

section Inverse

private def singleSubgroup [DecidableEq ι] (i : ι) (u : U i) :
    Subgroup.pi Set.univ U :=
  ⟨Pi.mulSingle i (u : H i), (Subgroup.mulSingle_mem_pi i _).mpr (fun _ => u.property)⟩

private theorem productCharacter_single [DecidableEq ι] (i : ι) (u : U i) :
    productCharacter U θ (singleSubgroup U i u) = θ i u := by
  rw [productCharacter_apply, Finset.prod_eq_single i]
  · congr 1
    apply Subtype.ext
    exact Pi.mulSingle_eq_same i (u : H i)
  · intro j _ hji
    have h : (⟨(singleSubgroup U i u).val j,
        (singleSubgroup U i u).property j (Set.mem_univ j)⟩ : U j) = 1 := by
      apply Subtype.ext
      exact Pi.mulSingle_eq_of_ne hji _
    rw [h, map_one]
  · simp

omit [Fintype ι] in
private theorem external_single_tprod_update [DecidableEq ι]
    (v : ∀ i, V i) (i : ι) (u : U i) (x : V i) :
    external ρ (singleSubgroup U i u) (PiTensorProduct.tprod R (update v i x)) =
      PiTensorProduct.tprod R (update v i (ρ i u x)) := by
  rw [external_tprod]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp [singleSubgroup]
  · simp [singleSubgroup, hji]

/-- The pure-tensor quotient map kills the character relations in each coordinate. -/
private theorem characterLocalization_slot_kernel [DecidableEq ι]
    (v : ∀ i, V i) (i : ι) :
    relations (ρ i) (U i) (θ i) ≤ LinearMap.ker
      (((mk (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ)).compMultilinearMap
        (PiTensorProduct.tprod R)).toLinearMap v i) := by
  rw [relations_le_ker_iff]
  intro u x
  have h := mk_apply_subgroup (external ρ) (Subgroup.pi Set.univ U)
    (productCharacter U θ) (singleSubgroup U i u)
    (PiTensorProduct.tprod R (update v i x))
  rw [external_single_tprod_update, productCharacter_single] at h
  exact h

/-- The inverse comparison, descending the pure-tensor quotient map in every slot. -/
def tensorToCharacterLocalization :
    PiTensorProduct R (fun i => Coinvariants (ρ i) (U i) (θ i)) →ₗ[R]
      Coinvariants (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ) := by
  classical
  exact PiTensorProduct.lift (multilinearQuotient (fun i => relations (ρ i) (U i) (θ i))
    ((mk (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ)).compMultilinearMap
      (PiTensorProduct.tprod R)) (characterLocalization_slot_kernel ρ U θ))

@[simp] theorem tensorToCharacterLocalization_tprod_mk (v : ∀ i, V i) :
    tensorToCharacterLocalization ρ U θ
      (PiTensorProduct.tprod R (fun i => mk (ρ i) (U i) (θ i) (v i))) =
      mk (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ)
        (PiTensorProduct.tprod R v) := by
  classical
  rw [tensorToCharacterLocalization, PiTensorProduct.lift.tprod]
  exact multilinearQuotient_mk _ _ _ v

/-- Descending to the tensor of quotients and back is the identity. -/
theorem tensorToCharacterLocalization_comp_toTensor :
    tensorToCharacterLocalization ρ U θ ∘ₗ characterLocalizationToTensor ρ U θ =
      LinearMap.id := by
  apply hom_ext
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.id_apply, characterLocalizationToTensor_mk_tprod,
    tensorToCharacterLocalization_tprod_mk]

/-- Descending to the product quotient and back is the identity. -/
theorem characterLocalizationToTensor_comp_toLocalization :
    characterLocalizationToTensor ρ U θ ∘ₗ tensorToCharacterLocalization ρ U θ =
      LinearMap.id := by
  ext q
  choose v hv using fun i => mk_surjective (ρ i) (U i) (θ i) (q i)
  obtain rfl : q = (fun i => mk (ρ i) (U i) (θ i) (v i)) := (funext hv).symm
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.id_apply, tensorToCharacterLocalization_tprod_mk,
    characterLocalizationToTensor_mk_tprod]

/-- The canonical quotient-universal-property comparison for a finite external tensor product. -/
def characterLocalizationEquiv :
    Coinvariants (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ) ≃ₗ[R]
      PiTensorProduct R (fun i => Coinvariants (ρ i) (U i) (θ i)) :=
  LinearEquiv.ofLinearMap (characterLocalizationToTensor ρ U θ)
    (tensorToCharacterLocalization ρ U θ)
    (characterLocalizationToTensor_comp_toLocalization ρ U θ)
    (tensorToCharacterLocalization_comp_toTensor ρ U θ)

@[simp] theorem characterLocalizationEquiv_mk_tprod (v : ∀ i, V i) :
    characterLocalizationEquiv ρ U θ
      (mk (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ)
        (PiTensorProduct.tprod R v)) =
      PiTensorProduct.tprod R (fun i => mk (ρ i) (U i) (θ i) (v i)) :=
  characterLocalizationToTensor_mk_tprod ρ U θ v

@[simp] theorem characterLocalizationEquiv_symm_tprod_mk (v : ∀ i, V i) :
    (characterLocalizationEquiv ρ U θ).symm
      (PiTensorProduct.tprod R (fun i => mk (ρ i) (U i) (θ i) (v i))) =
      mk (external ρ) (Subgroup.pi Set.univ U) (productCharacter U θ)
        (PiTensorProduct.tprod R v) :=
  tensorToCharacterLocalization_tprod_mk ρ U θ v

end Inverse

end Langlands.FiniteTensor
