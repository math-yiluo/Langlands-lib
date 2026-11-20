import Langlands.Algebra.LieEnvelopingEquiv
import Langlands.Algebra.TensorProductCenter
import Mathlib.Algebra.Lie.Prod

/-! Enveloping algebras and their centers under products of Lie algebras. -/

noncomputable section

open scoped Classical TensorProduct
open UniversalEnvelopingAlgebra
open Langlands.Algebra.LieEnvelopingEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.ProductLieEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K]
local notation "U" => UniversalEnvelopingAlgebra K
local notation "Z" => Subalgebra.center K

section Binary

variable {L M A : Type*} [LieRing L] [LieAlgebra K L]
  [LieRing M] [LieAlgebra K M] [Ring A] [Algebra K A]

theorem map_comp {N : Type*} [LieRing N] [LieAlgebra K N]
    (f : M →ₗ⁅K⁆ N) (g : L →ₗ⁅K⁆ M) : (map f).comp (map g) = map (f.comp g) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  change map f (map g (ι K x)) = map (f.comp g) (ι K x)
  simp only [map_generator, LieHom.comp_apply]

/-- A subalgebra of the universal enveloping algebra containing all Lie generators is full. -/
theorem eq_top_of_generators (S : Subalgebra K (U L)) (h : ∀ x : L, ι K x ∈ S) : S = ⊤ := by
  refine top_unique (fun a _ => ?_)
  refine Quotient.inductionOn a ?_
  intro t
  change mkAlgHom K L t ∈ S
  induction t using TensorAlgebra.induction with
  | algebraMap c => rw [AlgHom.commutes]; exact S.algebraMap_mem c
  | ι x => exact h x
  | mul x y hx hy => rw [map_mul]; exact S.mul_mem hx hy
  | add x y hx hy => rw [map_add]; exact S.add_mem hx hy

/-- Commutation with the image of each Lie generator suffices to commute with the enveloping image. -/
theorem commute_of_generators
    (f : U L →ₐ[K] A) (x : A) (hx : ∀ y : L, Commute x (f (ι K y))) (a : U L) :
    Commute x (f a) := by
  refine Quotient.inductionOn a ?_
  intro t
  change Commute x (f (mkAlgHom K L t))
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (Algebra.commutes c x).symm
  | ι y => exact hx y
  | mul y z hy hz => simpa only [map_mul] using hy.mul_right hz
  | add y z hy hz => simpa only [map_add] using hy.add_right hz

/-- The two enveloping inclusions of a binary product. -/
def prodLeft : U L →ₐ[K] U (L × M) := map (LieHom.inl K L M)

def prodRight : U M →ₐ[K] U (L × M) := map (LieHom.inr K L M)

private theorem prodLeft_right_commute (a : U L) (b : U M) :
    Commute (prodLeft a) (prodRight b) := by
  apply Commute.symm
  apply commute_of_generators
  intro x
  apply Commute.symm
  apply commute_of_generators
  intro y
  rw [prodLeft, prodRight, map_generator, map_generator]
  apply sub_eq_zero.mp
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie]
  change ι K ((⁅x, (0 : L)⁆, ⁅(0 : M), y⁆) : L × M) = 0
  simp only [lie_zero, zero_lie]
  exact map_zero (ι K : (L × M) →ₗ⁅K⁆ U (L × M))

private def prodToTensorLie : (L × M) →ₗ⁅K⁆ (U L ⊗[K] U M) := by
  let f : L →ₗ⁅K⁆ (U L ⊗[K] U M) :=
    (Algebra.TensorProduct.includeLeft : U L →ₐ[K] _).toLieHom.comp (ι K)
  let g : M →ₗ⁅K⁆ (U L ⊗[K] U M) :=
    (Algebra.TensorProduct.includeRight : U M →ₐ[K] _).toLieHom.comp (ι K)
  have h (x : L) (y : M) : Commute (f x) (g y) :=
    (Commute.one_right (ι K x)).tmul (Commute.one_left (ι K y))
  have hfg (x : L) (y : M) : ⁅f x, g y⁆ = 0 := sub_eq_zero.mpr (h x y).eq
  have hgf (x : L) (y : M) : ⁅g y, f x⁆ = 0 := sub_eq_zero.mpr (h x y).symm.eq
  refine { (f.toLinearMap.comp (LinearMap.fst K L M) +
    g.toLinearMap.comp (LinearMap.snd K L M)) with map_lie' := ?_ }
  intro x y
  change f ⁅x.1, y.1⁆ + g ⁅x.2, y.2⁆ = ⁅f x.1 + g x.2, f y.1 + g y.2⁆
  simp only [add_lie, lie_add, LieHom.map_lie, hfg, hgf, zero_add, add_zero]

private def prodToTensor : U (L × M) →ₐ[K] U L ⊗[K] U M := lift K prodToTensorLie

private def tensorToProd : (U L ⊗[K] U M) →ₐ[K] U (L × M) :=
  Algebra.TensorProduct.lift prodLeft prodRight prodLeft_right_commute

private theorem prodToTensor_generator (x : L × M) :
    prodToTensor (ι K x) = (ι K x.1 ⊗ₜ[K] (1 : U M)) + ((1 : U L) ⊗ₜ[K] ι K x.2) :=
  lift_ι_apply K prodToTensorLie x

private theorem tensorToProd_tmul (a : U L) (b : U M) :
    tensorToProd (a ⊗ₜ[K] b) = prodLeft a * prodRight b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

/-- Enveloping a binary product of Lie algebras gives the tensor product of their enveloping algebras. -/
def prodEquiv : U (L × M) ≃ₐ[K] (U L ⊗[K] U M) := by
  refine AlgEquiv.ofAlgHom prodToTensor tensorToProd ?_ ?_
  · apply Algebra.TensorProduct.ext
    · apply UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      change prodToTensor (tensorToProd (ι K x ⊗ₜ[K] (1 : U M))) = ι K x ⊗ₜ[K] (1 : U M)
      simp only [tensorToProd_tmul, map_one, mul_one, prodLeft, map_generator,
        prodToTensor_generator, LieHom.inl_apply, map_zero, TensorProduct.tmul_zero, add_zero]
    · apply UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro y
      change prodToTensor (tensorToProd ((1 : U L) ⊗ₜ[K] ι K y)) = (1 : U L) ⊗ₜ[K] ι K y
      simp only [tensorToProd_tmul, map_one, one_mul, prodRight, map_generator,
        prodToTensor_generator, LieHom.inr_apply, map_zero, TensorProduct.zero_tmul, zero_add]
  · apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change tensorToProd (prodToTensor (ι K x)) = ι K x
    rw [prodToTensor_generator, map_add, tensorToProd_tmul, tensorToProd_tmul]
    simp only [map_one, mul_one, one_mul, prodLeft, prodRight, map_generator,
      LieHom.inl_apply, LieHom.inr_apply, ← map_add]
    congr 1
    exact Prod.ext (add_zero _) (zero_add _)

@[simp] theorem prodEquiv_symm_tmul (a : U L) (b : U M) :
    (prodEquiv (K := K) (L := L) (M := M)).symm (a ⊗ₜ[K] b) = prodLeft a * prodRight b :=
  tensorToProd_tmul a b

/-- The binary enveloping center lies in the subalgebra generated by the two images of centers. -/
theorem prod_center_le_sup : Z (U (L × M)) ≤
    (Z (U L)).map (prodLeft (K := K)) ⊔ (Z (U M)).map (prodRight (K := K)) := by
  intro z hz
  let e := prodEquiv (K := K) (L := L) (M := M)
  let t := TensorProductCenter.centerEquiv (K := K) (A := U L) (B := U M)
  obtain ⟨x, hx⟩ := t.surjective (LieEnvelopingEquiv.center e ⟨z, hz⟩)
  have h : e.symm (t x).val = z := by
    rw [hx, LieEnvelopingEquiv.center_apply, e.symm_apply_apply]
  rw [← h]
  clear h hx z hz
  let S : Subalgebra K (U (L × M)) :=
    (Z (U L)).map (prodLeft (K := K)) ⊔ (Z (U M)).map (prodRight (K := K))
  change e.symm (t x).val ∈ S
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProductCenter.centerEquiv_tmul, prodEquiv_symm_tmul]
    exact S.mul_mem
      ((le_sup_left : (Z (U L)).map (prodLeft (K := K)) ≤ S) ⟨a.val, a.property, rfl⟩)
      ((le_sup_right : (Z (U M)).map (prodRight (K := K)) ≤ S) ⟨b.val, b.property, rfl⟩)
  | add x y hx hy =>
    simpa only [map_add, Subalgebra.coe_add] using S.add_mem hx hy

end Binary

section FiniteProduct

variable {I L : Type*} [Ring L] [Algebra K L]

/-- The Lie inclusion supported at one coordinate of a product. -/
def lieSingle (i : I) : L →ₗ⁅K⁆ (I → L) :=
  { LinearMap.single K (fun _ : I => L) i with
    map_lie' := by
      intro x y
      funext j
      by_cases h : j = i
      · subst j
        simp
      · simp [h] }

@[simp] theorem lieSingle_apply (i : I) (x : L) :
    lieSingle (K := K) i x = Pi.single i x := rfl

/-- The enveloping inclusion supported at one coordinate. -/
def singleEnveloping (i : I) : U L →ₐ[K] U (I → L) := map (lieSingle i)

private def finSuccLieEquiv (m : ℕ) : (Fin (m + 1) → L) ≃ₗ⁅K⁆ (L × (Fin m → L)) where
  toFun X := (X 0, fun i => X i.succ)
  invFun X := Fin.cons X.1 X.2
  left_inv X := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv X := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

private theorem finSuccLieEquiv_symm_apply (m : ℕ) (x : L × (Fin m → L)) :
    (finSuccLieEquiv (K := K) m).symm x = Fin.cons x.1 x.2 := rfl

private theorem finSuccLieEquiv_symm_inl (m : ℕ) :
    (finSuccLieEquiv (K := K) (L := L) m).symm.toLieHom.comp
      (LieHom.inl K L (Fin m → L)) = lieSingle 0 := by
  apply LieHom.ext
  intro x
  funext i
  simp only [LieHom.comp_apply, LieEquiv.coe_coe, finSuccLieEquiv_symm_apply, lieSingle_apply,
    LieHom.inl_apply]
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem finSuccLieEquiv_symm_inr_single {m : ℕ} (i : Fin m) :
    ((finSuccLieEquiv (K := K) (L := L) m).symm.toLieHom.comp
      (LieHom.inr K L (Fin m → L))).comp (lieSingle i) = lieSingle i.succ := by
  apply LieHom.ext
  intro x
  funext j
  simp only [LieHom.comp_apply, LieEquiv.coe_coe, finSuccLieEquiv_symm_apply, lieSingle_apply,
    LieHom.inr_apply]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · by_cases h : k = i <;> simp [h]

private theorem fin_center_le (m : ℕ) : Z (U (Fin m → L)) ≤
    ⨆ i : Fin m, (Z (U L)).map (singleEnveloping i) := by
  induction m with
  | zero =>
    rw [iSup_of_empty]
    have h : (⊥ : Subalgebra K (U (Fin 0 → L))) = ⊤ :=
      eq_top_of_generators _ (fun x => by rw [Subsingleton.elim x 0, map_zero]; exact zero_mem _)
    rw [h]
    exact le_top
  | succ m ih =>
    let S : Subalgebra K (U (Fin (m + 1) → L)) :=
      ⨆ i : Fin (m + 1), (Z (U L)).map (singleEnveloping i)
    let e := enveloping (finSuccLieEquiv (K := K) (L := L) m)
    let f : U (L × (Fin m → L)) →ₐ[K] U (Fin (m + 1) → L) := e.symm.toAlgHom
    have hf : f = map (finSuccLieEquiv (K := K) (L := L) m).symm.toLieHom := rfl
    have hl : (Z (U L)).map (prodLeft (M := Fin m → L)) ≤ S.comap f := by
      rintro _ ⟨a, ha, rfl⟩
      change (f.comp prodLeft) a ∈ S
      rw [hf, prodLeft, map_comp, finSuccLieEquiv_symm_inl]
      exact le_iSup (fun i => (Z (U L)).map (singleEnveloping i)) 0 ⟨a, ha, rfl⟩
    have hr : (Z (U (Fin m → L))).map (prodRight (L := L)) ≤ S.comap f := by
      rintro _ ⟨a, ha, rfl⟩
      have htail : (⨆ i : Fin m, (Z (U L)).map (singleEnveloping i)) ≤
          S.comap (f.comp prodRight) := by
        apply iSup_le
        intro i
        rintro _ ⟨b, hb, rfl⟩
        change (((f.comp prodRight).comp (singleEnveloping i)) b) ∈ S
        rw [hf, prodRight, singleEnveloping, map_comp, map_comp, finSuccLieEquiv_symm_inr_single]
        exact le_iSup (fun j => (Z (U L)).map (singleEnveloping j)) i.succ ⟨b, hb, rfl⟩
      exact htail (ih ha)
    have hctr := prod_center_le_sup.trans (sup_le hl hr)
    intro a ha
    have hmem := hctr (LieEnvelopingEquiv.center e ⟨a, ha⟩).property
    change f (e a) ∈ S at hmem
    simpa only [f, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using hmem

private def reindexLieEquiv {J : Type*} (e : I ≃ J) : (I → L) ≃ₗ⁅K⁆ (J → L) where
  toFun f j := f (e.symm j)
  invFun f i := f (e i)
  left_inv f := by funext i; simp
  right_inv f := by funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

private theorem reindexLieEquiv_symm_apply {J : Type*} (e : I ≃ J) (x : J → L) (i : I) :
    (reindexLieEquiv (K := K) e).symm x i = x (e i) := rfl

/-- The enveloping center of a finite product lies in the subalgebra generated by the block centers. -/
theorem pi_center_le [Fintype I] : Z (U (I → L)) ≤
    ⨆ i : I, (Z (U L)).map (singleEnveloping i) := by
  let S : Subalgebra K (U (I → L)) := ⨆ i : I, (Z (U L)).map (singleEnveloping i)
  let σ := Fintype.equivFin I
  let e := enveloping (reindexLieEquiv (K := K) (L := L) σ)
  let f : U (Fin (Fintype.card I) → L) →ₐ[K] U (I → L) := e.symm.toAlgHom
  have hf : f = map (reindexLieEquiv (K := K) (L := L) σ).symm.toLieHom := rfl
  have hspan : (⨆ j : Fin (Fintype.card I), (Z (U L)).map (singleEnveloping j)) ≤ S.comap f := by
    apply iSup_le
    intro j
    rintro _ ⟨b, hb, rfl⟩
    change (f.comp (singleEnveloping j)) b ∈ S
    have h : (reindexLieEquiv (K := K) (L := L) σ).symm.toLieHom.comp (lieSingle j) =
        lieSingle (σ.symm j) := by
      apply LieHom.ext
      intro x
      funext i
      simp only [LieHom.comp_apply, LieEquiv.coe_coe, reindexLieEquiv_symm_apply, lieSingle_apply]
      by_cases hi : i = σ.symm j
      · subst i
        simp
      · have hj : σ i ≠ j := fun h => hi (σ.eq_symm_apply.mpr h)
        simp [hi, hj]
    rw [hf, singleEnveloping, map_comp, h]
    exact le_iSup (fun i => (Z (U L)).map (singleEnveloping i)) (σ.symm j) ⟨b, hb, rfl⟩
  intro a ha
  have hmem := hspan (fin_center_le _ (LieEnvelopingEquiv.center e ⟨a, ha⟩).property)
  change f (e a) ∈ S at hmem
  simpa only [f, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using hmem

/-- A block center includes into the center of the enveloping algebra of the product. -/
def singleCenter (i : I) : Z (U L) →ₐ[K] Z (U (I → L)) :=
  ((singleEnveloping i).comp (Z (U L)).val).codRestrict _ fun z => by
    rw [Subalgebra.mem_center_iff]
    intro a
    apply Commute.eq
    apply Commute.symm
    apply commute_of_generators (AlgHom.id K _)
    intro x
    let r : I → L := x - lieSingle (K := K) i (x i)
    have h (y : L) : ⁅r, lieSingle (K := K) i y⁆ = 0 := by
      funext j
      by_cases hj : j = i
      · subst j
        change ⁅x i - (Pi.single i (x i) : I → L) i, (Pi.single i y : I → L) i⁆ = 0
        simp
      · change ⁅r j, (Pi.single i y : I → L) j⁆ = 0
        simp [hj]
    have hr : Commute (ι K r) (singleEnveloping i z.val) := by
      apply commute_of_generators
      intro y
      rw [singleEnveloping, map_generator]
      apply sub_eq_zero.mp
      rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, h, map_zero]
    have hi : Commute (singleEnveloping i (ι K (x i))) (singleEnveloping i z.val) :=
      (show Commute (ι K (x i)) z.val from Subalgebra.mem_center_iff.mp z.property _).map
        (singleEnveloping i)
    have hx : ι K x = ι K r + singleEnveloping i (ι K (x i)) := by
      rw [singleEnveloping, map_generator, ← map_add, sub_add_cancel]
    apply Commute.symm
    change Commute (ι K x) (singleEnveloping i z.val)
    rw [hx]
    exact hr.add_left hi

@[simp] theorem singleCenter_coe (i : I) (z : Z (U L)) :
    (singleCenter i z).val = singleEnveloping i z.val := rfl

/-- The actual associative center of the enveloping algebra is generated by the block centers. -/
theorem iSup_singleCenter_range [Fintype I] :
    (⨆ i : I, (singleCenter (K := K) (L := L) i).range) = (⊤ : Subalgebra K (Z (U (I → L)))) := by
  let S : Subalgebra K (Z (U (I → L))) := ⨆ i : I, (singleCenter (K := K) (L := L) i).range
  have h : (⨆ i : I, (Z (U L)).map (singleEnveloping i)) ≤ S.map (Z (U (I → L))).val := by
    apply iSup_le
    intro i
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨singleCenter i ⟨a, ha⟩, ?_, rfl⟩
    exact le_iSup (fun i => (singleCenter (K := K) (L := L) i).range) i ⟨⟨a, ha⟩, rfl⟩
  refine top_unique (fun z _ => ?_)
  obtain ⟨w, hw, e⟩ := h (pi_center_le z.property)
  exact (Subtype.ext e : w = z) ▸ hw

end FiniteProduct

end Langlands.Algebra.ProductLieEnveloping
