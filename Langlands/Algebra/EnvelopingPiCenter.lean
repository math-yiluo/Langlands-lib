import Langlands.Algebra.EnvelopingCenterQuotients
import Mathlib.LinearAlgebra.Pi

/-! # Enveloping centers of finite products of associative algebras -/

noncomputable section

universe u v w

open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.LieEnvelopingEquiv

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]

local notation "U" => UniversalEnvelopingAlgebra K

private abbrev envelopingCenter (L : Type v) [LieRing L] [LieAlgebra K L] :=
  Subalgebra.center K (U L)

local notation "Z" => envelopingCenter K

/-- Put a Lie element in one coordinate of the product. -/
def coordinateLieInclusion {ι : Type w} [DecidableEq ι] (i : ι) : A →ₗ⁅K⁆ (ι → A) :=
  { LinearMap.single K (fun _ : ι => A) i with
    map_lie' := fun {X Y} => by
      funext j
      change (Pi.single i ⁅X, Y⁆ : ι → A) j =
        ⁅(Pi.single i X : ι → A) j, (Pi.single i Y : ι → A) j⁆
      by_cases h : j = i
      · subst j
        simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_of_ne h, lie_zero] }

@[simp]
theorem coordinateLieInclusion_apply {ι : Type w} [DecidableEq ι] (i : ι) (X : A) :
    coordinateLieInclusion K A i X = Pi.single i X := rfl

/-- Include a coordinate center in the enveloping center of the product. -/
def coordinateCenterInclusion {ι : Type w} [DecidableEq ι] (i : ι) :
    Subalgebra.center K (U A) →ₐ[K] Subalgebra.center K (U (ι → A)) :=
  centerMapOfComplement (coordinateLieInclusion K A i) (fun X => X i) (by
    intro X Y
    funext j
    change ⁅X j - (Pi.single i (X i) : ι → A) j, (Pi.single i Y : ι → A) j⁆ = 0
    by_cases h : j = i
    · subst j
      simp only [Pi.single_eq_same, sub_self, zero_lie]
    · simp only [Pi.single_eq_of_ne h, lie_zero])

@[simp]
theorem coordinateCenterInclusion_val {ι : Type w} [DecidableEq ι] (i : ι)
    (z : Subalgebra.center K (U A)) :
    (coordinateCenterInclusion K A i z).val = map (coordinateLieInclusion K A i) z.val :=
  rfl

private def finHeadTailLieEquiv (p : ℕ) : (Fin (p + 1) → A) ≃ₗ⁅K⁆ (A × (Fin p → A)) where
  toFun X := (X 0, Fin.tail X)
  invFun X := Fin.cons X.1 X.2
  left_inv X := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp [Fin.tail]
  right_inv X := by
    apply Prod.ext
    · change Fin.cons (α := fun _ : Fin (p + 1) => A) X.1 X.2 0 = X.1
      exact Fin.cons_zero _ _
    · funext i
      change Fin.cons (α := fun _ : Fin (p + 1) => A) X.1 X.2 i.succ = X.2 i
      exact Fin.cons_succ _ _ _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

private def centerTensorEquiv (p : ℕ) :
    (Z A ⊗[K] Z (Fin p → A)) ≃ₐ[K] Z (Fin (p + 1) → A) :=
  (envelopingProductCenter K A (Fin p → A)).symm.trans
    (center (enveloping (finHeadTailLieEquiv K A p).symm))

private theorem centerTensorEquiv_left (p : ℕ) (z : Z A) :
    centerTensorEquiv K A p (z ⊗ₜ[K] (1 : Z (Fin p → A))) =
      coordinateCenterInclusion K A (0 : Fin (p + 1)) z := by
  apply Subtype.ext
  change enveloping (finHeadTailLieEquiv K A p).symm
    ((envelopingProductCenter K A (Fin p → A)).symm (z ⊗ₜ[K] 1)).val = _
  rw [envelopingProductCenter_symm_left_val, coordinateCenterInclusion_val]
  change ((map (finHeadTailLieEquiv K A p).symm.toLieHom).comp
    (map (LieHom.inl K A (Fin p → A)))) z.val = _
  rw [map_comp]
  have h : (finHeadTailLieEquiv K A p).symm.toLieHom.comp (LieHom.inl K A (Fin p → A)) =
      coordinateLieInclusion K A (0 : Fin (p + 1)) := by
    apply LieHom.ext
    intro X
    funext j
    change Fin.cons (α := fun _ : Fin (p + 1) => A) X (0 : Fin p → A) j =
      (Pi.single 0 X : Fin (p + 1) → A) j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero, Pi.single_eq_same]
    · simp only [Fin.cons_succ, Pi.zero_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero j)]
  rw [h]

private theorem centerTensorEquiv_right_coordinate (p : ℕ) (i : Fin p) (z : Z A) :
    centerTensorEquiv K A p ((1 : Z A) ⊗ₜ[K] coordinateCenterInclusion K A i z) =
      coordinateCenterInclusion K A i.succ z := by
  apply Subtype.ext
  change enveloping (finHeadTailLieEquiv K A p).symm
    ((envelopingProductCenter K A (Fin p → A)).symm
      (1 ⊗ₜ[K] coordinateCenterInclusion K A i z)).val = _
  rw [envelopingProductCenter_symm_right_val, coordinateCenterInclusion_val,
    coordinateCenterInclusion_val]
  change ((map (finHeadTailLieEquiv K A p).symm.toLieHom).comp
    ((map (LieHom.inr K A (Fin p → A))).comp (map (coordinateLieInclusion K A i)))) z.val = _
  rw [map_comp (LieHom.inr K A (Fin p → A)), map_comp]
  have h : (finHeadTailLieEquiv K A p).symm.toLieHom.comp
      ((LieHom.inr K A (Fin p → A)).comp (coordinateLieInclusion K A i)) =
      coordinateLieInclusion K A i.succ := by
    apply LieHom.ext
    intro X
    funext j
    change Fin.cons (α := fun _ : Fin (p + 1) => A) 0 (Pi.single i X : Fin p → A) j =
      (Pi.single i.succ X : Fin (p + 1) → A) j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
    · by_cases h : j = i
      · subst j
        simp only [Fin.cons_succ, Pi.single_eq_same]
      · simp only [Fin.cons_succ, Pi.single_eq_of_ne h,
          Pi.single_eq_of_ne (fun he => h (Fin.succ_injective _ he))]
  rw [h]

private def envelopingSubsingleton (L : Type v) [LieRing L] [LieAlgebra K L] [Subsingleton L] :
    U L ≃ₐ[K] K := by
  let f := UniversalEnvelopingAlgebra.lift K (0 : L →ₗ⁅K⁆ K)
  let g := Algebra.ofId K (U L)
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AlgHom.ext
    intro c
    exact f.commutes c
  · apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro X
    rw [Subsingleton.elim X 0]
    simp only [map_zero]

/-- A quotient of the center of an enveloping algebra of finitely many copies of an associative
algebra is finite-dimensional if its contractions to all coordinate centers are cofinite. -/
theorem quotientFinite_center_pi (p : ℕ)
    (I : Ideal (Z (Fin p → A)))
    (h : ∀ i : Fin p, Module.Finite K ((Z A) ⧸
      I.comap (coordinateCenterInclusion K A i).toRingHom)) :
    Module.Finite K ((Z (Fin p → A)) ⧸ I) := by
  induction p with
  | zero =>
    let f := (envelopingSubsingleton K (Fin 0 → A)).toLinearEquiv.toLinearMap
    have : Module.Finite K (Z (Fin 0 → A)) :=
      Module.Finite.of_injective (f.comp (Subalgebra.center K (U (Fin 0 → A))).val.toLinearMap)
        ((envelopingSubsingleton K (Fin 0 → A)).injective.comp Subtype.val_injective)
    exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I).toLinearMap
      Ideal.Quotient.mk_surjective
  | succ p ih =>
    let E := centerTensorEquiv K A p
    let l : Z A →ₐ[K] Z A ⊗[K] Z (Fin p → A) := Algebra.TensorProduct.includeLeft
    let r : Z (Fin p → A) →ₐ[K] Z A ⊗[K] Z (Fin p → A) := Algebra.TensorProduct.includeRight
    let J := I.comap E.toAlgHom.toRingHom
    have hl : E.toAlgHom.comp l = coordinateCenterInclusion K A (0 : Fin (p + 1)) :=
      AlgHom.ext (centerTensorEquiv_left K A p)
    have hr (i : Fin p) : (E.toAlgHom.comp r).comp (coordinateCenterInclusion K A i) =
        coordinateCenterInclusion K A i.succ :=
      AlgHom.ext (centerTensorEquiv_right_coordinate K A p i)
    have h₁ : Module.Finite K ((Z A) ⧸ J.comap l.toRingHom) := by
      change Module.Finite K ((Z A) ⧸ (I.comap E.toAlgHom.toRingHom).comap l.toRingHom)
      rw [Ideal.comap_comap l.toRingHom E.toAlgHom.toRingHom]
      change Module.Finite K ((Z A) ⧸ I.comap (E.toAlgHom.comp l).toRingHom)
      rw [hl]
      exact h 0
    have h₂ : Module.Finite K ((Z (Fin p → A)) ⧸ J.comap r.toRingHom) := by
      refine ih (J.comap r.toRingHom) fun i => ?_
      change Module.Finite K ((Z A) ⧸
        ((I.comap E.toAlgHom.toRingHom).comap r.toRingHom).comap
          (coordinateCenterInclusion K A i).toRingHom)
      rw [Ideal.comap_comap r.toRingHom E.toAlgHom.toRingHom]
      change Module.Finite K ((Z A) ⧸
        (I.comap (E.toAlgHom.comp r).toRingHom).comap
          (coordinateCenterInclusion K A i).toRingHom)
      rw [Ideal.comap_comap (coordinateCenterInclusion K A i).toRingHom
        (E.toAlgHom.comp r).toRingHom]
      change Module.Finite K ((Z A) ⧸
        I.comap ((E.toAlgHom.comp r).comp (coordinateCenterInclusion K A i)).toRingHom)
      rw [hr i]
      exact h i.succ
    have : Module.Finite K ((Z A ⊗[K] Z (Fin p → A)) ⧸ J) :=
      quotientFinite_tensorProduct J h₁ h₂
    exact Module.Finite.of_surjective (Ideal.quotientMapₐ I E.toAlgHom (I := J) le_rfl).toLinearMap
      (Ideal.quotientMap_surjective (H := le_rfl) E.surjective)

end Langlands.Algebra.LieEnvelopingEquiv
