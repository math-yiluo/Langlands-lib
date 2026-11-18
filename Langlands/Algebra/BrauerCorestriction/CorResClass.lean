import Langlands.Algebra.BrauerCorestriction.CorRes
import Langlands.Algebra.BrauerCorestriction.Hom
import Langlands.Algebra.BrauerScalarExtension

/-!
# Corestriction after restriction

For a finite separable extension `L/K`, corestriction after scalar extension is multiplication
by `[L : K]` on the actual Brauer group: `Cor_{L/K}(Res_{L/K} x) = [L : K] • x`.
-/

universe u

open TensorProduct PiTensorProduct Module Langlands.Brauer
open Langlands.PiTensorSemilinear

namespace Langlands.BrauerCorestriction

section Power

variable {K : Type u} [Field K]

/-- The tensor power `⨂_K (i : E), B` of an actual central simple algebra, over a finite
index type, as an actual central simple algebra. -/
noncomputable def piCSA (E : Type u) [Finite E] (B : CSA.{u, u} K) : CSA.{u, u} K where
  toAlgCat := AlgCat.of K (⨂[K] _ : E, (B : Type u))
  isCentral := (piTensor_isCentral_isSimpleRing K (fun _ : E => (B : Type u))).1
  isSimple := (piTensor_isCentral_isSimpleRing K (fun _ : E => (B : Type u))).2
  fin_dim := PiTensorProduct.finite

/-- Reindexing a tensor power along a bijection of index types. -/
noncomputable def piReindexAlgEquiv {α β : Type u} (e : α ≃ β) (B : Type u) [Ring B]
    [Algebra K B] : (⨂[K] _ : β, B) ≃ₐ[K] (⨂[K] _ : α, B) :=
  AlgEquiv.ofLinearEquiv (reindex K (fun _ : β => B) e.symm) (reindex_one K e.symm)
    (reindex_mul K e.symm)

/-- A tensor power over an empty index type is the ground field. -/
noncomputable def piEmptyAlgEquiv (B : Type u) [Ring B] [Algebra K B] :
    K ≃ₐ[K] (⨂[K] _ : PEmpty.{u + 1}, B) :=
  have hsurj : Function.Surjective (algebraMap K (⨂[K] _ : PEmpty.{u + 1}, B)) := by
    intro x
    refine ⟨isEmptyEquiv PEmpty x, ?_⟩
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [map_smul, isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one,
        Algebra.algebraMap_eq_smul_one, PiTensorProduct.one_def]
      congr 2
      funext i
      exact i.elim
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : Nontrivial (⨂[K] _ : PEmpty.{u + 1}, B) := (isEmptyEquiv PEmpty).toEquiv.nontrivial
  AlgEquiv.ofBijective (Algebra.ofId K _) ⟨(algebraMap K _).injective, hsurj⟩

/-- A tensor power over `Option α` splits off the extra factor. -/
noncomputable def piOptionAlgEquiv (α : Type u) (B : Type u) [Ring B] [Algebra K B] :
    (⨂[K] _ : Option α, B) ≃ₐ[K] (⨂[K] _ : α, B) ⊗[K] B :=
  let e := Equiv.optionEquivSumPUnit.{0} α
  let l : (⨂[K] _ : Option α, B) ≃ₗ[K] (⨂[K] _ : α, B) ⊗[K] B :=
    (reindex K (fun _ : Option α => B) e).trans
      ((tmulEquivDep K (fun _ : α ⊕ PUnit => B)).symm.trans
        (TensorProduct.congr (LinearEquiv.refl K _)
          (subsingletonEquiv (R := K) (s := fun _ : PUnit => B) PUnit.unit)))
  have hl : ∀ f : Option α → B, l (tprod K f) = tprod K (fun i => f (some i)) ⊗ₜ f none := by
    intro f
    simp only [l, LinearEquiv.trans_apply, reindex_tprod, tmulEquivDep_symm_apply]
    exact congrArg (TensorProduct.tmul K _)
      (subsingletonEquiv_apply_tprod (R := K) (s := fun _ : PUnit => B) PUnit.unit _)
  let φ : MultilinearMap K (fun _ : Option α => B) ((⨂[K] _ : α, B) ⊗[K] B) :=
    l.toLinearMap.compMultilinearMap (tprod K)
  have hφ : ∀ f, φ f = tprod K (fun i => f (some i)) ⊗ₜ f none := fun f => hl f
  let F := liftAlgHom φ
    (by rw [hφ]; rfl)
    (fun x y => by
      rw [hφ, hφ, hφ, Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod]
      rfl)
  have hF : F.toLinearMap = l.toLinearMap := by
    refine PiTensorProduct.ext ?_
    ext f
    simp [F, φ]
  have hbij : Function.Bijective F := by
    have : (F : (⨂[K] _ : Option α, B) → _) = l := congrArg DFunLike.coe hF
    rw [this]
    exact l.bijective
  AlgEquiv.ofBijective F hbij

/-- The class of a tensor power is the multiple of the class. -/
theorem classOf_piCSA (E : Type u) [Finite E] (B : CSA.{u, u} K) :
    classOf (piCSA E B) = Nat.card E • classOf B := by
  have key : ∀ (α : Type u) [Finite α], classOf (piCSA α B) = Nat.card α • classOf B := by
    intro α _
    refine Finite.induction_empty_option
      (P := fun α => ∀ (_ : Finite α), classOf (piCSA α B) = Nat.card α • classOf B)
      ?_ ?_ ?_ α inferInstance
    · intro α β e h _
      have : Finite α := Finite.of_equiv β e.symm
      rw [← Nat.card_congr e, ← h this]
      exact classOf_eq_of_algEquiv (piReindexAlgEquiv e (B : Type u))
    · intro _
      rw [Nat.card_of_isEmpty, zero_smul, ← classOf_groundField]
      exact classOf_eq_of_algEquiv (piEmptyAlgEquiv (B : Type u)).symm
    · intro α _ h _
      rw [Finite.card_option, succ_nsmul, ← h inferInstance, ← classOf_tensor]
      exact classOf_eq_of_algEquiv (piOptionAlgEquiv α (B : Type u))
  exact key E

end Power

section CorRes

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- The corestriction of the scalar extension of `B` has the class of the `[L : K]`-th
tensor power of `B`. -/
theorem classOf_corCSA_baseChange (B : CSA.{u, u} K) :
    classOf (corCSA K L (baseChange L B)) = finrank K L • classOf B := by
  classical
  let N := canonicalClosure K L
  let E := L →ₐ[K] N
  let _ : Fintype E := Fintype.ofFinite E
  let e₀ : (baseChange L B : Type u) ≃ₐ[L] (L ⊗[K] (B : Type u)) := AlgEquiv.refl
  let eS : (corCSA K L (baseChange L B) : Type u) ≃ₐ[K] corAlg K L N (baseChange L B) :=
    AlgEquiv.refl
  let e₁ : corAlg K L N (baseChange L B) ≃ₐ[K] corAlg K L N (L ⊗[K] (B : Type u)) :=
    corEquiv K L N e₀
  let eC : ((piCSA E B : Type u))ᵐᵒᵖ ≃ₐ[K] (⨂[K] _ : E, (B : Type u))ᵐᵒᵖ := AlgEquiv.refl
  let eT : (tensor (corCSA K L (baseChange L B)) (opposite (piCSA E B)) : Type u) ≃ₐ[K]
      (corCSA K L (baseChange L B) : Type u) ⊗[K] ((piCSA E B : Type u))ᵐᵒᵖ := AlgEquiv.refl
  let e := eT.trans ((Algebra.TensorProduct.congr (eS.trans e₁) eC).trans
    (corResSplitEquiv K L N (B : Type u)))
  have hsplit :
      classOf (tensor (corCSA K L (baseChange L B)) (opposite (piCSA E B))) = 0 := by
    rw [← classOf_groundField, classOf_eq_iff]
    exact ⟨1, finrank K (twistFixed K L N (B : Type u)), one_ne_zero,
      (finrank_twistFixed_pos K L N (B : Type u)).ne', ⟨(matrixFinOneAlgEquiv K _).trans e⟩⟩
  rw [classOf_tensor, classOf_opposite, add_neg_eq_zero] at hsplit
  rw [hsplit, classOf_piCSA, natCard_algHom_canonicalClosure]

/-- **Corestriction after restriction**: `Cor_{L/K} (Res_{L/K} x) = [L : K] • x` on the actual
Brauer group, where restriction is Task 7532's actual scalar-extension homomorphism. -/
theorem corHom_scalarExtension (x : BrauerGroup.{u, u} K) :
    corHom K L (scalarExtension L x) = finrank K L • x := by
  induction x using Quotient.inductionOn with
  | _ B => exact classOf_corCSA_baseChange K L B

/-- The same identity as an equality of additive homomorphisms. -/
theorem corHom_comp_scalarExtension :
    (corHom K L).comp (scalarExtension L) = finrank K L • AddMonoidHom.id (BrauerGroup.{u, u} K) :=
  AddMonoidHom.ext fun x => by
    rw [AddMonoidHom.comp_apply, corHom_scalarExtension, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply]

end CorRes

end Langlands.BrauerCorestriction
