import Mathlib.RingTheory.Etale.Finite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-! # Evaluation and descent for finite étale coordinate algebras -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.EtaleExtensionSplit

variable (k L A : Type u) [Field k] [Field L] [Algebra k L]
  [CommRing A] [Algebra k A] [Algebra.Etale k A] [IsSepClosed L]

set_option backward.isDefEq.respectTransparency false

/-- The base change of a finite étale algebra to a separably closed field is
split by evaluation at its geometric points. -/
def evaluationEquiv : (L ⊗[k] A) ≃ₐ[L] ((A →ₐ[k] L) → L) :=
  let r := Algebra.TensorProduct.liftEquivRight k L A L
  let s := Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[k] A)
  (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[k] A)).trans
    (AlgEquiv.piCongrLeft L (fun _ => L) (r.trans s)).symm

private theorem evaluationEquiv_apply (t : L ⊗[k] A) (x : A →ₐ[k] L) :
    evaluationEquiv k L A t x = Algebra.TensorProduct.liftEquivRight k L A L x t := by
  let r := Algebra.TensorProduct.liftEquivRight k L A L x
  let P : PrimeSpectrum L := ⊥
  change Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[k] A) t
    (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[k] A) r) = r t
  have hP : Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[k] A) r = P.comap r := by
    ext : 1
    rfl
  rw [hP, Algebra.FormallyEtale.equivPiOfIsSepClosed_comap,
    Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply]

@[simp] theorem evaluationEquiv_tmul (l : L) (a : A) (x : A →ₐ[k] L) :
    evaluationEquiv k L A (l ⊗ₜ a) x = l * x a := by
  rw [evaluationEquiv_apply]
  simp

/-- Geometric points separate the elements of the original algebra. -/
theorem eq_of_geometric_evaluation {a b : A} (h : ∀ x : A →ₐ[k] L, x a = x b) : a = b := by
  apply (Algebra.TensorProduct.includeRight_injective (B := A) (algebraMap k L).injective)
  apply (evaluationEquiv k L A).injective
  funext x
  change evaluationEquiv k L A (1 ⊗ₜ a) x = evaluationEquiv k L A (1 ⊗ₜ b) x
  simpa using h x

private theorem exists_of_equivariant_evaluation [IsGalois k L] (f : (A →ₐ[k] L) → L)
    (hf : ∀ (σ : L ≃ₐ[k] L) x, f (σ.toAlgHom.comp x) = σ (f x)) :
    ∃ a : A, ∀ x, x a = f x := by
  classical
  let E := evaluationEquiv k L A
  let t := E.symm f
  have ht : E t = f := E.apply_symm_apply f
  let τ (σ : L ≃ₐ[k] L) := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)
  have hτ (σ : L ≃ₐ[k] L) (z : L ⊗[k] A) (x : A →ₐ[k] L) :
      E (τ σ z) x = σ (E z (σ.symm.toAlgHom.comp x)) := by
    induction z using TensorProduct.inductionOn with
    | tmul l a => simp [E, τ]
    | add z w hz hw => simp [hz, hw]
  have hfixed (σ : L ≃ₐ[k] L) : τ σ t = t := by
    apply E.injective
    funext x
    rw [hτ, ht, ← hf]
    apply congrArg f
    exact AlgHom.ext fun a => σ.apply_symm_apply (x a)
  let b := Module.Free.chooseBasis k A
  let bL := b.baseChange L
  have hrepr (σ : L ≃ₐ[k] L) (z : L ⊗[k] A) (i : Module.Free.ChooseBasisIndex k A) :
      bL.repr (τ σ z) i = σ (bL.repr z i) := by
    induction z using TensorProduct.inductionOn with
    | tmul l a => simp [τ, bL, Algebra.smul_def]
    | add z w hz hw => simp [hz, hw]
  have hc (i : Module.Free.ChooseBasisIndex k A) :
      ∃ c : k, algebraMap k L c = bL.repr t i :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (bL.repr t i)).2
      (fun σ => (hrepr σ t i).symm.trans (by rw [hfixed]))
  choose c hc using hc
  have := Algebra.FormallyUnramified.finite_of_free k A
  let a := b.repr.symm (Finsupp.equivFunOnFinite.symm c)
  have ha : (1 : L) ⊗ₜ a = t := by
    apply bL.repr.injective
    ext i
    simpa [bL, a, Algebra.smul_def] using hc i
  refine ⟨a, fun x => ?_⟩
  have h := congrFun ht x
  rw [← ha] at h
  simpa [E] using h

/-- A Galois-equivariant family of maps into the geometric coefficient field
is induced by a map into the finite étale algebra itself. -/
theorem exists_algHom_of_equivariant [IsGalois k L] {B : Type u} [CommRing B] [Algebra k B]
    (f : (A →ₐ[k] L) → (B →ₐ[k] L))
    (hf : ∀ (σ : L ≃ₐ[k] L) x, f (σ.toAlgHom.comp x) = σ.toAlgHom.comp (f x)) :
    ∃ g : B →ₐ[k] A, ∀ x, x.comp g = f x := by
  classical
  have he (b : B) : ∃ a : A, ∀ x : A →ₐ[k] L, x a = f x b :=
    exists_of_equivariant_evaluation k L A (fun x => f x b)
      (fun σ x => DFunLike.congr_fun (hf σ x) b)
  choose g hg using he
  refine ⟨{
    toFun := g
    map_one' := eq_of_geometric_evaluation k L A (fun x => by rw [hg, map_one, map_one])
    map_zero' := eq_of_geometric_evaluation k L A (fun x => by rw [hg, map_zero, map_zero])
    map_mul' := fun a b => eq_of_geometric_evaluation k L A
      (fun x => by simp only [hg, map_mul])
    map_add' := fun a b => eq_of_geometric_evaluation k L A
      (fun x => by simp only [hg, map_add])
    commutes' := fun c => eq_of_geometric_evaluation k L A
      (fun x => by rw [hg, AlgHom.commutes, AlgHom.commutes]) }, fun x => AlgHom.ext (fun b => hg b x)⟩

end Langlands.GroupScheme.EtaleExtensionSplit
