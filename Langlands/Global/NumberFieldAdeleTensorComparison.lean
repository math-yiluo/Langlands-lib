import Langlands.Global.AdelicTensorBaseChange
import Langlands.Global.AdelicFunctoriality.FiniteAdeleTensorEquiv
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Full number-field tensor comparison -/

noncomputable section

universe u

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField NumberField.LiesOver

namespace Langlands.Global

open AdelicFunctoriality
open scoped AdelicFunctoriality.FiniteAdeleExtension

variable (K L : Type u) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

private def infiniteRegroup :
    ((p : InfinitePlace K) → (q : InfinitePlacesAbove L p) → q.1.Completion) ≃+
      InfiniteAdeleRing L where
  toFun a q := a (q.comap (algebraMap K L)) ⟨q, ⟨rfl⟩⟩
  invFun a _ q := a q.1
  left_inv a := by
    funext p q
    rcases q with ⟨q, hq⟩
    have := hq
    have h : q.comap (algebraMap K L) = p := InfinitePlace.LiesOver.comap_eq q p
    subst h
    rfl
  right_inv a := rfl
  map_add' _ _ := rfl

private def infiniteTensorComparison :
    L ⊗[K] InfiniteAdeleRing K ≃+ InfiniteAdeleRing L := by
  classical
  exact (TensorProduct.piRight K K L (fun p : InfinitePlace K => p.Completion)).toAddEquiv.trans
    ((AddEquiv.piCongrRight fun p : InfinitePlace K =>
      (TensorProduct.comm K L p.Completion).toAddEquiv.trans
        (infiniteTensorEquiv (L := L) p).toAddEquiv).trans (infiniteRegroup K L))

private theorem infiniteTensorComparison_tmul (a : L) (x : InfiniteAdeleRing K)
    (q : InfinitePlace L) :
    infiniteTensorComparison K L (a ⊗ₜ[K] x) q =
      algebraMap L q.Completion a *
        infiniteCompletionMap (algebraMap K L) q (x (q.comap (algebraMap K L))) := by
  have : q.LiesOver (q.comap (algebraMap K L)) := ⟨rfl⟩
  change NumberField.LiesOver.completionMap (x (q.comap (algebraMap K L))) *
    algebraMap L q.Completion a = _
  exact mul_comm _ _

private def finiteTensorComparison :
    L ⊗[K] FiniteAdeles K ≃+ FiniteAdeles L :=
  (TensorProduct.comm K L (FiniteAdeles K)).toAddEquiv.trans
    (finiteAdeleTensorEquiv K L).toAddEquiv

private def fullTensorComparison : L ⊗[K] Adeles K ≃+ Adeles L :=
  (TensorProduct.prodRight K K L (InfiniteAdeleRing K) (FiniteAdeles K)).toAddEquiv.trans
    ((infiniteTensorComparison K L).prodCongr (finiteTensorComparison K L))

private theorem fullTensorComparison_apply (z : L ⊗[K] Adeles K) :
    fullTensorComparison K L z = numberFieldAdeleTensorMap K L z := by
  induction z with
  | tmul a x =>
    apply Prod.ext
    · funext q
      exact infiniteTensorComparison_tmul K L a x.1 q
    · apply RestrictedProduct.ext
      intro q
      change finiteAdeleTensorEquiv K L (x.2 ⊗ₜ[K] a) q = _
      rw [finiteAdeleTensorEquiv_tmul_apply]
      exact mul_comm _ _
  | add z w hz hw =>
    simp only [map_add, hz, hw]

/-- The canonical full map, retaining every archimedean factor, is bijective. -/
theorem numberFieldAdeleTensorMap_bijective :
    Function.Bijective (numberFieldAdeleTensorMap K L) := by
  have h : ⇑(fullTensorComparison K L) = ⇑(numberFieldAdeleTensorMap K L) :=
    funext (fullTensorComparison_apply K L)
  rw [← h]
  exact (fullTensorComparison K L).bijective

/-- The canonical full adelic tensor map as an algebra equivalence. -/
def numberFieldAdeleTensorEquiv : L ⊗[K] Adeles K ≃ₐ[L] Adeles L :=
  AlgEquiv.ofBijective (numberFieldAdeleTensorMap K L)
    (numberFieldAdeleTensorMap_bijective K L)

/-- The equivalence has the original canonical algebra map. -/
@[simp] theorem numberFieldAdeleTensorEquiv_toAlgHom :
    (numberFieldAdeleTensorEquiv K L).toAlgHom = numberFieldAdeleTensorMap K L := rfl

/-- Pure tensors evaluate using the original full adelic inclusion. -/
@[simp] theorem numberFieldAdeleTensorEquiv_tmul (a : L) (x : Adeles K) :
    numberFieldAdeleTensorEquiv K L (a ⊗ₜ[K] x) =
      algebraMap L (Adeles L) a * adeleInclusion x := rfl

end Langlands.Global
