import Langlands.Global.NumberFieldAdeleTensorComparison
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicFunctoriality.NormReduction
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Langlands.Algebra.TensorNorm

/-! # The determinant tensor norm is the actual full adelic norm -/

noncomputable section

universe u

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField.LiesOver
  Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.Global

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AdelicFunctoriality

variable (K L : Type u) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- Evaluation of a full adele at an original infinite completion. -/
def adeleInfiniteEvaluation (p : InfinitePlace K) : Adeles K →ₐ[K] p.Completion where
  toFun x := x.1 p
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Evaluation of a full adele at an original finite completion. -/
def adeleFiniteEvaluation (p : HeightOneSpectrum (𝓞 K)) :
    Adeles K →ₐ[K] p.adicCompletion K where
  toFun x := x.2 p
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem infiniteTensorEvaluation (p : InfinitePlace K) (z : L ⊗[K] Adeles K)
    (q : InfinitePlacesAbove L p) :
    infiniteTensorEquiv (L := L) p
        (Algebra.TensorProduct.comm K L p.Completion
          (Algebra.TensorProduct.lTensor (S := L) L (adeleInfiniteEvaluation K p) z)) q =
      (numberFieldAdeleTensorMap K L z).1 q.1 := by
  induction z with
  | tmul a x =>
    change NumberField.LiesOver.completionMap (x.1 p) *
      algebraMap L q.1.Completion a =
      algebraMap L q.1.Completion a *
        infiniteCompletionMap (algebraMap K L) q.1 (x.1 (q.1.comap (algebraMap K L)))
    rw [infiniteCompletionMap_comap_eq p q.1 x.1, mul_comm]
  | add z w hz hw =>
    simp only [map_add, Pi.add_apply]
    change _ = (numberFieldAdeleTensorMap K L z).1 q.1 +
      (numberFieldAdeleTensorMap K L w).1 q.1
    exact congrArg₂ (· + ·) hz hw

open scoped AdelicFunctoriality.FiniteExtension in
theorem finiteTensorEvaluation (p : HeightOneSpectrum (𝓞 K)) (z : L ⊗[K] Adeles K)
    (q : FinitePlacesAbove L p) :
    finiteTensorMap (L := L) p
        (Algebra.TensorProduct.comm K L (p.adicCompletion K)
          (Algebra.TensorProduct.lTensor (S := L) L (adeleFiniteEvaluation K p) z)) q =
      (numberFieldAdeleTensorMap K L z).2 q.1 := by
  induction z with
  | tmul a x =>
    change FiniteExtension.completionMap p q.1 (x.2 p) *
      algebraMap L (q.1.adicCompletion L) a =
      algebraMap L (q.1.adicCompletion L) a *
        FiniteExtension.completionMap (q.1.under (𝓞 K)) q.1 (x.2 (q.1.under (𝓞 K)))
    rw [completionMap_under_eq p q.1 x.2, mul_comm]
  | add z w hz hw =>
    simp only [map_add, Pi.add_apply]
    change _ = (numberFieldAdeleTensorMap K L z).2 q.1 +
      (numberFieldAdeleTensorMap K L w).2 q.1
    exact congrArg₂ (· + ·) hz hw

/-- The determinant norm over the original full base-field adele ring. -/
def numberFieldAdeleTensorNorm : L ⊗[K] Adeles K →* Adeles K :=
  Langlands.Algebra.tensorNorm K L (Adeles K)

/-- Every infinite coordinate of the determinant norm is the product of the actual local norms. -/
theorem numberFieldAdeleTensorNorm_infinite (z : L ⊗[K] Adeles K)
    (p : InfinitePlace K) :
    (numberFieldAdeleTensorNorm K L z).1 p =
      ∏ q : InfinitePlacesAbove L p,
        InfiniteExtension.localNorm p q.1 ((numberFieldAdeleTensorMap K L z).1 q.1) := by
  have hn := Langlands.Algebra.tensorNorm_naturality (B := L) (adeleInfiniteEvaluation K p) z
  change Langlands.Algebra.tensorNorm K L p.Completion
    (Algebra.TensorProduct.lTensor (S := L) L (adeleInfiniteEvaluation K p) z) =
      (numberFieldAdeleTensorNorm K L z).1 p at hn
  rw [← hn]
  change Algebra.norm p.Completion
    (Algebra.TensorProduct.comm K L p.Completion
      (Algebra.TensorProduct.lTensor (S := L) L (adeleInfiniteEvaluation K p) z)) =
    ∏ q : InfinitePlacesAbove L p,
      Algebra.norm p.Completion ((numberFieldAdeleTensorMap K L z).1 q.1)
  rw [← norm_pi p.Completion (InfinitePlacesAbove L p)
    (fun q => q.1.Completion), ← Algebra.norm_eq_of_algEquiv (infiniteTensorEquiv (L := L) p)]
  apply congrArg (Algebra.norm p.Completion)
  funext q
  exact infiniteTensorEvaluation K L p z q

open scoped AdelicFunctoriality.FiniteExtension in
/-- Every finite coordinate has the same actual local-norm product formula. -/
theorem numberFieldAdeleTensorNorm_finite (z : L ⊗[K] Adeles K)
    (p : HeightOneSpectrum (𝓞 K)) :
    (numberFieldAdeleTensorNorm K L z).2 p =
      ∏ q : FinitePlacesAbove L p,
        FiniteExtension.localNorm p q.1 ((numberFieldAdeleTensorMap K L z).2 q.1) := by
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := L) p)
    ((completedTensorComparison K L).1 p)
  have hn := Langlands.Algebra.tensorNorm_naturality (B := L) (adeleFiniteEvaluation K p) z
  change Langlands.Algebra.tensorNorm K L (p.adicCompletion K)
    (Algebra.TensorProduct.lTensor (S := L) L (adeleFiniteEvaluation K p) z) =
      (numberFieldAdeleTensorNorm K L z).2 p at hn
  rw [← hn]
  change Algebra.norm (p.adicCompletion K)
    (Algebra.TensorProduct.comm K L (p.adicCompletion K)
      (Algebra.TensorProduct.lTensor (S := L) L (adeleFiniteEvaluation K p) z)) =
    ∏ q : FinitePlacesAbove L p,
      Algebra.norm (p.adicCompletion K) ((numberFieldAdeleTensorMap K L z).2 q.1)
  rw [← norm_pi (p.adicCompletion K) (FinitePlacesAbove L p)
    (fun q => q.1.adicCompletion L), ← Algebra.norm_eq_of_algEquiv e]
  apply congrArg (Algebra.norm (p.adicCompletion K))
  funext q
  exact finiteTensorEvaluation K L p z q

/-- The determinant tensor norm agrees with the original product of all local adelic norms. -/
theorem numberFieldAdeleTensorNorm_eq (z : L ⊗[K] Adeles K) :
    numberFieldAdeleTensorNorm K L z =
      adeleNorm (K := K) (L := L) (numberFieldAdeleTensorEquiv K L z) := by
  apply Prod.ext
  · funext p
    exact numberFieldAdeleTensorNorm_infinite K L z p
  · apply FiniteAdeleRing.ext
    intro p
    exact numberFieldAdeleTensorNorm_finite K L z p

/-- The identical comparison on actual tensor units and full ideles. -/
theorem numberFieldAdeleTensorNormUnits_eq (z : (L ⊗[K] Adeles K)ˣ) :
    Langlands.Algebra.tensorNormUnits K L (Adeles K) z =
      ideleNorm (K := K) (L := L)
        (Units.map (numberFieldAdeleTensorEquiv K L).toMonoidHom z) := by
  apply Units.ext
  exact numberFieldAdeleTensorNorm_eq K L z.val

end Langlands.Global
