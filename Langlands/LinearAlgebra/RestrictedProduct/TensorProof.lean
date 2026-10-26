/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper

Modified by Worker 288 (2026): prove the published three-clause proposition
from Imperial FLT commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean:93-232.
Retain the scalar comparison and reduction of left-linear bijectivity;
replace the principal-filter/direct-limit proof by full-product injectivity
and a filter-large coordinate-submodule lifting argument, using the published
arbitrary-product comparison. Keep all four universes independent.
The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.LinearAlgebra.RestrictedProduct.TensorStatement
import Langlands.LinearAlgebra.RestrictedProduct.TensorPiProof

namespace RestrictedProduct

open TensorProduct

universe uR uM uι uN

private theorem scalar_comparison
    (R : Type uR) (M : Type uM) [CommRing R] [CommRing M] [Algebra R M]
    {ι : Type uι} (N : ι → Type uN) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)]
    (L : ∀ i, Submodule R (N i)) (ℱ : Filter ι) :
    ⇑(lTensorLeft R M N ℱ L) = lTensor R M N ℱ L := by
  ext x i
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp [lTensorLeft_tmul]; rfl
  | add x y hx hy => simp_all; rfl

private theorem restricted_bijective
    (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]
    {ι : Type uι} (N : ι → Type uN) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (L : ∀ i, Submodule R (N i)) (ℱ : Filter ι) :
    Function.Bijective (lTensor R M N ℱ L) := by
  classical
  let j : (Πʳ i, [N i, L i]_[ℱ]) →ₗ[R] ∀ i, N i :=
    { toFun := fun x i ↦ x i
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let k : (Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ]) →ₗ[R]
      ∀ i, M ⊗[R] N i :=
    { toFun := fun x i ↦ x i
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hj : Function.Injective j := fun _ _ h ↦ Subtype.ext h
  have square : k ∘ₗ lTensor R M N ℱ L =
      piRightHom R R M N ∘ₗ j.lTensor M := by
    apply TensorProduct.ext'
    intro m x
    rfl
  constructor
  · have hinj : Function.Injective (k ∘ₗ lTensor R M N ℱ L) := by
      rw [square]
      exact (tensorPiComparison_proof R M N).injective.comp
        (Module.Flat.lTensor_preserves_injective_linearMap j hj)
    intro x y h
    exact hinj (congrArg k h)
  · intro y
    let P (i : ι) : Submodule R (N i) :=
      if y i ∈ rangeLTensor R M N L i then L i else ⊤
    have hlift (i : ι) :
        ∃ z : M ⊗[R] P i, (P i).subtype.lTensor M z = y i := by
      by_cases hi : y i ∈ rangeLTensor R M N L i
      · have hP : P i = L i := by unfold P; split <;> simp_all
        rw [hP]
        exact hi
      · have htop : Function.Surjective ((⊤ : Submodule R (N i)).subtype) :=
          fun n ↦ ⟨⟨n, trivial⟩, rfl⟩
        have hP : P i = ⊤ := by unfold P; split <;> simp_all
        rw [hP]
        exact LinearMap.lTensor_surjective M htop (y i)
    choose z hz using hlift
    let e : (∀ i, P i) →ₗ[R] Πʳ i, [N i, L i]_[ℱ] :=
      { toFun := fun x ↦ ⟨fun i ↦ (x i).val, by
          filter_upwards [y.property] with i hi
          have hP : P i = L i := by
            unfold P
            split
            · rfl
            · rename_i h
              exact (h hi).elim
          exact hP.le (x i).property⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let q : (∀ i, M ⊗[R] P i) →ₗ[R] ∀ i, M ⊗[R] N i :=
      LinearMap.pi (fun i ↦ (P i).subtype.lTensor M ∘ₗ LinearMap.proj i)
    have naturality : k ∘ₗ lTensor R M N ℱ L ∘ₗ e.lTensor M =
        q ∘ₗ piRightHom R R M (fun i ↦ P i) := by
      apply TensorProduct.ext'
      intro m x
      rfl
    obtain ⟨t, ht⟩ := (tensorPiComparison_proof R M (fun i ↦ P i)).surjective z
    refine ⟨e.lTensor M t, ?_⟩
    apply RestrictedProduct.ext
    intro i
    have hn := congrFun (LinearMap.congr_fun naturality t) i
    change (lTensor R M N ℱ L (e.lTensor M t)) i =
      (P i).subtype.lTensor M (piRightHom R R M (fun i ↦ P i) t i) at hn
    rw [hn, ht]
    exact hz i

/-- Scalar comparison and bijectivity of the canonical restricted-product tensor maps. -/
theorem tensorRestrictedProductComparison_proof :
    TensorRestrictedProductComparison.{uR, uM, uι, uN} := by
  refine ⟨?_, ?_, ?_⟩
  · intro R M _ _ _ ι N _ _ L ℱ
    exact scalar_comparison R M N L ℱ
  · intro R M _ _ _ _ _ ι N _ _ L ℱ
    exact restricted_bijective R M N L ℱ
  · intro R M _ _ _ _ _ ι N _ _ L ℱ
    rw [scalar_comparison R M N L ℱ]
    exact restricted_bijective R M N L ℱ

end RestrictedProduct
