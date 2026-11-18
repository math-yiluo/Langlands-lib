import Langlands.LinearAlgebra.OrthogonalCocycleComparison
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-! # Orthogonal cocycle comparison after scalar extension -/

noncomputable section

universe u w

open scoped TensorProduct

namespace Langlands.LinearAlgebra.OrthogonalCocycleDescent

open Algebra.TensorProduct Matrix

variable {F K L : Type u} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/-- The action on `K ⊗[F] L` that fixes `K` and acts on `L` by `σ`. -/
def tensorGaloisMap (K : Type u) [Field K] [Algebra F K] (σ : L ≃ₐ[F] L) :
    K ⊗[F] L →ₐ[K] K ⊗[F] L :=
  Algebra.TensorProduct.map (AlgHom.id K K) σ.toAlgHom

/-- On the right tensor factor the action is the original Galois action. -/
theorem tensorGaloisMap_comp_includeRight (σ : L ≃ₐ[F] L) :
    ((tensorGaloisMap K σ).restrictScalars F).comp
        (includeRight : L →ₐ[F] K ⊗[F] L) = includeRight.comp σ.toAlgHom :=
  map_restrictScalars_comp_includeRight _ _

private theorem algebraMap_tensor_injective : Function.Injective (algebraMap K (K ⊗[F] L)) :=
  includeLeft_injective (S := K) (A := K) (algebraMap F L).injective

variable [FiniteDimensional F L] [IsGalois F L]

/-- The fixed coefficients of `K ⊗[F] L` come from `K`, even when the tensor ring has zero divisors. -/
theorem exists_tensor_fixed_preimage (x : K ⊗[F] L)
    (hx : ∀ σ : L ≃ₐ[F] L, tensorGaloisMap K σ x = x) :
    ∃ y : K, algebraMap K (K ⊗[F] L) y = x := by
  classical
  let b := Module.Free.chooseBasis F K
  let e := _root_.TensorProduct.equivFinsuppOfBasisLeft (N := L) b
  have haction (σ : L ≃ₐ[F] L) (z : K ⊗[F] L) (i : Module.Free.ChooseBasisIndex F K) :
      e (tensorGaloisMap K σ z) i = σ (e z i) := by
    induction z using TensorProduct.inductionOn with
    | tmul a l =>
      simp only [tensorGaloisMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Algebra.smul_def, map_mul,
        AlgEquiv.commutes]
      rfl
    | add z z' hz hz' => simp only [map_add, Finsupp.add_apply, hz, hz']
  have hcoeff (i : Module.Free.ChooseBasisIndex F K) : ∃ y : F, algebraMap F L y = e x i := by
    apply IntermediateField.mem_bot.mp
    apply (IsGalois.mem_bot_iff_fixed _).mpr
    intro σ
    rw [← haction, hx]
  choose y hy using hcoeff
  refine ⟨(e x).sum (fun i _ => y i • b i), ?_⟩
  calc
    algebraMap K (K ⊗[F] L) ((e x).sum (fun i _ => y i • b i)) =
        (e x).sum (fun i l => b i ⊗ₜ[F] l) := by
      simp only [Finsupp.sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (y i • b i) ⊗ₜ[F] (1 : L) = b i ⊗ₜ[F] (e x) i
      rw [TensorProduct.smul_tmul, ← hy i, Algebra.smul_def, mul_one]
    _ = e.symm (e x) := (TensorProduct.equivFinsuppOfBasisLeft_symm_apply _ _).symm
    _ = x := e.symm_apply_apply x

variable {n : Type w} [Fintype n] [DecidableEq n]

/-- An invertible matrix fixed by the tensor Galois action descends to `K`. -/
theorem exists_unit_of_tensor_fixed (P : GL n (K ⊗[F] L))
    (hP : ∀ σ : L ≃ₐ[F] L, GeneralLinearGroup.map (tensorGaloisMap K σ).toRingHom P = P) :
    ∃ Q : GL n K, GeneralLinearGroup.map (algebraMap K (K ⊗[F] L)) Q = P := by
  have hcoeff (i j : n) : ∃ z : K, algebraMap K (K ⊗[F] L) z = P i j :=
    exists_tensor_fixed_preimage (P i j) (fun σ =>
      congrArg (fun M : GL n (K ⊗[F] L) => M i j) (hP σ))
  choose B hB using hcoeff
  have hmap : Matrix.map B (algebraMap K (K ⊗[F] L)) = (P : Matrix n n (K ⊗[F] L)) :=
    Matrix.ext hB
  let : Nontrivial (K ⊗[F] L) := by
    let f := algebraMap K (K ⊗[F] L)
    have hf : Function.Injective f := algebraMap_tensor_injective
    exact ⟨⟨f 0, f 1, fun h => zero_ne_one (hf h)⟩⟩
  have hdet : Matrix.det B ≠ 0 := by
    intro hz
    apply P.det_ne_zero
    rw [← hmap]
    let f := algebraMap K (K ⊗[F] L)
    exact (f.map_det B).symm.trans ((congrArg f hz).trans (map_zero f))
  exact ⟨GeneralLinearGroup.mkOfDetNeZero B hdet, Units.ext hmap⟩

omit [FiniteDimensional F L] [IsGalois F L] in
private theorem map_tensor_includeRight (σ : L ≃ₐ[F] L) (P : GL n L) :
    GeneralLinearGroup.map (tensorGaloisMap K σ).toRingHom
        (GeneralLinearGroup.map (includeRight : L →ₐ[F] K ⊗[F] L).toRingHom P) =
      GeneralLinearGroup.map (includeRight : L →ₐ[F] K ⊗[F] L).toRingHom
        (GeneralLinearGroup.map σ.toRingHom P) := by
  apply Units.ext
  ext i j
  exact DFunLike.congr_fun (tensorGaloisMap_comp_includeRight (K := K) σ) (P i j)

variable {H : Matrix n n F} {c₁ c₂ : OrthogonalCocycle (L := L) H}

/-- A matrix twist on the tensor extension gives a congruence over the extended ground field. -/
theorem gramCongruent_of_tensorCohomology (d₁ : Descent c₁) (d₂ : Descent c₂)
    (a : GL n (K ⊗[F] L))
    (ha : gramTransform a (H.map (algebraMap F (K ⊗[F] L))) =
      H.map (algebraMap F (K ⊗[F] L)))
    (hc : ∀ σ : L ≃ₐ[F] L,
      GeneralLinearGroup.map (includeRight : L →ₐ[F] K ⊗[F] L).toRingHom (c₂.toFun σ) =
        a⁻¹ * GeneralLinearGroup.map (includeRight : L →ₐ[F] K ⊗[F] L).toRingHom (c₁.toFun σ) *
          GeneralLinearGroup.map (tensorGaloisMap K σ).toRingHom a) :
    GramCongruent (d₁.gram.map (algebraMap F K)) (d₂.gram.map (algebraMap F K)) := by
  let j := (includeRight : L →ₐ[F] K ⊗[F] L).toRingHom
  change ∀ σ, GeneralLinearGroup.map j (c₂.toFun σ) =
    a⁻¹ * GeneralLinearGroup.map j (c₁.toFun σ) *
      GeneralLinearGroup.map (tensorGaloisMap K σ).toRingHom a at hc
  let B (c : OrthogonalCocycle (L := L) H) (d : Descent c) := d.gram.map (algebraMap F K)
  let P (c : OrthogonalCocycle (L := L) H) (d : Descent c) := GeneralLinearGroup.map j d.matrix
  let H' := H.map (algebraMap F (K ⊗[F] L))
  have hP (c : OrthogonalCocycle (L := L) H) (d : Descent c) (σ : L ≃ₐ[F] L) :
      GeneralLinearGroup.map (tensorGaloisMap K σ).toRingHom (P c d) =
        (GeneralLinearGroup.map j (c.toFun σ))⁻¹ * P c d := by
    dsimp only [P]
    rw [map_tensor_includeRight, d.map_matrix, map_mul, map_inv]
  have hmap (A : Matrix n n F) :
      (A.map (algebraMap F K)).map (algebraMap K (K ⊗[F] L)) = (A.map (algebraMap F L)).map j := by
    ext i j'
    exact (IsScalarTower.algebraMap_apply F K (K ⊗[F] L) (A i j')).symm.trans
      ((includeRight : L →ₐ[F] K ⊗[F] L).commutes (A i j')).symm
  have hB (c : OrthogonalCocycle (L := L) H) (d : Descent c) :
      (B c d).map (algebraMap K (K ⊗[F] L)) = gramTransform (P c d)⁻¹ H' := by
    change (d.gram.map (algebraMap F K)).map (algebraMap K (K ⊗[F] L)) = _
    rw [hmap, show d.gram.map (algebraMap F L) = gramTransform d.matrix⁻¹ (H.map (algebraMap F L))
        from d.gram_eq, gramTransform_map, map_inv]
    congr 1
    exact Matrix.ext (fun i j' => (includeRight : L →ₐ[F] K ⊗[F] L).commutes (H i j'))
  let Z := (P c₁ d₁)⁻¹ * a * P c₂ d₂
  have hfix (σ : L ≃ₐ[F] L) : GeneralLinearGroup.map (tensorGaloisMap K σ).toRingHom Z = Z := by
    dsimp only [Z]
    rw [map_mul, map_mul, map_inv, hP, hP, hc σ]
    group
  obtain ⟨Q, hQ⟩ := exists_unit_of_tensor_fixed Z hfix
  refine ⟨Q, ?_⟩
  apply Matrix.map_injective (algebraMap_tensor_injective (F := F) (K := K) (L := L))
  change (gramTransform Q (B c₂ d₂)).map (algebraMap K (K ⊗[F] L)) =
    (B c₁ d₁).map (algebraMap K (K ⊗[F] L))
  rw [gramTransform_map, hQ, hB, hB]
  dsimp only [Z]
  simp only [gramTransform_mul, gramTransform_inv_right, show gramTransform a H' = H' from ha]

end Langlands.LinearAlgebra.OrthogonalCocycleDescent
