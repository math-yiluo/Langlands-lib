import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Matrix coefficients of finite-dimensional subcomodules of a coalgebra over a field -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.AffineLinearEmbedding

variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Module K B] [Coalgebra K B]

/-- The right translation operator of a functional: `b ↦ ∑ f (b₂) • b₁` for
`comul b = ∑ b₁ ⊗ b₂`. -/
def rightAct (f : Module.Dual K B) : B →ₗ[K] B :=
  TensorProduct.rid K B ∘ₗ f.lTensor B ∘ₗ comul

/-- The left translation operator of a functional: `b ↦ ∑ φ (b₁) • b₂` for
`comul b = ∑ b₁ ⊗ b₂`. -/
def leftAct (φ : Module.Dual K B) : B →ₗ[K] B :=
  TensorProduct.lid K B ∘ₗ φ.rTensor B ∘ₗ comul

theorem rightAct_apply (f : Module.Dual K B) (b : B) :
    rightAct f b = TensorProduct.rid K B (f.lTensor B (comul b)) := rfl

theorem leftAct_apply (φ : Module.Dual K B) (b : B) :
    leftAct φ b = TensorProduct.lid K B (φ.rTensor B (comul b)) := rfl

/-- Both sides are `∑ φ (b₁) * g (b₂)`. -/
theorem apply_leftAct (g φ : Module.Dual K B) (b : B) :
    g (leftAct φ b) = φ (rightAct g b) := by
  rw [leftAct_apply, rightAct_apply]
  generalize (comul (R := K) b : B ⊗[K] B) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem rightAct_counit (b : B) : rightAct (counit (R := K)) b = b := by
  simp [rightAct_apply]

@[simp] theorem leftAct_counit (b : B) : leftAct (counit (R := K)) b = b := by
  simp [leftAct_apply]

/-- Coassociativity: right translations compose. -/
theorem rightAct_rightAct (g f : Module.Dual K B) (a : B) :
    rightAct g (rightAct f a) = rightAct (g ∘ₗ rightAct f) a := by
  have h1 : rightAct g ∘ₗ ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B) =
      ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B) ∘ₗ (rightAct g).rTensor B := by
    ext x y
    simp
  have h3 : ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B) ∘ₗ
        (((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B).rTensor B) ∘ₗ
          (TensorProduct.assoc K B B B).symm.toLinearMap =
      (TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B ∘ₗ
        ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B).lTensor B := by
    apply TensorProduct.ext_threefold'
    intro x y z
    simp [smul_comm (f z) (g y) x]
  calc rightAct g (rightAct f a)
      = (rightAct g ∘ₗ ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B)) (comul a) := rfl
    _ = ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B)
          ((((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B).rTensor B)
            ((comul (R := K)).rTensor B (comul a))) := by
        rw [h1]
        simp only [rightAct, LinearMap.rTensor_comp, LinearMap.comp_apply, LinearEquiv.coe_coe]
    _ = ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B)
          ((((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B).rTensor B)
            ((TensorProduct.assoc K B B B).symm ((comul (R := K)).lTensor B (comul a)))) := by
        rw [coassoc_symm_apply]
    _ = TensorProduct.rid K B (g.lTensor B
          (((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B).lTensor B
            ((comul (R := K)).lTensor B (comul a)))) :=
        LinearMap.congr_fun h3 _
    _ = rightAct (g ∘ₗ rightAct f) a := by
        simp only [rightAct, LinearMap.lTensor_comp, LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- Coassociativity: left and right translations commute. -/
theorem rightAct_leftAct (g φ : Module.Dual K B) (a : B) :
    rightAct g (leftAct φ a) = leftAct φ (rightAct g a) := by
  have h1 : rightAct g ∘ₗ ((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B) =
      ((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B) ∘ₗ (rightAct g).lTensor B := by
    ext x y
    simp
  have h2 : leftAct φ ∘ₗ ((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B) =
      ((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B) ∘ₗ (leftAct φ).rTensor B := by
    ext x y
    simp
  have h3 : ((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B) ∘ₗ
        ((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B).lTensor B =
      ((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B) ∘ₗ
        (((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B).rTensor B) ∘ₗ
          (TensorProduct.assoc K B B B).symm.toLinearMap := by
    apply TensorProduct.ext_threefold'
    intro x y z
    simp
  calc rightAct g (leftAct φ a)
      = (rightAct g ∘ₗ ((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B)) (comul a) := rfl
    _ = ((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B)
          (((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B).lTensor B
            ((comul (R := K)).lTensor B (comul a))) := by
        rw [h1]
        simp only [rightAct, LinearMap.lTensor_comp, LinearMap.comp_apply, LinearEquiv.coe_coe]
    _ = ((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B)
          ((((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B).rTensor B)
            ((TensorProduct.assoc K B B B).symm ((comul (R := K)).lTensor B (comul a)))) :=
        LinearMap.congr_fun h3 _
    _ = ((TensorProduct.rid K B).toLinearMap ∘ₗ g.lTensor B)
          ((((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B).rTensor B)
            ((comul (R := K)).rTensor B (comul a))) := by
        rw [coassoc_symm_apply]
    _ = leftAct φ (rightAct g a) := by
        rw [← LinearMap.rTensor_comp_apply]
        exact (LinearMap.congr_fun h2 (comul a)).symm

omit [Coalgebra K B] in
/-- Tensors in `B ⊗ B` are separated by contracting the second factor with functionals. -/
theorem tensor_ext {t t' : B ⊗[K] B}
    (h : ∀ g : Module.Dual K B,
      TensorProduct.rid K B (g.lTensor B t) = TensorProduct.rid K B (g.lTensor B t')) :
    t = t' := by
  classical
  let b := Basis.ofVectorSpace K B
  have key : ∀ (u : B ⊗[K] B) (i : Basis.ofVectorSpaceIndex K B),
      TensorProduct.equivFinsuppOfBasisRight b u i =
        TensorProduct.rid K B ((b.coord i).lTensor B u) := by
    intro u i
    induction u using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, key, h]

/-- All right translates of a fixed element lie in a finitely generated subspace. -/
theorem exists_fg_rightAct (a : B) :
    ∃ U : Submodule K B, U.FG ∧ ∀ f : Module.Dual K B, rightAct f a ∈ U := by
  classical
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset (R := K) (comul (R := K) a)
  refine ⟨Submodule.span K ((T.image Prod.fst : Finset B) : Set B),
    Submodule.fg_span (Finset.finite_toSet _), fun f => ?_⟩
  rw [rightAct_apply, hT, map_sum, map_sum]
  refine Submodule.sum_mem _ fun x hx => ?_
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr
    (Finset.mem_image_of_mem _ hx)))

/-- Milne, Proposition 4.7 and Theorem 4.9, for the regular comodule: every finite subset of a
coalgebra over a field lies in the span of the entries of a square matrix `M` with
`comul (M i j) = ∑ l, M i l ⊗ M l j` and `counit (M i j) = δ i j`. -/
theorem exists_matrix_coefficients (S : Finset B) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) B),
      (∀ i j, comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j) ∧
      (∀ i j, counit (R := K) (M i j) = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      (S : Set B) ⊆ Submodule.span K (Set.range fun p : Fin N × Fin N => M p.1 p.2) := by
  classical
  -- The finite-dimensional right-translation-stable subspace generated by `S`.
  let W : Submodule K B :=
    Submodule.span K (Set.range fun p : S × Module.Dual K B => rightAct p.2 (p.1 : B))
  choose U hUfg hU using exists_fg_rightAct (K := K) (B := B)
  have hWle : W ≤ S.sup U := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨a, f⟩, rfl⟩
    exact Finset.le_sup (f := U) a.2 (hU a f)
  have : FiniteDimensional K ↥(S.sup U) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_finset_sup S U fun a _ => hUfg a)
  have : FiniteDimensional K W := Submodule.finiteDimensional_of_le hWle
  have hSW : ∀ a ∈ S, a ∈ W := fun a ha => by
    have := Submodule.subset_span (R := K)
      (Set.mem_range_self (f := fun p : S × Module.Dual K B => rightAct p.2 (p.1 : B))
        (⟨a, ha⟩, counit))
    simpa using this
  have hWstable : ∀ (g : Module.Dual K B) (w : B), w ∈ W → rightAct g w ∈ W := by
    intro g w hw
    have hle : W ≤ W.comap (rightAct g) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨a, f⟩, rfl⟩
      exact Submodule.subset_span ⟨⟨a, g ∘ₗ rightAct f⟩, (rightAct_rightAct g f a).symm⟩
    exact hle hw
  -- A basis of `W` and coordinate functionals extended to `B`.
  let N := Module.finrank K W
  let e : Basis (Fin N) K W := Module.finBasis K W
  obtain ⟨P, hP⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  let φ : Fin N → Module.Dual K B := fun i => e.coord i ∘ₗ P
  have hPW : ∀ (w : B) (hw : w ∈ W), P w = ⟨w, hw⟩ := fun w hw =>
    LinearMap.congr_fun hP ⟨w, hw⟩
  have hexpand : ∀ w ∈ W, ∑ i, φ i w • (e i : B) = w := by
    intro w hw
    have h := congrArg Subtype.val (e.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simpa [φ, hPW w hw] using h
  have hφe : ∀ i j, φ i (e j) = (1 : Matrix (Fin N) (Fin N) K) i j := by
    intro i j
    simp only [φ, LinearMap.comp_apply, hPW _ (e j).2, Subtype.coe_eta, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  let M : Matrix (Fin N) (Fin N) B := Matrix.of fun i j => leftAct (φ i) (e j : B)
  have hM : ∀ i j, M i j = leftAct (φ i) (e j : B) := fun _ _ => rfl
  have hrightM : ∀ (g : Module.Dual K B) (j : Fin N),
      rightAct g (e j : B) = ∑ i, g (M i j) • (e i : B) := by
    intro g j
    simp only [hM, apply_leftAct]
    exact (hexpand _ (hWstable g _ (e j).2)).symm
  have hcomul_e : ∀ j, comul (R := K) (e j : B) = ∑ i, (e i : B) ⊗ₜ[K] M i j := by
    intro j
    apply tensor_ext
    intro g
    rw [← rightAct_apply, hrightM, map_sum, map_sum]
    simp
  refine ⟨N, M, ?_, ?_, ?_⟩
  · intro i j
    apply tensor_ext
    intro g
    rw [← rightAct_apply, hM, rightAct_leftAct, ← hexpand _ (hWstable g _ (e j).2), map_sum,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← apply_leftAct, ← hM]
    simp [hM]
  · intro i j
    rw [hM, ← LinearMap.comp_apply (counit (R := K)) (leftAct (φ i)), LinearMap.comp_apply,
      apply_leftAct, rightAct_counit, hφe]
  · intro a ha
    have hspan : ∀ j, (e j : B) ∈
        Submodule.span K (Set.range fun p : Fin N × Fin N => M p.1 p.2) := by
      intro j
      rw [← leftAct_counit (K := K) (e j : B), leftAct_apply, hcomul_e, map_sum, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    rw [← hexpand a (hSW a ha)]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hspan i)

end Langlands.GroupScheme.AffineLinearEmbedding
