import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Splitting a pair of maps of finite free modules that is jointly injective over a field

If two linear maps out of a finite free module are jointly injective after extending scalars
along a ring map `φ : A →+* k` to a field, then they have a left inverse up to one scalar
`a` with `φ a ≠ 0`.
-/

universe u

open CategoryTheory Matrix

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.FibreH0Spread

/-- A matrix over a field whose `mulVec` is injective has a square row-submatrix with nonzero
determinant. -/
theorem exists_row_minor_of_mulVec_injective {k : Type*} [Field k] {m ι : Type*}
    [Fintype m] [Fintype ι] [DecidableEq ι] (A : Matrix m ι k)
    (hA : Function.Injective A.mulVec) :
    ∃ e : ι → m, (A.submatrix e id).det ≠ 0 := by
  classical
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hA]
    simp
  have hspan : Submodule.span k (Set.range A.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [← A.rank_eq_finrank_span_row, hrank]
      simp)
  have htop : ⊤ ≤ Submodule.span k (Set.range A.row) := hspan.ge
  let b := Module.Basis.ofSpan htop
  let c := b.reindex (b.indexEquiv (Pi.basisFun k ι))
  have hc (i : ι) : ∃ j : m, A.row j = c i := by
    apply Module.Basis.ofSpan_subset htop
    exact ⟨(b.indexEquiv (Pi.basisFun k ι)).symm i, (b.reindex_apply _ i).symm⟩
  choose e he using hc
  refine ⟨e, ?_⟩
  have hrows : (A.submatrix e id).row = c := by
    funext i
    exact he i
  have hunit : IsUnit (A.submatrix e id) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp (by
      rw [hrows]
      exact c.linearIndependent)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- A matrix whose image in a field is injective has a left inverse up to the scalar given by a
minor that is nonzero in the field. -/
theorem exists_mul_eq_smul_one {A k : Type*} [CommRing A] [Field k] (φ : A →+* k)
    {m ι : Type*} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]
    (F : Matrix ι m A) (hF : Function.Injective (F.map φ).mulVec) :
    ∃ a : A, φ a ≠ 0 ∧ ∃ G : Matrix m ι A, G * F = a • 1 := by
  obtain ⟨e, he⟩ := exists_row_minor_of_mulVec_injective (F.map φ) hF
  let D := F.submatrix e id
  refine ⟨D.det, ?_, D.adjugate * (1 : Matrix ι ι A).submatrix e (Equiv.refl ι), ?_⟩
  · rw [RingHom.map_det]
    exact he
  · rw [Matrix.mul_assoc, Matrix.one_submatrix_mul]
    exact Matrix.adjugate_mul D

/-- Two linear maps out of a finite free module, jointly injective after extension of scalars to
a field, have a common left inverse up to a scalar that is nonzero in the field. -/
theorem exists_split_of_baseChange {A k : Type*} [CommRing A] [Nontrivial A] [Field k]
    [Algebra A k] {M N₁ N₂ : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N₁]
    [Module A N₁] [AddCommGroup N₂] [Module A N₂] [Module.Finite A M] [Module.Free A M]
    [Module.Finite A N₁] [Module.Free A N₁] [Module.Finite A N₂] [Module.Free A N₂]
    (f₁ : M →ₗ[A] N₁) (f₂ : M →ₗ[A] N₂)
    (h : ∀ x : TensorProduct A k M, f₁.baseChange k x = 0 → f₂.baseChange k x = 0 → x = 0) :
    ∃ a : A, algebraMap A k a ≠ 0 ∧ ∃ (g₁ : N₁ →ₗ[A] M) (g₂ : N₂ →ₗ[A] M),
      g₁ ∘ₗ f₁ + g₂ ∘ₗ f₂ = a • LinearMap.id := by
  classical
  let bM := Module.finBasis A M
  let b₁ := Module.finBasis A N₁
  let b₂ := Module.finBasis A N₂
  let F₁ := LinearMap.toMatrix bM b₁ f₁
  let F₂ := LinearMap.toMatrix bM b₂ f₂
  let F := Matrix.fromRows F₁ F₂
  have hF : Function.Injective (F.map (algebraMap A k)).mulVec := by
    have : Function.Injective (F.map (algebraMap A k)).mulVecLin := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hv' : (F.map (algebraMap A k)) *ᵥ v = 0 := hv
      let bk := Algebra.TensorProduct.basis k bM
      let x : TensorProduct A k M := bk.equivFun.symm v
      have hx : ⇑(bk.repr x) = v := bk.equivFun.apply_symm_apply v
      have hFmap : F.map (algebraMap A k) =
          Matrix.fromRows (F₁.map (algebraMap A k)) (F₂.map (algebraMap A k)) := by
        ext i j
        cases i <;> rfl
      rw [hFmap, Matrix.fromRows_mulVec] at hv'
      have hv₁ : (F₁.map (algebraMap A k)) *ᵥ v = 0 := by
        funext i
        exact congrFun hv' (Sum.inl i)
      have hv₂ : (F₂.map (algebraMap A k)) *ᵥ v = 0 := by
        funext i
        exact congrFun hv' (Sum.inr i)
      have h₁ : f₁.baseChange k x = 0 := by
        apply (Algebra.TensorProduct.basis k b₁).repr.injective
        rw [map_zero]
        ext i
        rw [← LinearMap.toMatrix_mulVec_repr bk, LinearMap.toMatrix_baseChange, hx]
        exact congrFun hv₁ i
      have h₂ : f₂.baseChange k x = 0 := by
        apply (Algebra.TensorProduct.basis k b₂).repr.injective
        rw [map_zero]
        ext i
        rw [← LinearMap.toMatrix_mulVec_repr bk, LinearMap.toMatrix_baseChange, hx]
        exact congrFun hv₂ i
      have hx0 := h x h₁ h₂
      rw [← hx, hx0, map_zero]
      rfl
    exact this
  obtain ⟨a, ha, G, hG⟩ := exists_mul_eq_smul_one (algebraMap A k) F hF
  refine ⟨a, ha, Matrix.toLin b₁ bM G.toCols₁, Matrix.toLin b₂ bM G.toCols₂, ?_⟩
  have hGF : G.toCols₁ * F₁ + G.toCols₂ * F₂ = a • 1 := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromCols_toCols]
    exact hG
  apply (LinearMap.toMatrix bM bM).injective
  rw [map_add, LinearMap.toMatrix_comp bM b₁ bM, LinearMap.toMatrix_comp bM b₂ bM,
    LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin, map_smul, LinearMap.toMatrix_id]
  exact hGF

/-- The categorical form of `exists_split_of_baseChange`, phrased with `ModuleCat.extendScalars`
along a ring map `φ : A →+* k` to a field. -/
theorem exists_split_of_extendScalars {A k : Type u} [CommRing A] [Field k] (φ : A →+* k)
    {M N₁ N₂ : ModuleCat.{u} A} [Module.Finite A M] [Module.Free A M]
    [Module.Finite A N₁] [Module.Free A N₁] [Module.Finite A N₂] [Module.Free A N₂]
    (f₁ : M ⟶ N₁) (f₂ : M ⟶ N₂)
    (h : ∀ x : (ModuleCat.extendScalars φ).obj M,
      ((ModuleCat.extendScalars φ).map f₁).hom x = 0 →
      ((ModuleCat.extendScalars φ).map f₂).hom x = 0 → x = 0) :
    ∃ a : A, φ a ≠ 0 ∧ ∃ (g₁ : N₁ ⟶ M) (g₂ : N₂ ⟶ M), f₁ ≫ g₁ + f₂ ≫ g₂ = a • 𝟙 M := by
  have := φ.domain_nontrivial
  let := φ.toAlgebra
  obtain ⟨a, ha, g₁, g₂, hg⟩ := exists_split_of_baseChange (k := k) f₁.hom f₂.hom h
  refine ⟨a, ha, ModuleCat.ofHom g₁, ModuleCat.ofHom g₂, ?_⟩
  ext1
  exact hg

end Langlands.Cohomology.ModuleComplex.FibreH0Spread
