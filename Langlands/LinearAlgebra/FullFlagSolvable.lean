import Langlands.Group.GL.UpperTriangularSolvable
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

open Matrix

namespace Langlands.LinearAlgebra

private theorem independent_of_fullFlag_steps {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {n : ℕ}
    (F : Fin (n + 1) → Submodule K V) (hF : Monotone F)
    (v : Fin n → V) (hv : ∀ i, v i ∈ F i.succ)
    (hnot : ∀ i, v i ∉ F i.castSucc) : LinearIndependent K v := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
      rw [linearIndependent_finSucc']
      constructor
      · apply ih (fun j => F j.castSucc)
          (fun i j hij => hF (Fin.castSucc_le_castSucc_iff.mpr hij))
          (Fin.init v)
        · intro i
          simpa only [Fin.init, Fin.castSucc_succ] using hv i.castSucc
        · intro i
          exact hnot i.castSucc
      · intro h
        apply hnot (Fin.last n)
        apply (Submodule.span_le.mpr ?_) h
        · rintro _ ⟨i, rfl⟩
          exact hF (by
            change i.val + 1 ≤ n
            omega) (hv i.castSucc)

private theorem exists_fullFlag_step {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j) (i : Fin N) :
    ∃ v, v ∈ F i.succ ∧ v ∉ F i.castSucc := by
  apply SetLike.exists_of_lt
  apply lt_of_le_of_ne (hF (by
    change i.val ≤ i.val + 1
    omega))
  intro he
  have he' := congrArg (fun W : Submodule K (Fin N → K) => Module.finrank K W) he
  rw [hdim, hdim] at he'
  change i.val = i.val + 1 at he'
  omega

/-- Choose one vector in each successive difference of a full flag. -/
def fullFlagVector {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j) (i : Fin N) : Fin N → K :=
  Classical.choose (exists_fullFlag_step F hF hdim i)

theorem fullFlagVector_mem {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j) (i : Fin N) :
    fullFlagVector F hF hdim i ∈ F i.succ :=
  (Classical.choose_spec (exists_fullFlag_step F hF hdim i)).1

theorem fullFlagVector_not_mem {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j) (i : Fin N) :
    fullFlagVector F hF hdim i ∉ F i.castSucc :=
  (Classical.choose_spec (exists_fullFlag_step F hF hdim i)).2

/-- A basis obtained by choosing vectors in the successive differences of a full flag. -/
def fullFlagBasis {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j) :
    Module.Basis (Fin N) K (Fin N → K) :=
  basisOfLinearIndependentOfCardEqFinrank' (fullFlagVector F hF hdim)
    (independent_of_fullFlag_steps F hF _ (fullFlagVector_mem F hF hdim)
      (fullFlagVector_not_mem F hF hdim)) (by simp)

@[simp] theorem fullFlagBasis_apply {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j) (i : Fin N) :
    fullFlagBasis F hF hdim i = fullFlagVector F hF hdim i := by
  simp [fullFlagBasis]

private theorem finrank_basis_flag {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {N : ℕ}
    (b : Module.Basis (Fin N) K V) (j : Fin (N + 1)) :
    Module.finrank K (b.flag j) = j := by
  let f : Fin j.val → Fin N := fun i =>
    ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩
  have hf : Function.Injective f := by
    intro i i' h
    exact Fin.ext (congrArg (fun t : Fin N => t.val) h)
  have hs : b '' {i | i.castSucc < j} = Set.range (b ∘ f) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, congrArg b (Fin.ext rfl)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, i.isLt, rfl⟩
  rw [Module.Basis.flag, hs, finrank_span_eq_card (b.linearIndependent.comp f hf)]
  simp

/-- The constructed basis realizes every member of the original full flag. -/
@[simp] theorem fullFlagBasis_flag {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j) (j : Fin (N + 1)) :
    (fullFlagBasis F hF hdim).flag j = F j := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply (Module.Basis.flag_le_iff _).mpr
    intro i hi
    rw [fullFlagBasis_apply]
    exact hF (by
      change i.val + 1 ≤ j.val
      exact hi) (fullFlagVector_mem F hF hdim i)
  · rw [finrank_basis_flag, hdim]

/-- Express an invertible matrix in the coordinates of a chosen basis. -/
def basisCoordinates {K : Type*} [Field K] {N : ℕ}
    (b : Module.Basis (Fin N) K (Fin N → K)) :
    Matrix.GeneralLinearGroup (Fin N) K ≃* Matrix.GeneralLinearGroup (Fin N) K :=
  Matrix.GeneralLinearGroup.toLin.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

theorem basisCoordinates_apply {K : Type*} [Field K] {N : ℕ}
    (b : Module.Basis (Fin N) K (Fin N → K))
    (g : Matrix.GeneralLinearGroup (Fin N) K) (i j : Fin N) :
    (basisCoordinates b g : Matrix (Fin N) (Fin N) K) i j =
      b.repr ((g : Matrix (Fin N) (Fin N) K) *ᵥ b j) i := by
  change LinearMap.toMatrixAlgEquiv b
      (Matrix.GeneralLinearGroup.toLin g : (Fin N → K) →ₗ[K] (Fin N → K)) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

theorem basisCoordinates_mem_upperTriangular {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j)
    (g : Matrix.GeneralLinearGroup (Fin N) K)
    (hg : ∀ j, ∀ v ∈ F j, (g : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ F j) :
    basisCoordinates (fullFlagBasis F hF hdim) g ∈
      Langlands.GeneralLinear.upperTriangularSubgroup N K := by
  rw [Langlands.GeneralLinear.mem_upperTriangularSubgroup_iff]
  intro i j hji
  rw [basisCoordinates_apply]
  apply ((fullFlagBasis F hF hdim).mem_flag_iff_repr_eq_zero (k := j.succ)).mp ?_ i
    (by exact hji)
  rw [fullFlagBasis_flag]
  apply hg
  rw [fullFlagBasis_apply]
  exact fullFlagVector_mem F hF hdim j

/-- A flag-preserving subgroup embeds into the upper triangular group in adapted coordinates. -/
def fullFlagTriangularEmbedding {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) K))
    (hG : ∀ g ∈ G, ∀ j, ∀ v ∈ F j,
      (g : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ F j) :
    G →* Langlands.GeneralLinear.upperTriangularSubgroup N K where
  toFun g := ⟨basisCoordinates (fullFlagBasis F hF hdim) g.val,
    basisCoordinates_mem_upperTriangular F hF hdim g.val (hG g.val g.property)⟩
  map_one' := Subtype.ext (basisCoordinates (fullFlagBasis F hF hdim)).map_one
  map_mul' g h :=
    Subtype.ext ((basisCoordinates (fullFlagBasis F hF hdim)).map_mul g.val h.val)

@[simp] theorem fullFlagTriangularEmbedding_val {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) K))
    (hG : ∀ g ∈ G, ∀ j, ∀ v ∈ F j,
      (g : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ F j) (g : G) :
    (fullFlagTriangularEmbedding F hF hdim G hG g).val =
      basisCoordinates (fullFlagBasis F hF hdim) g.val := rfl

theorem fullFlagTriangularEmbedding_injective {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) K))
    (hG : ∀ g ∈ G, ∀ j, ∀ v ∈ F j,
      (g : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ F j) :
    Function.Injective (fullFlagTriangularEmbedding F hF hdim G hG) := by
  intro g h he
  apply Subtype.ext
  apply (basisCoordinates (fullFlagBasis F hF hdim)).injective
  exact congrArg
    (fun x : Langlands.GeneralLinear.upperTriangularSubgroup N K => x.val) he

/-- A subgroup of `GL_N(K)` preserving a full flag is solvable. -/
theorem isSolvable_of_mulVec_mem_fullFlag {K : Type*} [Field K] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) K))
    (hG : ∀ g ∈ G, ∀ j, ∀ v ∈ F j,
      (g : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ F j) :
    Group.IsSolvable G := by
  have := Langlands.GeneralLinear.UpperTriangularSolvable.isSolvable N K
  exact Group.isSolvable_of_isSolvable_injective
    (fullFlagTriangularEmbedding_injective F hF hdim G hG)

/-- A faithful linear representation preserving a full flag has solvable source. -/
theorem isSolvable_of_injective_representation_fullFlag {K H : Type*} [Field K]
    [Group H] {N : ℕ}
    (F : Fin (N + 1) → Submodule K (Fin N → K)) (hF : Monotone F)
    (hdim : ∀ j, Module.finrank K (F j) = j)
    (ρ : H →* Matrix.GeneralLinearGroup (Fin N) K) (hρ : Function.Injective ρ)
    (hpres : ∀ h, ∀ j, ∀ v ∈ F j,
      (ρ h : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ F j) :
    Group.IsSolvable H := by
  have : Group.IsSolvable ρ.range := isSolvable_of_mulVec_mem_fullFlag F hF hdim
    ρ.range (by
      rintro _ ⟨h, rfl⟩
      exact hpres h)
  exact Group.isSolvable_of_isSolvable_injective
    (f := ρ.rangeRestrict) (by
      intro h h' he
      exact hρ (congrArg (fun g : ρ.range => g.val) he))

end Langlands.LinearAlgebra
