import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Split
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free

/-! # Spreading middle exactness of a three-term complex from a field point to modules -/

universe u

open TensorProduct

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.ObstructionCone.ExactSpread

variable {A : Type u} [CommRing A]

/-- Multiplication by a scalar that is bijective on `M` is bijective on `N ⊗ M`. -/
lemma smul_bijective_tensor {M : Type*} [AddCommGroup M] [Module A M] (N : Type*)
    [AddCommGroup N] [Module A N] {g : A} (hg : Function.Bijective (fun m : M => g • m)) :
    Function.Bijective (fun t : N ⊗[A] M => g • t) := by
  let e : M ≃ₗ[A] M := LinearEquiv.ofBijective (g • LinearMap.id) hg
  have he : (fun t : N ⊗[A] M => g • t) = e.lTensor N := by
    funext t
    induction t using TensorProduct.inductionOn with
    | tmul n m =>
        simp [e, TensorProduct.tmul_smul]
    | add x y hx hy =>
        rw [smul_add, map_add, ← hx, ← hy]
  rw [he]
  exact (e.lTensor N).bijective

/-- A left inverse up to a scalar that is bijective on `M` gives injectivity after `⊗ M`. -/
lemma injective_rTensor_of_comp_eq_smul {E N : Type*} [AddCommGroup E] [Module A E]
    [AddCommGroup N] [Module A N] (h : E →ₗ[A] N) (ψ : N →ₗ[A] E) {g : A}
    (hψ : ψ ∘ₗ h = g • LinearMap.id) {M : Type*} [AddCommGroup M] [Module A M]
    (hg : Function.Bijective (fun m : M => g • m)) : Function.Injective (h.rTensor M) := by
  intro x y hxy
  have := congrArg (ψ.rTensor M) hxy
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hψ,
    LinearMap.rTensor_smul, LinearMap.rTensor_id] at this
  exact (smul_bijective_tensor E hg).injective (by simpa using this)

/-- A right inverse up to a scalar that is bijective on `M` gives surjectivity after `⊗ M`. -/
lemma surjective_rTensor_of_comp_eq_smul {E N : Type*} [AddCommGroup E] [Module A E]
    [AddCommGroup N] [Module A N] (f : E →ₗ[A] N) (f' : N →ₗ[A] E) {g : A}
    (hf : f ∘ₗ f' = g • LinearMap.id) {M : Type*} [AddCommGroup M] [Module A M]
    (hg : Function.Bijective (fun m : M => g • m)) : Function.Surjective (f.rTensor M) := by
  intro y
  obtain ⟨y', rfl⟩ := (smul_bijective_tensor N hg).surjective y
  refine ⟨f'.rTensor M y', ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hf, LinearMap.rTensor_smul,
    LinearMap.rTensor_id]
  simp

/-- An endomorphism of a finite free module has a right inverse up to its determinant. -/
lemma exists_comp_eq_det_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → A) →ₗ[A] (ι → A)) : ∃ f' : (ι → A) →ₗ[A] (ι → A),
      f ∘ₗ f' = LinearMap.det f • LinearMap.id := by
  set m := LinearMap.toMatrix' f with hm
  have hf : f = Matrix.toLin' m := by rw [hm, Matrix.toLin'_toMatrix']
  refine ⟨Matrix.toLin' m.adjugate, ?_⟩
  rw [hf, ← Matrix.toLin'_mul, Matrix.mul_adjugate, ← hf, ← LinearMap.det_toMatrix', ← hm,
    map_smul, Matrix.toLin'_one]

/-- If an endomorphism of a finite free module becomes bijective over a field, its
determinant is nonzero there. -/
lemma algebraMap_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → A) →ₗ[A] (ι → A)) (k : Type*) [Field k] [Algebra A k]
    (hf : Function.Bijective (f.baseChange k)) : algebraMap A k (LinearMap.det f) ≠ 0 := by
  rw [← LinearMap.det_baseChange]
  have hu : IsUnit (f.baseChange k) := (Module.End.isUnit_iff _).mpr hf
  exact (LinearMap.isUnit_det _ hu).ne_zero


/-- A split injection stays injective after base change. -/
lemma rTensor_injective_of_retract {N P : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] {s : N →ₗ[A] P} {π : P →ₗ[A] N}
    (h : π ∘ₗ s = LinearMap.id) (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (s.rTensor M) := by
  intro x y hxy
  have := congrArg (π.rTensor M) hxy
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, h,
    LinearMap.rTensor_id, LinearMap.id_apply, LinearMap.id_apply] at this

/-- A split injection stays injective after base change to an algebra. -/
lemma baseChange_injective_of_retract {N P : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] {s : N →ₗ[A] P} {π : P →ₗ[A] N}
    (h : π ∘ₗ s = LinearMap.id) (K : Type*) [CommRing K] [Algebra A K] :
    Function.Injective (s.baseChange K) := by
  intro x y hxy
  have := congrArg (π.baseChange K) hxy
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h,
    LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this

/-- A finite projective module is a retract of a finite free module. -/
lemma exists_retract (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Projective A N] :
    ∃ (m : ℕ) (s : N →ₗ[A] (Fin m → A)) (π : (Fin m → A) →ₗ[A] N),
      π ∘ₗ s = LinearMap.id := by
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  exact ⟨m, s, π, hs⟩

/-- The span of the images of a generating family after base change to a field. -/
lemma span_range_baseChange {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (f : M →ₗ[A] N) {p : ℕ} (π : (Fin p → A) →ₗ[A] M)
    (hπ : Function.Surjective π) (k : Type*) [Field k] [Algebra A k] :
    Submodule.span k (Set.range (fun l : Fin p => f.baseChange k (1 ⊗ₜ π (Pi.single l 1)))) =
      LinearMap.range (f.baseChange k) := by
  let bp := Algebra.TensorProduct.basis k (Pi.basisFun A (Fin p))
  have h1 : LinearMap.range (f.baseChange k) = LinearMap.range ((f ∘ₗ π).baseChange k) := by
    rw [LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr (LinearMap.baseChange_surjective k hπ)
  have h2 : (fun l : Fin p => f.baseChange k (1 ⊗ₜ π (Pi.single l 1))) =
      (f ∘ₗ π).baseChange k ∘ bp := by
    funext l
    simp [bp, Algebra.TensorProduct.basis_apply]
  rw [h1, h2, LinearMap.range_eq_map, ← bp.span_eq, Submodule.map_span, ← Set.range_comp]


/-- Restricting a standard basis vector of `κ₁ ⊕ κ₂ → A` to one summand. -/
lemma funLeft_single_inl {κ₁ κ₂ : Type*} [DecidableEq κ₁] [DecidableEq κ₂] (i : κ₁) :
    LinearMap.funLeft A A (Sum.inl : κ₁ → κ₁ ⊕ κ₂) (Pi.single (Sum.inl i) 1) = Pi.single i 1 := by
  funext j
  simp [LinearMap.funLeft_apply, Pi.single_apply]

lemma funLeft_single_inr_inl {κ₁ κ₂ : Type*} [DecidableEq κ₁] [DecidableEq κ₂] (i : κ₁) :
    LinearMap.funLeft A A (Sum.inr : κ₂ → κ₁ ⊕ κ₂) (Pi.single (Sum.inl i) 1) = 0 := by
  funext j
  simp [LinearMap.funLeft_apply]

lemma funLeft_single_inr {κ₁ κ₂ : Type*} [DecidableEq κ₁] [DecidableEq κ₂] (j : κ₂) :
    LinearMap.funLeft A A (Sum.inr : κ₂ → κ₁ ⊕ κ₂) (Pi.single (Sum.inr j) 1) = Pi.single j 1 := by
  funext i
  simp [LinearMap.funLeft_apply, Pi.single_apply]

lemma funLeft_single_inl_inr {κ₁ κ₂ : Type*} [DecidableEq κ₁] [DecidableEq κ₂] (j : κ₂) :
    LinearMap.funLeft A A (Sum.inl : κ₁ → κ₁ ⊕ κ₂) (Pi.single (Sum.inr j) 1) = 0 := by
  funext i
  simp [LinearMap.funLeft_apply]

/-- If a product of two scalars acts bijectively, so does each factor. -/
lemma smul_bijective_of_mul {M : Type*} [AddCommGroup M] [Module A M] {g h : A}
    (H : Function.Bijective (fun m : M => (g * h) • m)) :
    Function.Bijective (fun m : M => g • m) ∧ Function.Bijective (fun m : M => h • m) := by
  refine ⟨⟨fun m m' hm => H.injective ?_, fun m => ?_⟩,
    ⟨fun m m' hm => H.injective ?_, fun m => ?_⟩⟩
  · simp only at hm ⊢
    rw [mul_comm, mul_smul, mul_smul, hm]
  · obtain ⟨m'', rfl⟩ := H.surjective m
    exact ⟨h • m'', by simp [mul_smul]⟩
  · simp only at hm ⊢
    rw [mul_smul, mul_smul, hm]
  · obtain ⟨m'', rfl⟩ := H.surjective m
    exact ⟨g • m'', by simp only; rw [smul_smul, mul_comm]⟩

/-- Middle exactness of a three-term complex with finite projective middle and target
spreads from one field point to every module on which a single element acts bijectively. -/
theorem exists_exact_rTensor_spread {F₁ F₂ F₃ : Type u} [AddCommGroup F₁] [Module A F₁]
    [AddCommGroup F₂] [Module A F₂] [AddCommGroup F₃] [Module A F₃] [Module.Finite A F₁]
    [Module.Finite A F₂] [Module.Projective A F₂] [Module.Finite A F₃] [Module.Projective A F₃]
    (a : F₁ →ₗ[A] F₂) (b : F₂ →ₗ[A] F₃) (hba : b ∘ₗ a = 0)
    (k : Type u) [Field k] [Algebra A k]
    (hk : Function.Exact (a.baseChange k) (b.baseChange k)) :
    ∃ g : A, algebraMap A k g ≠ 0 ∧ ∀ (M : Type u) [AddCommGroup M] [Module A M],
      Function.Bijective (fun m : M => g • m) → Function.Exact (a.rTensor M) (b.rTensor M) := by
  classical
  have : Nontrivial A := (algebraMap A k).domain_nontrivial
  have hk' : LinearMap.ker (b.baseChange k) = LinearMap.range (a.baseChange k) :=
    LinearMap.exact_iff.mp hk
  -- a family of images under `a` forming a basis of the range of `a` at `k`
  obtain ⟨p, π₁, hπ₁⟩ := Module.Finite.exists_fin' A F₁
  obtain ⟨κ₁, α₁, hα₁, hsp₁, hli₁⟩ := exists_linearIndependent' k
    (fun l : Fin p => a.baseChange k (1 ⊗ₜ π₁ (Pi.single l 1)))
  rw [span_range_baseChange a π₁ hπ₁ k] at hsp₁
  -- a family of elements whose images under `b` form a basis of the range of `b` at `k`
  obtain ⟨q, σ, hσ⟩ := Module.Finite.exists_fin' A F₂
  obtain ⟨κ₂, α₂, hα₂, hsp₂, hli₂⟩ := exists_linearIndependent' k
    (fun l : Fin q => b.baseChange k (1 ⊗ₜ σ (Pi.single l 1)))
  rw [span_range_baseChange b σ hσ k] at hsp₂
  have : Finite κ₁ := Finite.of_injective α₁ hα₁
  have : Finite κ₂ := Finite.of_injective α₂ hα₂
  let : Fintype κ₁ := Fintype.ofFinite κ₁
  let : Fintype κ₂ := Fintype.ofFinite κ₂
  let x : κ₁ → F₁ := fun i => π₁ (Pi.single (α₁ i) 1)
  let z : κ₂ → F₂ := fun j => σ (Pi.single (α₂ j) 1)
  let X : (κ₁ → A) →ₗ[A] F₁ := Fintype.linearCombination A x
  let Z : (κ₂ → A) →ₗ[A] F₂ := Fintype.linearCombination A z
  let e : (κ₁ ⊕ κ₂ → A) →ₗ[A] F₂ :=
    a ∘ₗ X ∘ₗ LinearMap.funLeft A A Sum.inl + Z ∘ₗ LinearMap.funLeft A A Sum.inr
  let h₂ : (κ₂ → A) →ₗ[A] F₃ := b ∘ₗ Z
  have hbe : b ∘ₗ e = h₂ ∘ₗ LinearMap.funLeft A A Sum.inr := by
    simp only [e, h₂, LinearMap.comp_add]
    rw [← LinearMap.comp_assoc, hba, LinearMap.zero_comp, zero_add, LinearMap.comp_assoc]
  -- the map `e` is bijective at `k`
  let bE := Algebra.TensorProduct.basis k (Pi.basisFun A (κ₁ ⊕ κ₂))
  let v : κ₁ → k ⊗[A] F₂ := fun i => a.baseChange k (1 ⊗ₜ x i)
  let w : κ₂ → k ⊗[A] F₂ := fun j => 1 ⊗ₜ z j
  let u : κ₁ ⊕ κ₂ → k ⊗[A] F₂ := Sum.elim v w
  have heu : e.baseChange k = bE.constr k u := by
    apply bE.ext
    intro t
    rw [Module.Basis.constr_basis]
    cases t with
    | inl i =>
        simp [bE, u, v, e, X, Algebra.TensorProduct.basis_apply, funLeft_single_inl,
          funLeft_single_inr_inl, Fintype.linearCombination_apply_single]
    | inr j =>
        simp [bE, u, w, e, Z, Algebra.TensorProduct.basis_apply, funLeft_single_inr,
          funLeft_single_inl_inr, Fintype.linearCombination_apply_single]
  have hbw : (b.baseChange k) ∘ w = (fun l : Fin q => b.baseChange k (1 ⊗ₜ σ (Pi.single l 1))) ∘ α₂ := by
    funext j
    simp [w, z]
  have hliw : LinearIndependent k w := by
    apply LinearIndependent.of_comp (b.baseChange k)
    rw [hbw]
    exact hli₂
  have hvker : ∀ y ∈ Submodule.span k (Set.range v), b.baseChange k y = 0 := by
    intro y hy
    have hy' : y ∈ LinearMap.range (a.baseChange k) := by
      refine Submodule.span_le.mpr ?_ hy
      rintro _ ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    rw [← hk'] at hy'
    exact hy'
  have hliu : LinearIndependent k u := by
    apply LinearIndependent.sum_type hli₁ hliw
    rw [Submodule.disjoint_def]
    intro y hy₁ hy₂
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hy₂
    have h0 := hvker _ hy₁
    rw [map_sum] at h0
    simp only [map_smul] at h0
    have hc := (Fintype.linearIndependent_iff.mp hli₂) c (by
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [w, z])
    simp [hc]
  have hspu : Submodule.span k (Set.range u) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hby : b.baseChange k y ∈ Submodule.span k
        (Set.range ((fun l : Fin q => b.baseChange k (1 ⊗ₜ σ (Pi.single l 1))) ∘ α₂)) := by
      rw [hsp₂]
      exact ⟨y, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hby
    let y' : k ⊗[A] F₂ := ∑ j, c j • w j
    have hy'y : y - y' ∈ LinearMap.range (a.baseChange k) := by
      rw [← hk', LinearMap.mem_ker, map_sub, sub_eq_zero, ← hc]
      simp only [y', map_sum, map_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [w, z]
    rw [← hsp₁] at hy'y
    have hv : Submodule.span k (Set.range ((fun l : Fin p =>
        a.baseChange k (1 ⊗ₜ π₁ (Pi.single l 1))) ∘ α₁)) = Submodule.span k (Set.range v) := by
      rfl
    rw [hv] at hy'y
    have hy' : y' ∈ Submodule.span k (Set.range w) :=
      (Submodule.mem_span_range_iff_exists_fun k).mpr ⟨c, rfl⟩
    rw [Set.Sum.elim_range, Submodule.span_union]
    rw [← sub_add_cancel y y']
    exact Submodule.add_mem_sup hy'y hy'
  have hek : Function.Bijective (e.baseChange k) := by
    refine ⟨?_, ?_⟩
    · rw [heu]
      exact bE.injective_constr_of_linearIndependent hliu
    · rw [← LinearMap.range_eq_top, heu, Module.Basis.constr_range, hspu]
  -- the map `h₂` is injective at `k`
  let bZ := Algebra.TensorProduct.basis k (Pi.basisFun A κ₂)
  have hh₂k : Function.Injective (h₂.baseChange k) := by
    have : h₂.baseChange k = bZ.constr k ((b.baseChange k) ∘ w) := by
      apply bZ.ext
      intro j
      rw [Module.Basis.constr_basis]
      simp [bZ, h₂, Z, w, Algebra.TensorProduct.basis_apply,
        Fintype.linearCombination_apply_single]
    rw [this, hbw]
    exact bZ.injective_constr_of_linearIndependent hli₂
  -- left inverses up to scalars
  obtain ⟨m₂, s₂, π₂, hsπ₂⟩ := exists_retract (A := A) F₂
  obtain ⟨m₃, s₃, π₃, hsπ₃⟩ := exists_retract (A := A) F₃
  obtain ⟨g₁, hg₁, ψ₁, ψ₁', hψ₁⟩ :=
    Langlands.Cohomology.ModuleComplex.FibreH0Spread.exists_split_of_baseChange (k := k)
      (s₂ ∘ₗ e) (s₂ ∘ₗ e) (by
        intro y hy _
        rw [LinearMap.baseChange_comp, LinearMap.comp_apply] at hy
        exact hek.injective
          ((baseChange_injective_of_retract hsπ₂ k) (by rw [hy, map_zero, map_zero])))
  obtain ⟨g₃, hg₃, ψ₃, ψ₃', hψ₃⟩ :=
    Langlands.Cohomology.ModuleComplex.FibreH0Spread.exists_split_of_baseChange (k := k)
      (s₃ ∘ₗ h₂) (s₃ ∘ₗ h₂) (by
        intro y hy _
        rw [LinearMap.baseChange_comp, LinearMap.comp_apply] at hy
        exact hh₂k ((baseChange_injective_of_retract hsπ₃ k) (by rw [hy, map_zero, map_zero])))
  let L : F₂ →ₗ[A] (κ₁ ⊕ κ₂ → A) := (ψ₁ + ψ₁') ∘ₗ s₂
  have hLe : L ∘ₗ e = g₁ • LinearMap.id := by
    rw [← hψ₁]
    simp only [L, LinearMap.comp_assoc, LinearMap.add_comp]
  let H : F₃ →ₗ[A] (κ₂ → A) := (ψ₃ + ψ₃') ∘ₗ s₃
  have hHh : H ∘ₗ h₂ = g₃ • LinearMap.id := by
    rw [← hψ₃]
    simp only [H, LinearMap.comp_assoc, LinearMap.add_comp]
  -- a square matrix controlling surjectivity of `e`
  let Φ : (Fin m₂ → A) →ₗ[A] (Fin m₂ → A) :=
    s₂ ∘ₗ e ∘ₗ L ∘ₗ π₂ + (LinearMap.id - s₂ ∘ₗ π₂)
  have hπΦ : π₂ ∘ₗ Φ = e ∘ₗ L ∘ₗ π₂ := by
    simp only [Φ, LinearMap.comp_add, LinearMap.comp_sub, LinearMap.comp_id]
    simp only [← LinearMap.comp_assoc, hsπ₂, LinearMap.id_comp, sub_self, add_zero]
  have heLk : ∀ y : k ⊗[A] F₂, e.baseChange k (L.baseChange k y) = algebraMap A k g₁ • y := by
    intro y
    obtain ⟨c, rfl⟩ := hek.surjective y
    rw [← LinearMap.comp_apply (L.baseChange k), ← LinearMap.baseChange_comp, hLe,
      LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply,
      LinearMap.id_apply, ← algebraMap_smul k g₁ c, map_smul]
  have hΦk : Function.Bijective (Φ.baseChange k) := by
    have hinj : Function.Injective (Φ.baseChange k) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      have h1 : π₂.baseChange k (Φ.baseChange k y) = 0 := by rw [hy, map_zero]
      rw [← LinearMap.comp_apply (π₂.baseChange k), ← LinearMap.baseChange_comp, hπΦ,
        LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply,
        LinearMap.comp_apply, heLk] at h1
      have h2 : π₂.baseChange k y = 0 := (smul_eq_zero.mp h1).resolve_left hg₁
      have h3 : Φ.baseChange k y = y := by
        simp only [Φ, LinearMap.baseChange_add, LinearMap.baseChange_sub,
          LinearMap.baseChange_comp, LinearMap.baseChange_id, LinearMap.add_apply,
          LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, h2, map_zero,
          zero_add, sub_zero]
      rw [← h3, hy]
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hg₂ := algebraMap_det_ne_zero Φ k hΦk
  obtain ⟨Φ', hΦ'⟩ := exists_comp_eq_det_smul Φ
  refine ⟨LinearMap.det Φ * g₃, by simp [hg₂, hg₃], fun M _ _ hM => ?_⟩
  obtain ⟨hM₂, hM₃⟩ := smul_bijective_of_mul hM
  have hesurj : Function.Surjective (e.rTensor M) := by
    intro y
    obtain ⟨t, ht⟩ := surjective_rTensor_of_comp_eq_smul Φ Φ' hΦ' hM₂ (s₂.rTensor M y)
    refine ⟨(L ∘ₗ π₂).rTensor M t, ?_⟩
    have := congrArg (π₂.rTensor M) ht
    rw [← LinearMap.comp_apply (π₂.rTensor M) (s₂.rTensor M), ← LinearMap.rTensor_comp, hsπ₂,
      LinearMap.rTensor_id, LinearMap.id_apply, ← LinearMap.comp_apply (π₂.rTensor M),
      ← LinearMap.rTensor_comp, hπΦ] at this
    rw [← this, ← LinearMap.comp_apply (e.rTensor M), ← LinearMap.rTensor_comp]
  have hh₂inj : Function.Injective (h₂.rTensor M) :=
    injective_rTensor_of_comp_eq_smul h₂ H hHh hM₃
  intro y
  constructor
  · intro hy
    obtain ⟨c, rfl⟩ := hesurj y
    have h1 : h₂.rTensor M ((LinearMap.funLeft A A Sum.inr).rTensor M c) = 0 := by
      rw [← LinearMap.comp_apply (h₂.rTensor M), ← LinearMap.rTensor_comp, ← hbe,
        LinearMap.rTensor_comp, LinearMap.comp_apply]
      exact hy
    have h2 : (LinearMap.funLeft A A Sum.inr).rTensor M c = 0 :=
      hh₂inj (by rw [h1, map_zero])
    refine ⟨(X ∘ₗ LinearMap.funLeft A A Sum.inl).rTensor M c, ?_⟩
    simp only [e, LinearMap.rTensor_add, LinearMap.add_apply, LinearMap.rTensor_comp,
      LinearMap.comp_apply] at h2 ⊢
    rw [h2, map_zero, add_zero]
  · rintro ⟨t, rfl⟩
    rw [← LinearMap.comp_apply (b.rTensor M), ← LinearMap.rTensor_comp, hba,
      LinearMap.rTensor_zero, LinearMap.zero_apply]

end Langlands.Cohomology.ModuleComplex.ObstructionCone.ExactSpread
