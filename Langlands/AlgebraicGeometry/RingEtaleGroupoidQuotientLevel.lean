import Langlands.AlgebraicGeometry.RingEtaleGroupoidStableSubalgebra

/-! # A Čech presentation of the relation ring at a finitely generated level

Let `t₀ : B₀ →+* C₀` be a ring étale groupoid with `C₀` of finite type over `B₀`, and let `θ'`
be a multiplicative coaction on a `B₀`-algebra `B'`. Suppose that a flat `A₁`-algebra `B₁` of
finite type over `ℤ` and a ring map `φ : B₁ → B'` present the relation ring: the map
`B₁ ⊗[A₁] B' → C₀ ⊗[B₀] B'`, `b ⊗ d ↦ θ'(φ b) * (1 ⊗ d)`, is bijective. Then there is a finite
set `s ⊆ B'` such that for every stable subalgebra `D' ⊇ s` the same formula gives a bijection
`B₁ ⊗[A₁] D' → C₀ ⊗[B₀] D'`. This is the ring form of the comparison in the proof of Stacks
Project Lemma 70.5.10 (Tag 07SQ) used in the fourth step of the proof of Lemma 70.15.1.
-/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry

namespace RingEtaleGroupoid

open GroupoidCoaction

variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀] [Algebra B₀ C₀] {t₀ : B₀ →+* C₀}
  {B' : Type u} [CommRing B'] [Algebra B₀ B']
  {A₁ B₁ : Type u} [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁]

/-- The presentation of the relation ring by `B₁ ⊗[A₁] B'` descends to every stable subalgebra
that contains a suitable finite set. -/
theorem exists_bijective_level [Algebra.FiniteType B₀ C₀] [Module.Flat A₁ B₁]
    [Algebra.FiniteType ℤ B₁] (hE₀ : RingEtaleGroupoid t₀) (θ' : GroupoidCoaction t₀ B')
    (hθ' : θ'.IsMultiplicative) (φ : B₁ →+* B') :
    letI : Algebra A₁ B' := (φ.comp (algebraMap A₁ B₁)).toAlgebra
    ∀ L : B₁ ⊗[A₁] B' →+* C₀ ⊗[B₀] B',
      (∀ b d, L (b ⊗ₜ d) = θ'.coaction (φ b) * ((1 : C₀) ⊗ₜ d)) → Function.Bijective L →
      ∃ s : Finset B', ∀ (D' : Subalgebra B₀ B') (hD' : θ'.IsStableSubalgebra D'),
        (s : Set B') ⊆ D' →
        ∃ φ' : B₁ →+* D', (∀ b, (φ' b : B') = φ b) ∧
          (letI : Algebra A₁ D' := (φ'.comp (algebraMap A₁ B₁)).toAlgebra
          ∃ F : B₁ ⊗[A₁] D' →+* C₀ ⊗[B₀] D',
            (∀ b d, F (b ⊗ₜ d) =
              (hE₀.subalgebraCoaction θ' D' hD').coaction (φ' b) * ((1 : C₀) ⊗ₜ d)) ∧
            Function.Bijective F) := by
  classical
  let _ : Algebra A₁ B' := (φ.comp (algebraMap A₁ B₁)).toAlgebra
  intro L hL hbij
  obtain ⟨G₁, hG₁⟩ := Algebra.FiniteType.out (R := ℤ) (A := B₁)
  obtain ⟨G₀, hG₀⟩ := Algebra.FiniteType.out (R := B₀) (A := C₀)
  choose w hw using fun c : C₀ => hbij.2 (c ⊗ₜ[B₀] (1 : B'))
  obtain ⟨N, hNfin, hN⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ((G₀.image w : Finset (B₁ ⊗[A₁] B')) : Set (B₁ ⊗[A₁] B')) (Finset.finite_toSet _)
  obtain ⟨T, hT⟩ := (Module.Finite.iff_fg (N := N)).mp hNfin
  refine ⟨G₁.image φ ∪ T, ?_⟩
  intro D' hD' hs
  have hφD : ∀ b, φ b ∈ D' := by
    let S : Subring B₁ := D'.toSubring.comap φ
    have hle : (⊤ : Subalgebra ℤ B₁) ≤ subalgebraOfSubring S := by
      rw [← hG₁, Algebra.adjoin_le_iff]
      intro g hg
      exact hs (Finset.mem_coe.mpr (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨g, Finset.mem_coe.mp hg, rfl⟩)))
    intro b
    exact hle Algebra.mem_top
  let φ' : B₁ →+* D' := φ.codRestrict D' hφD
  refine ⟨φ', fun _ => rfl, ?_⟩
  let _ : Algebra A₁ D' := (φ'.comp (algebraMap A₁ B₁)).toAlgebra
  let θD := hE₀.subalgebraCoaction θ' D' hD'
  have hθD : θD.IsMultiplicative := hE₀.subalgebraCoaction_isMultiplicative θ' hθ' D' hD'
  let M : C₀ ⊗[B₀] D' →ₐ[B₀] C₀ ⊗[B₀] B' := Algebra.TensorProduct.map (AlgHom.id B₀ C₀) D'.val
  have hMinj : Function.Injective M := by
    intro x y hxy
    apply hE₀.lTensor_val_injective D'
    rw [lTensor_eq_map, lTensor_eq_map]
    exact hxy
  have hMθ : ∀ x : D', M (θD.coaction x) = θ'.coaction x :=
    hE₀.subalgebraCoaction_val θ' D' hD'
  have hM1 : ∀ x : D', M ((1 : C₀) ⊗ₜ x) = (1 : C₀) ⊗ₜ (x : B') := fun _ => rfl
  have hinvB : ∀ a : A₁, θ'.coaction (φ (algebraMap A₁ B₁ a)) =
      (1 : C₀) ⊗ₜ φ (algebraMap A₁ B₁ a) := by
    intro a
    have h1 := hL (algebraMap A₁ B₁ a) 1
    have h2 := hL 1 (algebraMap A₁ B' a)
    rw [algebraMap_tmul_one, h2, map_one, hθ'.map_one, one_mul] at h1
    rw [← Algebra.TensorProduct.one_def, mul_one] at h1
    exact h1.symm
  have hinv : (((θD.toRingHom hθD).comp φ').comp (algebraMap A₁ B₁)) =
      (Algebra.TensorProduct.includeRight : D' →ₐ[B₀] C₀ ⊗[B₀] D').toRingHom.comp
        (algebraMap A₁ D') := by
    ext a
    apply hMinj
    change M (θD.coaction (φ' (algebraMap A₁ B₁ a))) = M ((1 : C₀) ⊗ₜ φ' (algebraMap A₁ B₁ a))
    rw [hMθ, hM1]
    exact hinvB a
  let F : B₁ ⊗[A₁] D' →+* C₀ ⊗[B₀] D' :=
    tensorLift ((θD.toRingHom hθD).comp φ')
      (Algebra.TensorProduct.includeRight : D' →ₐ[B₀] C₀ ⊗[B₀] D').toRingHom hinv
  have hF : ∀ b d, F (b ⊗ₜ d) = θD.coaction (φ' b) * ((1 : C₀) ⊗ₜ d) := fun b d =>
    tensorLift_tmul ((θD.toRingHom hθD).comp φ')
      (Algebra.TensorProduct.includeRight : D' →ₐ[B₀] C₀ ⊗[B₀] D').toRingHom hinv b d
  let ι : D' →ₗ[A₁] B' :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcompat : ∀ z, M (F z) = L (LinearMap.lTensor B₁ ι z) := by
    intro z
    induction z with
    | tmul b d =>
      rw [hF, map_mul, hMθ, hM1]
      change θ'.coaction (φ b) * ((1 : C₀) ⊗ₜ (d : B')) = L (b ⊗ₜ (d : B'))
      rw [hL]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hι : Function.Injective (LinearMap.lTensor B₁ ι) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι Subtype.val_injective
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply hι
    apply hbij.1
    rw [← hcompat, ← hcompat, hxy]
  have hincR : ∀ d : D', (1 : C₀) ⊗ₜ[B₀] d ∈ F.range := fun d =>
    ⟨1 ⊗ₜ d, by rw [hF, map_one, hθD.map_one, one_mul]⟩
  have hND : ∀ x ∈ N, x ∈ D' := by
    intro x hx
    rw [← hT] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hs (by simp [hx])
    | zero => exact D'.zero_mem
    | add x y _ _ hx hy => exact D'.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def]
      exact D'.mul_mem (hφD (algebraMap A₁ B₁ a)) hx
  have hgen : ∀ c ∈ G₀, c ⊗ₜ[B₀] (1 : D') ∈ F.range := by
    intro c hc
    obtain ⟨z, hz⟩ := hN (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨c, hc, rfl⟩))
    let ν : N →ₗ[A₁] D' :=
      { toFun := fun x => ⟨x.1, hND x.1 x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨LinearMap.lTensor B₁ ν z, ?_⟩
    apply hMinj
    rw [hcompat, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have hιν : ι ∘ₗ ν = N.subtype := rfl
    rw [hιν, hz, hw]
    change c ⊗ₜ[B₀] (1 : B') = (AlgHom.id B₀ C₀ c) ⊗ₜ D'.val 1
    rw [map_one]
    rfl
  have hleft : ∀ c : C₀, c ⊗ₜ[B₀] (1 : D') ∈ F.range := by
    let S : Subalgebra B₀ C₀ :=
      { (F.range.comap Algebra.TensorProduct.includeLeftRingHom) with
        algebraMap_mem' := fun b => by
          change (algebraMap B₀ C₀ b) ⊗ₜ[B₀] (1 : D') ∈ F.range
          rw [algebraMap_tmul_one]
          exact hincR _ }
    have hle : (⊤ : Subalgebra B₀ C₀) ≤ S := by
      rw [← hG₀, Algebra.adjoin_le_iff]
      intro c hc
      exact hgen c hc
    intro c
    exact hle Algebra.mem_top
  have hFsurj : ∀ x, x ∈ F.range := by
    intro x
    induction x with
    | tmul c d =>
      have hcd : c ⊗ₜ[B₀] d = (c ⊗ₜ[B₀] (1 : D')) * ((1 : C₀) ⊗ₜ[B₀] d) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hcd]
      exact F.range.mul_mem (hleft c) (hincR d)
    | add x y hx hy => exact F.range.add_mem hx hy
  exact ⟨F, hF, hFinj, fun x => hFsurj x⟩

end RingEtaleGroupoid

end Langlands.AlgebraicGeometry
