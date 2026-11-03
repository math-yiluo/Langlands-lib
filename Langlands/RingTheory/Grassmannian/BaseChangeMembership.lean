import Langlands.RingTheory.Grassmannian.PrincipalDescent
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Finiteness.Projective

/-! # Membership in base changes of points of quotient Grassmannians

For a point `N` of the quotient Grassmannian `G(k, A ⊗[R] M; A)` and an `R`-algebra map
`φ : A → B`, the base-changed point `map φ N` is the `B`-span of the image of `N`, and the locus
of `φ` where given base-changed vectors lie in `map φ N` is cut out by an ideal of `A`.
-/

universe u

open scoped TensorProduct
open TensorProduct

namespace Langlands.Grassmannian

open Module.Grassmannian Module.Grassmannian.PrincipalDescent

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

section Tower

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B]

theorem cancelBaseChange_tmul_eq_smul_l (b : B) (n : A ⊗[R] M) :
    AlgebraTensorModule.cancelBaseChange R A B B M (b ⊗ₜ[A] n) = b • l R M A B n := by
  induction n using TensorProduct.inductionOn with
  | tmul a m =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul, l_tmul, smul_tmul', smul_eq_mul,
      Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [tmul_add, map_add, hx, hy, map_add, smul_add]

/-- Right exactness of base change: the kernel of `B ⊗[R] M → B ⊗[A] ((A ⊗[R] M) ⧸ N)` is the
`B`-span of the image of `N`. -/
theorem ker_baseChangeMkQ_eq_span (N : Submodule A (A ⊗[R] M)) :
    LinearMap.ker (baseChangeMkQ B N) = Submodule.span B (l R M A B '' N) := by
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 ?_)
  · have hx' : (AlgebraTensorModule.cancelBaseChange R A B B M).symm x ∈
        LinearMap.ker (LinearMap.lTensor B N.mkQ) := by
      rw [LinearMap.mem_ker, ← LinearMap.baseChange_eq_ltensor]
      exact hx
    rw [lTensor_mkQ] at hx'
    obtain ⟨z, hz⟩ := hx'
    have hxz : x = AlgebraTensorModule.cancelBaseChange R A B B M
        (LinearMap.lTensor B N.subtype z) := by
      rw [hz, LinearEquiv.apply_symm_apply]
    rw [hxz]
    clear hz hxz
    induction z using TensorProduct.inductionOn with
    | tmul b n =>
      rw [LinearMap.lTensor_tmul, cancelBaseChange_tmul_eq_smul_l]
      exact Submodule.smul_mem _ b (Submodule.subset_span ⟨n, n.2, rfl⟩)
    | add y z hy hz =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hy hz
  · rintro _ ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, baseChangeMkQ_l, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).2 hn, tmul_zero]

end Tower

section Split

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- An element `q` of a module with a split embedding `g` into `A^m` becomes zero in
`B ⊗[A] Q` exactly when the coordinates of `g q` vanish in `B`. -/
theorem one_tmul_eq_zero_iff_of_comp_eq_id {Q : Type u} [AddCommGroup Q] [Module A Q] {m : ℕ}
    (f : (Fin m → A) →ₗ[A] Q) (g : Q →ₗ[A] Fin m → A) (hfg : f ∘ₗ g = LinearMap.id) (q : Q) :
    (1 : B) ⊗ₜ[A] q = 0 ↔ ∀ i, algebraMap A B (g q i) = 0 := by
  have key : piScalarRight A B B (Fin m) ((1 : B) ⊗ₜ[A] g q) =
      fun i => algebraMap A B (g q i) := by
    ext i
    simp [Algebra.smul_def]
  constructor
  · intro h i
    have h0 : (1 : B) ⊗ₜ[A] g q = 0 := by
      rw [← LinearMap.lTensor_tmul, h, map_zero]
    rw [h0, map_zero] at key
    exact (congrFun key i).symm
  · intro h
    have h0 : (1 : B) ⊗ₜ[A] g q = 0 := by
      apply (piScalarRight A B B (Fin m)).injective
      rw [key, map_zero]
      ext i
      exact h i
    have hq : q = f (g q) := (LinearMap.congr_fun hfg q).symm
    rw [hq, ← LinearMap.lTensor_tmul, h0, map_zero]

end Split

section Map

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem l_eq_rTensor (φ : A →ₐ[R] B) (x : A ⊗[R] M) :
    letI : Algebra A B := φ.toAlgebra
    letI : IsScalarTower R A B :=
      IsScalarTower.of_algebraMap_eq' <| (φ.comp_algebraMap).symm
    l R M A B x = φ.toLinearMap.rTensor M x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [l, RingHom.algebraMap_toAlgebra]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The base change of a point of the quotient Grassmannian is the span of the image of the
point. -/
theorem map_toSubmodule_eq_span {k : ℕ} (φ : A →ₐ[R] B) (N : Module.Grassmannian A (A ⊗[R] M) k) :
    (Module.Grassmannian.map φ N).toSubmodule =
      Submodule.span B (φ.toLinearMap.rTensor M '' N.toSubmodule) := by
  let _ : Algebra A B := φ.toAlgebra
  have _ : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' <| (φ.comp_algebraMap).symm
  rw [map_toSubmodule' R M φ (fun _ => rfl) N, ker_baseChangeMkQ_eq_span]
  congr 1

/-- For a point `N` of the quotient Grassmannian and a family `v` of vectors, the condition that
all base-changed vectors lie in the base-changed point is cut out by an ideal of `A`. -/
theorem exists_ideal_forall_rTensor_mem_map_iff {k : ℕ}
    (N : Module.Grassmannian A (A ⊗[R] M) k) {τ : Type u} (v : τ → A ⊗[R] M) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type u) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
      (∀ t, φ.toLinearMap.rTensor M (v t) ∈ (Module.Grassmannian.map φ N).toSubmodule) ↔
        ∀ a ∈ 𝔞, φ a = 0 := by
  obtain ⟨m, f, g, -, -, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective A ((A ⊗[R] M) ⧸ N.toSubmodule)
  refine ⟨Ideal.span (Set.range fun p : τ × Fin m => g (N.toSubmodule.mkQ (v p.1)) p.2),
    fun B _ _ φ => ?_⟩
  let _ : Algebra A B := φ.toAlgebra
  have _ : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' <| (φ.comp_algebraMap).symm
  have hmem : ∀ t, φ.toLinearMap.rTensor M (v t) ∈ (Module.Grassmannian.map φ N).toSubmodule ↔
      ∀ i, φ (g (N.toSubmodule.mkQ (v t)) i) = 0 := by
    intro t
    rw [map_toSubmodule' R M φ (fun _ => rfl) N, LinearMap.mem_ker, ← l_eq_rTensor,
      baseChangeMkQ_l]
    exact one_tmul_eq_zero_iff_of_comp_eq_id B f g hfg _
  simp only [hmem]
  constructor
  · intro h a ha
    have hle : Ideal.span (Set.range fun p : τ × Fin m => g (N.toSubmodule.mkQ (v p.1)) p.2) ≤
        RingHom.ker φ.toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      exact h p.1 p.2
    exact hle ha
  · intro h t i
    exact h _ (Ideal.subset_span ⟨(t, i), rfl⟩)

end Map

end Langlands.Grassmannian
