import Langlands.Representation.CommutingFamilyUniqueness
import Langlands.Representation.Classification.LeftCuspidalDerivative.Criterion
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Faithful tensor evaluation from parabolic covariance -/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false

universe uG uL uA uV uI uS

namespace Langlands.InducedSliceEvaluation

open Classification.LeftCuspidalDerivative (exists_dual_lid_rTensor_ne_zero)

variable {G : Type uG} {L : Type uL} [Monoid L]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {I : Type uI} [AddCommGroup I] [Module ℂ I]
variable {S : Type uS} [AddCommGroup S] [Module ℂ S]

/-- Pair vectors with a linear family of maps out of the coefficient space. -/
def pair (j : I →ₗ[ℂ] V →ₗ[ℂ] S) : V ⊗[ℂ] I →ₗ[ℂ] S :=
  TensorProduct.lift j.flip

@[simp]
theorem pair_tmul (j : I →ₗ[ℂ] V →ₗ[ℂ] S) (v : V) (i : I) :
    pair j (v ⊗ₜ[ℂ] i) = j i v := rfl

variable (e : G → A →ₗ[ℂ] V)

/-- At each finite argument, apply the inducing evaluation and then pair it
with the infinite coefficient map. -/
def slices (j : I →ₗ[ℂ] V →ₗ[ℂ] S) : A ⊗[ℂ] I →ₗ[ℂ] (G → S) :=
  LinearMap.pi fun g => (pair j).comp ((e g).rTensor I)

@[simp]
theorem slices_tmul (j : I →ₗ[ℂ] V →ₗ[ℂ] S) (a : A) (i : I) (g : G) :
    slices e j (a ⊗ₜ[ℂ] i) g = j i (e g a) := rfl

private theorem eq_zero_of_rTensor_evaluations
    (he : ∀ a : A, (∀ g, e g a = 0) → a = 0) (t : A ⊗[ℂ] I)
    (ht : ∀ g, (e g).rTensor I t = 0) : t = 0 := by
  let b := Module.Basis.ofVectorSpace ℂ I
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  rw [map_zero]
  ext i
  apply he
  intro g
  have h : e g ((TensorProduct.equivFinsuppOfBasisRight b) t i) =
      (TensorProduct.equivFinsuppOfBasisRight b) ((e g).rTensor I t) i := by
    clear ht
    induction t using TensorProduct.inductionOn with
    | tmul a v => simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        LinearMap.rTensor_tmul, map_smul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  rw [h, ht g, map_zero, Finsupp.zero_apply]

variable (ρ : Representation ℂ L V) [ρ.IsIrreducible]
variable (shift : L → G → G) (χ : L → ℂ)
variable (hχ : ∀ p, χ p ≠ 0)
variable (hcov : ∀ p g, e (shift p g) = χ p • (ρ p).comp (e g))

include hχ hcov in
/-- A nonzero inducing evaluation has coefficient values spanning the
irreducible Levi representation. -/
theorem span_values_eq_top (hn : ∃ g a, e g a ≠ 0) :
    Submodule.span ℂ (Set.range fun q : G × A => e q.1 q.2) = ⊤ := by
  let P : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range fun q : G × A => e q.1 q.2)
      apply_mem_toSubmodule := by
        intro p v hv
        induction hv using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨⟨g, a⟩, rfl⟩ := hv
          have h := LinearMap.congr_fun (hcov p g) a
          change e (shift p g) a = χ p • ρ p (e g a) at h
          rw [← inv_smul_smul₀ (hχ p) (ρ p (e g a)), ← h]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(shift p g, a), rfl⟩)
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx }
  obtain ⟨g, a, h⟩ := hn
  have hP : P ≠ ⊥ := fun hz => h (show e g a ∈ (⊥ : Submodule ℂ V) from by
    have hs : e g a ∈ P.toSubmodule := Submodule.subset_span ⟨(g, a), rfl⟩
    rw [hz] at hs
    exact hs)
  exact congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top P).resolve_left hP)

private theorem eq_zero_of_levi_tests (j : I →ₗ[ℂ] V →ₗ[ℂ] S)
    (hj : Function.Injective j) (hS : ∀ f : ρ.IntertwiningMap ρ,
      ∃ c : ℂ, f = c • Representation.IntertwiningMap.id ρ)
    (t : V ⊗[ℂ] I) (ht : ∀ p, pair j ((ρ p).rTensor I t) = 0) : t = 0 := by
  by_contra hn
  obtain ⟨φ, hφ⟩ := exists_dual_lid_rTensor_ne_zero hn
  let i := TensorProduct.lid ℂ I (φ.rTensor I t)
  have hji : j i ≠ 0 := fun h => hφ (hj (h.trans (map_zero j).symm))
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hji
  let f := φ.smulRight v
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
  have htest (r : MonoidAlgebra ℂ L) : pair j ((ρ.asAlgebraHom r).rTensor I t) = 0 := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp only [map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]
    | add r₁ r₂ h₁ h₂ => simp only [map_add, LinearMap.rTensor_add, LinearMap.add_apply,
        h₁, h₂, add_zero]
    | single p z => simp only [Representation.asAlgebraHom_single, LinearMap.rTensor_smul,
        LinearMap.smul_apply, map_smul, ht, smul_zero]
  obtain ⟨r, hr⟩ := CommutingFamily.exists_asAlgebraHom_eq_on ρ hS f (s.image Prod.fst)
  have hmatch : (ρ.asAlgebraHom r).rTensor I t = f.rTensor I t := by
    rw [hs]
    simp only [map_sum, LinearMap.rTensor_tmul]
    exact Finset.sum_congr rfl fun x hx =>
      congrArg (fun y => y ⊗ₜ[ℂ] x.2) (hr x.1 (Finset.mem_image_of_mem _ hx))
  apply hv
  have hrank (t' : V ⊗[ℂ] I) : pair j (f.rTensor I t') =
      j (TensorProduct.lid ℂ I (φ.rTensor I t')) v := by
    induction t' using TensorProduct.inductionOn with
    | tmul x y => simp only [f, LinearMap.rTensor_tmul, LinearMap.smulRight_apply,
        pair_tmul, map_smul, LinearMap.smul_apply, TensorProduct.lid_tmul]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  exact (hrank t).symm.trans (hmatch ▸ htest r)

include hχ hcov in
/-- Jointly faithful finite evaluations and irreducible Levi covariance make
pairing with the infinite coefficients injective on the tensor product. -/
theorem slices_injective (j : I →ₗ[ℂ] V →ₗ[ℂ] S)
    (hj : Function.Injective j) (he : ∀ a : A, (∀ g, e g a = 0) → a = 0)
    (hS : ∀ f : ρ.IntertwiningMap ρ, ∃ c : ℂ, f = c • Representation.IntertwiningMap.id ρ) :
    Function.Injective (slices e j) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  apply eq_zero_of_rTensor_evaluations e he t
  intro g
  apply eq_zero_of_levi_tests ρ j hj hS
  intro p
  have hz := congrFun ht (shift p g)
  change pair j ((e (shift p g)).rTensor I t) = 0 at hz
  rw [hcov, LinearMap.rTensor_smul, LinearMap.smul_apply, map_smul,
    LinearMap.rTensor_comp, LinearMap.comp_apply] at hz
  exact (smul_eq_zero.mp hz).resolve_left (hχ p)

end Langlands.InducedSliceEvaluation
