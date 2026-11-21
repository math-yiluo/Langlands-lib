import Langlands.Representation.Character.SeparationProof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Independent actions on the finite-dimensional Hecke corner -/

noncomputable section

namespace Langlands.BaseChange

variable {A : Type*} [Ring A] [Algebra ℂ A]
  {M : Type*} [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  {N : Type*} [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]

private theorem exists_scalar_of_simpleModuleEnd [FiniteDimensional ℂ M] [IsSimpleModule A M]
    (f : Module.End A M) : ∃ z : ℂ, ∀ x, f x = z • x := by
  let : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue (f.restrictScalars ℂ)
  obtain ⟨x, hx⟩ := hz.exists_hasEigenvector
  have hfx : f x = z • x := Module.End.mem_eigenspace_iff.mp hx.1
  let t : Module.End A M := f - z • LinearMap.id
  have htx : t x = 0 := sub_eq_zero.mpr hfx
  have ht : t = 0 := (LinearMap.bijective_or_eq_zero t).resolve_left (fun h =>
    hx.2 (h.injective (htx.trans (map_zero t).symm)))
  refine ⟨z, fun y => sub_eq_zero.mp ?_⟩
  exact LinearMap.congr_fun ht y

/-- On two nonisomorphic finite-dimensional simple modules, an algebra element
can prescribe an arbitrary complex-linear action on the first and zero on the second. -/
theorem exists_actions_of_nonisomorphic_simpleModules [FiniteDimensional ℂ M]
    [FiniteDimensional ℂ N] [IsSimpleModule A M] [IsSimpleModule A N]
    (hne : ¬ Nonempty (M ≃ₗ[A] N)) (T : Module.End ℂ M) :
    ∃ r : A, DistribSMul.toLinearMap ℂ M r = T ∧ DistribSMul.toLinearMap ℂ N r = 0 := by
  have hMN : ∀ f : M →ₗ[A] N, f = 0 := fun f =>
    f.bijective_or_eq_zero.resolve_left fun hf => hne ⟨LinearEquiv.ofBijective f hf⟩
  have hNM : ∀ f : N →ₗ[A] M, f = 0 := fun f =>
    f.bijective_or_eq_zero.resolve_left fun hf => hne ⟨(LinearEquiv.ofBijective f hf).symm⟩
  have : IsSemisimpleModule A (M × N) := by
    have hsup := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A M N))
      (IsSemisimpleModule.range (LinearMap.inr A M N))
    rw [LinearMap.sup_range_inl_inr] at hsup
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  have h1 (φ : Module.End A (M × N)) (n : N) : (φ (0, n)).1 = 0 :=
    LinearMap.congr_fun (hNM ((LinearMap.fst A M N).comp (φ.comp (LinearMap.inr A M N)))) n
  have h2 (φ : Module.End A (M × N)) (m : M) : (φ (m, 0)).2 = 0 :=
    LinearMap.congr_fun (hMN ((LinearMap.snd A M N).comp (φ.comp (LinearMap.inl A M N)))) m
  have hdiag (φ : Module.End A (M × N)) (m : M) (n : N) :
      (φ (m, n)).1 = (φ (m, 0)).1 := by
    rw [show (m, n) = (m, 0) + (0, n) by simp, map_add, Prod.fst_add, h1, add_zero]
  let op : Module.End (Module.End A (M × N)) (M × N) :=
    { toFun := fun x => (T x.1, 0)
      map_add' := fun _ _ => by simp
      map_smul' := fun φ x => by
        change (T (φ x).1, (0 : N)) = φ (T x.1, 0)
        refine Prod.ext ?_ (h2 φ _).symm
        change T (φ x).1 = (φ (T x.1, 0)).1
        let f := (LinearMap.fst A M N).comp (φ.comp (LinearMap.inl A M N))
        obtain ⟨z, hz⟩ := exists_scalar_of_simpleModuleEnd f
        rw [hdiag φ x.1 x.2]
        change T (f x.1) = f (T x.1)
        rw [hz, hz, map_smul] }
  classical
  let bM := Module.finBasis ℂ M
  let bN := Module.finBasis ℂ N
  obtain ⟨r, hr⟩ := jacobson_density op
    ((Finset.univ.image fun i => ((bM i, 0) : M × N)) ∪
      (Finset.univ.image fun j => ((0, bN j) : M × N)))
  refine ⟨r, bM.ext (fun i => ?_), bN.ext (fun j => ?_)⟩
  · have h := hr (bM i, 0) (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))
    exact (congrArg Prod.fst h).symm
  · have h := hr (0, bN j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ j)))
    exact (congrArg Prod.snd h).symm

end Langlands.BaseChange
