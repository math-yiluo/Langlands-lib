import Langlands.Representation.Plancherel.CoefficientTensors
import Langlands.Representation.Smooth.Schur.Proof

/-! # Injectivity of the coefficient tensor map of an irreducible admissible representation -/

noncomputable section

universe uG uV

open scoped TensorProduct

namespace Langlands.Plancherel

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [IsTopologicalGroup G] in
/-- Jacobson density for an admissible irreducible complex representation: on any
finite set of vectors, every complex linear endomorphism agrees with the action
of one element of the group algebra. -/
theorem exists_asAlgebraHom_eq (ρ : Representation ℂ G V) (ha : IsAdmissible ρ)
    (hi : ρ.IsIrreducible) (f : V →ₗ[ℂ] V) (s : Finset V) :
    ∃ r : MonoidAlgebra ℂ G, ∀ m ∈ s, ρ.asAlgebraHom r m = f m := by
  have : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hi
  have hcomm : ∀ (φ : Module.End (MonoidAlgebra ℂ G) ρ.asModule) (m : V),
      f (φ m) = φ (f m) := by
    intro φ m
    have hgv : ∀ (g : G) (x : V), ρ g x =
        ρ.asModuleEquiv (MonoidAlgebra.of ℂ G g • ρ.asModuleEquiv.symm x) := by
      intro g x
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
      rfl
    let T : ρ.IntertwiningMap ρ :=
      { toLinearMap := φ.restrictScalars ℂ
        isIntertwining' := fun g => by
          apply LinearMap.ext
          intro v
          change φ (ρ g v) = ρ g (φ v)
          rw [hgv g v, hgv g (φ v)]
          exact φ.map_smul _ _ }
    obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism ρ ha hi T
    have hφ : ∀ x : V, φ x = c • x := fun x => by
      have hx := congrArg (fun S : ρ.IntertwiningMap ρ => S.toLinearMap x) hc
      exact hx
    rw [hφ, hφ, map_smul]
  let F : Module.End (Module.End (MonoidAlgebra ℂ G) ρ.asModule) ρ.asModule :=
    { toFun := fun m => f m
      map_add' := fun x y => f.map_add x y
      map_smul' := fun φ m => hcomm φ m }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, fun m hm => (hr m hm).symm⟩

/-- The coefficient tensor map `v ⊗ ℓ ↦ (g ↦ ℓ(π(g)v))` of an admissible
irreducible smooth complex representation is injective. -/
theorem coefficientTensorMap_injective (A : SmoothRep.{0, uG, uV} ℂ G)
    (ha : IsAdmissible A.representation) (hi : A.representation.IsIrreducible) :
    Function.Injective (coefficientTensorMap A) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Basis.ofVectorSpace ℂ A
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hΦ : ∀ r : MonoidAlgebra ℂ G,
      ∑ i ∈ c.support, (c i).val (A.representation.asAlgebraHom r (b i)) = 0 := by
    intro r
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib, hx, hy, add_zero]
    | single g a =>
      have hg : LocallyConstant.evalₗ ℂ g
          (coefficientTensorMap A (c.sum fun i ℓ => b i ⊗ₜ[ℂ] ℓ)) = 0 := by
        rw [ht, map_zero]
      simp only [Finsupp.sum, map_sum, LocallyConstant.evalₗ_apply,
        coefficientTensorMap_tmul] at hg
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul,
        smul_eq_mul]
      rw [← Finset.mul_sum, hg, mul_zero]
  have hc : c = 0 := by
    ext j w
    simp only [Finsupp.coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero, LinearMap.zero_apply]
    by_cases hj : j ∈ c.support
    · obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq A.representation ha hi
        (b.constr ℂ (Pi.single j w)) (c.support.image b)
      have h := hΦ r
      rw [Finset.sum_eq_single j] at h
      · rw [hr (b j) (Finset.mem_image_of_mem b hj), Module.Basis.constr_basis, Pi.single_eq_same] at h
        exact h
      · intro i hi' hij
        rw [hr (b i) (Finset.mem_image_of_mem b hi'), Module.Basis.constr_basis, Pi.single_eq_of_ne hij,
          map_zero]
      · intro hj'
        exact absurd hj hj'
    · rw [Finsupp.notMem_support_iff.mp hj]
      rfl
  rw [hc, Finsupp.sum_zero_index]

end Langlands.Plancherel
