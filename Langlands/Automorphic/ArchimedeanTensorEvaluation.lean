import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement
import Langlands.Representation.Archimedean.GKModuleDensity
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Tensor evaluation of compact and Lie intertwiners -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.GKTensorEvaluation

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe uK uL uV uW

variable {K : Type uK} [Group K]
  {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
  (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W)

/-- All linear maps intertwining both the compact and the Lie actions. -/
abbrev Multiplicity := gkHoms ρ π ρ' π'

local instance gkTensorMultiplicityGroup : AddCommGroup (Multiplicity ρ π ρ' π') :=
  (gkHoms ρ π ρ' π').addCommGroup

/-- Evaluation of a simultaneous compact and Lie intertwiner at one vector. -/
def evalAt (v : V) : Multiplicity ρ π ρ' π' →ₗ[ℂ] W :=
  (gkHoms ρ π ρ' π').subtype.flip v

@[simp]
theorem evalAt_apply (v : V) (f : Multiplicity ρ π ρ' π') :
    evalAt ρ π ρ' π' v f = f.val v := rfl

/-- Tensor evaluation retains every simultaneous compact and Lie multiplicity. -/
def evaluation : V ⊗[ℂ] Multiplicity ρ π ρ' π' →ₗ[ℂ] W :=
  TensorProduct.lift (gkHoms ρ π ρ' π').subtype.flip

@[simp]
theorem evaluation_tmul (v : V) (f : Multiplicity ρ π ρ' π') :
    evaluation ρ π ρ' π' (v ⊗ₜ[ℂ] f) = f.val v := rfl

theorem evaluation_compact (k : K) (t : V ⊗[ℂ] Multiplicity ρ π ρ' π') :
    evaluation ρ π ρ' π' (TensorProduct.map (ρ k) LinearMap.id t) =
      ρ' k (evaluation ρ π ρ' π' t) := by
  induction t with
  | tmul v f => exact f.property.1 k v
  | add t t' ht ht' => simp only [map_add, ht, ht']

theorem evaluation_lie (X : L) (t : V ⊗[ℂ] Multiplicity ρ π ρ' π') :
    evaluation ρ π ρ' π' (TensorProduct.map (π X) LinearMap.id t) =
      π' X (evaluation ρ π ρ' π' t) := by
  induction t with
  | tmul v f => exact f.property.2 X v
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- Simultaneous intertwiners commute with every noncommutative generator polynomial. -/
theorem intertwines_freeAlgebra (f : Multiplicity ρ π ρ' π')
    (a : FreeAlgebra ℂ (K ⊕ L)) (v : V) :
    f.val (FreeAlgebra.lift ℂ (GKModuleDensity.gens ρ π) a v) =
      FreeAlgebra.lift ℂ (GKModuleDensity.gens ρ' π') a (f.val v) := by
  induction a using FreeAlgebra.induction generalizing v with
  | grade0 c =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | grade1 g =>
    simp only [FreeAlgebra.lift_ι_apply]
    cases g with
    | inl k => exact f.property.1 k v
    | inr X => exact f.property.2 X v
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Irreducibility makes evaluation at a nonzero vector injective on all multiplicities. -/
theorem evalAt_injective (h : IsIrreducibleGKModule ρ π) {v : V} (hv : v ≠ 0) :
    Function.Injective (evalAt ρ π ρ' π' v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hk : ∀ k x, x ∈ LinearMap.ker f.val → ρ k x ∈ LinearMap.ker f.val := by
    intro k x hx
    change f.val (ρ k x) = 0
    rw [f.property.1 k x, LinearMap.mem_ker.mp hx, map_zero]
  have hl : ∀ X x, x ∈ LinearMap.ker f.val → π X x ∈ LinearMap.ker f.val := by
    intro X x hx
    change f.val (π X x) = 0
    rw [f.property.2 X x, LinearMap.mem_ker.mp hx, map_zero]
  rcases h.2 (LinearMap.ker f.val) hk hl with hbot | htop
  · have hmem : v ∈ LinearMap.ker f.val := hf
    rw [hbot, Submodule.mem_bot] at hmem
    exact (hv hmem).elim
  · apply Subtype.ext
    apply LinearMap.ext
    intro x
    have hmem : x ∈ LinearMap.ker f.val := htop ▸ Submodule.mem_top
    exact LinearMap.mem_ker.mp hmem

variable [TopologicalSpace K]

/-- Jacobson density makes simultaneous tensor evaluation injective. -/
theorem evaluation_injective (h : GKModuleDensity.Hyp ρ π) :
    Function.Injective (evaluation ρ π ρ' π') := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ V
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hc : ∀ j v, (c j).val v = 0 := by
    intro j v
    obtain ⟨a, ha⟩ := GKModuleDensity.exists_freeAlgebra_eq h (c.support.image b)
      ((b.coord j).smulRight v)
    have hterm : ∀ i ∈ c.support,
        FreeAlgebra.lift ℂ (GKModuleDensity.gens ρ' π') a
            (evaluation ρ π ρ' π' (b i ⊗ₜ[ℂ] c i)) =
          b.coord j (b i) • (c i).val v := by
      intro i hi
      rw [evaluation_tmul, ← intertwines_freeAlgebra,
        ha (b i) (Finset.mem_image_of_mem b hi), LinearMap.smulRight_apply, map_smul]
    have h1 := congrArg (FreeAlgebra.lift ℂ (GKModuleDensity.gens ρ' π') a) ht
    simp only [map_finsuppSum, map_zero] at h1
    rw [Finsupp.sum, Finset.sum_congr rfl hterm, Finset.sum_eq_single j] at h1
    · simpa using h1
    · intro i _ hij
      simp [hij]
    · intro hj
      simp [Finsupp.notMem_support_iff.mp hj]
  have hc0 : c = 0 := Finsupp.ext fun j => Subtype.ext (LinearMap.ext fun v => hc j v)
  simp [hc0]

end Langlands.Archimedean.GKTensorEvaluation
