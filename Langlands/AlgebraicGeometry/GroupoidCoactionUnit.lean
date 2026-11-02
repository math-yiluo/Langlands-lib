import Langlands.AlgebraicGeometry.GroupoidCoactionInduced
import Langlands.AlgebraicGeometry.GroupoidCoactionAcyclic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # The invariant unit for arbitrary modules -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable (hE : RingEtaleEquivalenceRelation t)
variable (hacyclic : ∀ (K : Type (max u v)) [AddCommGroup K] [Module B K]
  (θK : GroupoidCoaction t K), θK.IsAcyclic)
variable (N : Type (max u v)) [AddCommGroup N] [Module (invariantRing t) N]

include hE hacyclic in
/-- A free cover and exactness on invariant surjections give surjectivity of every unit. -/
lemma inducedUnit_surjective_of_acyclic :
    Function.Surjective (inducedUnit t N) := by
  let F := N →₀ invariantRing t
  let p : F →ₗ[invariantRing t] N := Finsupp.linearCombination (invariantRing t) id
  have hp : Function.Surjective p := Finsupp.linearCombination_id_surjective _ _
  have hpinv := invariantsMap_surjective hE hacyclic
    (induced t F) (induced t N) (p.baseChange B)
    (induced_isHom_baseChange t p) (LinearMap.baseChange_surjective B hp)
  intro x
  obtain ⟨y, hy⟩ := hpinv x
  obtain ⟨z, hz⟩ := (inducedUnit_bijective t (N := F)).2 y
  refine ⟨p z, ?_⟩
  have hn := LinearMap.congr_fun (inducedUnit_natural t p) z
  simpa only [LinearMap.comp_apply, hz, hy] using hn.symm

include hE hacyclic in
/-- A free presentation and exactness of invariants give injectivity of the unit. -/
lemma inducedUnit_injective_of_free_cover
    (F : Type (max u v)) [AddCommGroup F] [Module (invariantRing t) F]
    [Module.Free (invariantRing t) F]
    (p : F →ₗ[invariantRing t] N) (hp : Function.Surjective p) :
    Function.Injective (inducedUnit t N) := by
  let i : LinearMap.ker p →ₗ[invariantRing t] F := (LinearMap.ker p).subtype
  have hseq : Function.Exact i p := LinearMap.exact_subtype_ker_map p
  have hext : Function.Exact (i.baseChange B) (p.baseChange B) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      lTensor_exact (R := invariantRing t) (f := i) (g := p) B hseq hp
  have hinv := invariantsMap_exact_of_acyclic hE hacyclic
    (induced t (LinearMap.ker p)) (induced t F) (induced t N)
    (i.baseChange B) (p.baseChange B)
    (induced_isHom_baseChange t i) (induced_isHom_baseChange t p)
    hext.linearMap_ker_eq.symm
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro n hn
  obtain ⟨z, hz⟩ := hp n
  have hmem : inducedUnit t F z ∈ LinearMap.range
      ((induced t (LinearMap.ker p)).invariantsMap (induced t F) (i.baseChange B)
        (induced_isHom_baseChange t i)) := by
    rw [hinv]
    have hnat := LinearMap.congr_fun (inducedUnit_natural t p) z
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, hz, hn] using hnat
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
  obtain ⟨k, hk⟩ := inducedUnit_surjective_of_acyclic hE hacyclic (LinearMap.ker p) y
  have hnat := LinearMap.congr_fun (inducedUnit_natural t i) k
  have hunit : inducedUnit t F (i k) = inducedUnit t F z := by
    simpa only [LinearMap.comp_apply, hk, hy] using hnat.symm
  have hik : i k = z := (inducedUnit_bijective t (N := F)).1 hunit
  calc
    n = p z := hz.symm
    _ = p (i k) := congrArg p hik.symm
    _ = 0 := k.property

include hE hacyclic in
/-- Exactness of invariants and tensor right exactness give injectivity of every unit. -/
lemma inducedUnit_injective_of_acyclic :
    Function.Injective (inducedUnit t N) :=
  inducedUnit_injective_of_free_cover hE hacyclic N (N →₀ invariantRing t)
    (Finsupp.linearCombination (invariantRing t) id)
    (Finsupp.linearCombination_id_surjective _ _)

include hE hacyclic in
/-- Every invariant-ring module is recovered as the invariants of its scalar extension. -/
lemma inducedUnit_bijective_of_acyclic :
    Function.Bijective (inducedUnit t N) :=
  ⟨inducedUnit_injective_of_acyclic hE hacyclic N,
    inducedUnit_surjective_of_acyclic hE hacyclic N⟩

/-- The invariant-unit isomorphism under all-module acyclicity. -/
noncomputable def inducedUnitLinearEquiv :
    N ≃ₗ[invariantRing t] (induced t N).invariantSubmodule :=
  LinearEquiv.ofBijective (inducedUnit t N) (inducedUnit_bijective_of_acyclic hE hacyclic N)

@[simp]
lemma inducedUnitLinearEquiv_apply (n : N) :
    inducedUnitLinearEquiv hE hacyclic N n = inducedUnit t N n :=
  rfl

end Langlands.AlgebraicGeometry.GroupoidCoaction
