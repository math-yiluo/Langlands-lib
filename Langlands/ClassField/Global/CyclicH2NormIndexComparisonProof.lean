import Langlands.ClassField.Global.CyclicH2NormIndexComparisonStatement
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # Cyclic idele-class H² and the actual norm index -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField CategoryTheory
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

/-- Actual idele-class descent and the Galois-product formula for the actual
norm imply the cyclic degree-two cohomology norm-index comparison. -/
theorem cyclicH2NormIndexComparison : CyclicH2NormIndexComparison.{u, v} := by
  intro hA hC F _ _ E _ _ _ _ _
  classical
  let _ : CommGroup (E ≃ₐ[F] E) := IsCyclic.commGroup
  let _ : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite (E ≃ₐ[F] E)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  let A := relativeIdeleClassRepresentation F E
  let π := Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 even_two
  have hker : ∀ a : A, a ∈ LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap ↔
      A.ρ g a = a := fun a => by simp [Rep.sub_hom, sub_eq_zero]
  have hmem : ∀ x : IdeleClassGroup (𝓞 F) F,
      (Additive.ofMul (ideleClassInclusion (K := F) (L := E) x) :
          Additive (IdeleClassGroup (𝓞 E) E)) ∈
        LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap := by
    intro x
    exact (hker (Additive.ofMul (ideleClassInclusion (K := F) (L := E) x))).2
      (congrArg Additive.ofMul (((hA F E).2 (ideleClassInclusion x)).2 ⟨x, rfl⟩ g))
  let ψ : IdeleClassGroup (𝓞 F) F →*
      Multiplicative (relativeIdeleClassCohomology F E 2 : Type v) :=
    { toFun x := Multiplicative.ofAdd (π.hom ⟨_, hmem x⟩)
      map_one' := by
        rw [← ofAdd_zero, ← map_zero π.hom]
        congr 2
        ext
        exact congrArg Additive.ofMul (map_one ideleClassInclusion)
      map_mul' x y := by
        rw [← ofAdd_add, ← map_add]
        congr 2
        ext
        exact congrArg Additive.ofMul (map_mul ideleClassInclusion x y) }
  have hπ : Function.Surjective π.hom := by
    have h1 : Epi (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatCyclesIso.inv :=
      inferInstance
    have : Epi π := epi_comp' h1 (epi_comp' inferInstance (IsIso.epi_of_iso _))
    exact (ModuleCat.epi_iff_surjective π).1 this
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨z, hz⟩ := hπ (Multiplicative.toAdd y)
    have hfix : A.ρ g z.1 = z.1 := (hker z.1).1 z.2
    have hinv := (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg z.1).2 hfix
    obtain ⟨x, hx⟩ := ((hA F E).2 (Additive.toMul z.1)).1
      (fun σ => congrArg Additive.toMul (hinv σ))
    refine ⟨x, ?_⟩
    change Multiplicative.ofAdd (π.hom ⟨_, hmem x⟩) = y
    have hz' : (⟨_, hmem x⟩ : LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap) = z :=
      Subtype.ext (congrArg Additive.ofMul hx)
    rw [hz', hz]
    rfl
  have hle : (ideleClassNorm (K := F) (L := E)).toMonoidHom.range ≤ ψ.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (π.hom ⟨_, hmem _⟩) = Multiplicative.ofAdd 0
    congr 1
    rw [Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff]
    refine ⟨Additive.ofMul y, ?_⟩
    change A.ρ.norm (Additive.ofMul y) = _
    have hsum : ∀ a : A, A.ρ.norm a = ∑ σ, A.ρ σ a := fun a => by
      rw [Representation.norm, LinearMap.sum_apply]
    refine (hsum _).trans ?_
    change ∑ σ : E ≃ₐ[F] E, Additive.ofMul (relativeIdeleClassAut F E σ y) = _
    rw [← ofMul_prod, ← hC F E y]
    rfl
  have h := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hψ, Subgroup.card_top] at h
  exact h

end Langlands.ClassField.Global
