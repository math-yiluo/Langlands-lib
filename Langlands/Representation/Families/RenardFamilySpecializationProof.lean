import Langlands.Representation.Families.RenardFamilyFixedTensorProof
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! # Admissibility under specialization of coefficient families -/

noncomputable section

open TensorProduct

namespace Langlands.Renard.AlgebraicFamily

universe uB uA uG uV

section BaseChange

variable {B : Type uB} [CommRing B]
  {A : Type uA} [CommRing A] [Algebra B A]
  {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module B V]

omit [TopologicalSpace G] in
private theorem baseChange_action (ρ : Representation B G V) (g : G) (t : A ⊗[B] V) :
    ((Module.End.baseChangeHom B A V).toMonoidHom.comp ρ) g t =
      ((Representation.trivial B G A).tprod ρ) g t := by
  induction t using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Scalar extension preserves smoothness of the original action. -/
theorem baseChange_isSmooth (ρ : Representation B G V) (hρ : IsSmooth ρ) :
    IsSmooth ((Module.End.baseChangeHom B A V).toMonoidHom.comp ρ) := by
  intro t
  obtain ⟨K, ht⟩ := trivialTensor_isSmooth (E := A) ρ hρ t
  refine ⟨K, fun g => ?_⟩
  change ((Module.End.baseChangeHom B A V).toMonoidHom.comp ρ) g.val t = t
  rw [baseChange_action]
  exact ht g

variable [Algebra ℂ B] [IsTopologicalGroup G]

/-- Finite compact-open fixed modules remain finite after scalar extension. -/
theorem baseChange_fixed_finite (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [Module.Finite B (fixedVectors ρ K.toSubgroup)] :
    Module.Finite A
      (fixedVectors ((Module.End.baseChangeHom B A V).toMonoidHom.comp ρ) K.toSubgroup) := by
  let τ := (Module.End.baseChangeHom B A V).toMonoidHom.comp ρ
  let N := fixedVectors ρ K.toSubgroup
  let f : A ⊗[B] N →ₗ[A] fixedVectors τ K.toSubgroup :=
    (N.subtype.baseChange A).codRestrict _ (by
      intro t g
      induction t using TensorProduct.inductionOn with
      | tmul a v =>
        change a ⊗ₜ[B] ρ g.val v.val = a ⊗ₜ[B] v.val
        exact congrArg (fun w : V => a ⊗ₜ[B] w) (v.property g)
      | add t s ht hs => simp only [map_add, ht, hs])
  apply Module.Finite.of_surjective f
  intro t
  have ht : t.val ∈ fixedVectors ((Representation.trivial B G A).tprod ρ) K.toSubgroup := by
    intro g
    change ((Representation.trivial B G A).tprod ρ) g.val t.val = t.val
    rw [← baseChange_action]
    exact t.property g
  rw [← (fixedTensorComparison_of_smooth (E := A) ρ hρ K hK).2] at ht
  obtain ⟨s, hs⟩ := ht
  exact ⟨s, Subtype.ext hs⟩

end BaseChange

/-- Renard VI.8.1 specialization Lemma at all three published universes. -/
theorem specializationAdmissibility : SpecializationAdmissibilityStatement.{uB, uG, uV} := by
  intro B _ _ _ _ _ G _ _ _ hG V _ _ ρ hρ _ hfinite χ
  let : Algebra B ℂ := χ.toRingHom.toAlgebra
  let τ := (Module.End.baseChangeHom B ℂ V).toMonoidHom.comp ρ
  refine ⟨baseChange_isSmooth ρ hρ, ?_⟩
  intro H
  obtain ⟨K, hK, hKH⟩ := (Topology.LocallyProfiniteProof.vanDantzig G).mp hG |>.2
    (H : Set G) H.mem_nhds_one
  let := hfinite K hK
  let : Module.Finite ℂ (fixedVectors τ K.toSubgroup) := baseChange_fixed_finite ρ hρ K hK
  apply Submodule.finiteDimensional_of_le (S₂ := fixedVectors τ K.toSubgroup)
  intro t ht g
  exact ht ⟨g.val, hKH g.property⟩

end Langlands.Renard.AlgebraicFamily
