import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units

/-! # Complex characters through open finite quotients -/

noncomputable section

universe u v

namespace Langlands.Topology

/-- Extend a complex character through an open finite quotient. The prescribed
character need only be trivial on the preimage of the open subgroup. -/
theorem exists_character_of_open_finite_quotient
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    {C : Type v} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (f : A →ₜ* C) (η : A →ₜ* ℂˣ) (N : Subgroup C)
    (hN : IsOpen (N : Set C)) [N.FiniteIndex]
    (m : ℕ) (hpow : ∀ x : C, x ^ m ∈ N)
    (hker : N.comap f.toMonoidHom ≤ η.toMonoidHom.ker) :
    ∃ χ : C →ₜ* ℂˣ, χ ^ m = 1 ∧ χ.comp f = η := by
  classical
  let : DiscreteTopology (C ⧸ N) := QuotientGroup.discreteTopology hN
  let g : A →* C ⧸ N := (QuotientGroup.mk' N).comp f.toMonoidHom
  have hg : g.rangeRestrict.ker ≤ η.toMonoidHom.ker := by
    intro a ha
    apply hker
    change f a ∈ N
    apply (QuotientGroup.eq_one_iff (f a)).mp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
  let ψ : g.range →* ℂˣ :=
    g.rangeRestrict.liftOfSurjective g.rangeRestrict_surjective ⟨η.toMonoidHom, hg⟩
  have hψ (a : A) : ψ (g.rangeRestrict a) = η a := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  obtain ⟨ρ, hρ⟩ := MonoidHom.domRestrict_surjective (M := ℂ) g.range ψ
  let χ : C →ₜ* ℂˣ :=
    { toMonoidHom := ρ.comp (QuotientGroup.mk' N)
      continuous_toFun :=
        (show Continuous ρ from continuous_of_discreteTopology).comp
          QuotientGroup.continuous_mk }
  refine ⟨χ, ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro x
    rw [ContinuousMonoidHom.pow_apply]
    change ρ (QuotientGroup.mk x : C ⧸ N) ^ m = 1
    rw [← map_pow, ← QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff (x ^ m)).mpr (hpow x), map_one]
  · apply ContinuousMonoidHom.ext
    intro a
    change ρ (g a) = η a
    have h := congrArg (fun τ : g.range →* ℂˣ => τ (g.rangeRestrict a)) hρ
    exact h.trans (hψ a)

end Langlands.Topology
