import Langlands.Representation.CuspidalSupport.RationalTwistStabilizerFiniteProof
import Mathlib.Topology.Algebra.Group.CompactOpen

/-! # Local isolation of actual unramified-twist coincidences -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj Topology

namespace Langlands.CuspidalSupport

universe uF uV uT

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- The actual unramified characters whose twist of `A` is isomorphic to `B`.
The character group carries its subspace compact-open topology. -/
def rationalUnramifiedTwistIsoLocus
    (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Set (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) :=
  {χ | Nonempty (rationalUnramifiedTwist G χ A ≅ B)}

/-- Cancel a common twist by applying its inverse to the actual isomorphism. -/
theorem rationalUnramifiedTwistIso_iff
    (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (χ ψ : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) :
    Nonempty (rationalUnramifiedTwist G χ A ≅ rationalUnramifiedTwist G ψ B) ↔
      Nonempty (rationalUnramifiedTwist G (ψ⁻¹ * χ) A ≅ B) := by
  constructor
  · rintro ⟨e⟩
    refine ⟨(rationalUnramifiedTwistMulIso G ψ⁻¹ χ A).symm ≪≫
      SmoothRep.twistIso (ψ⁻¹).val.toMonoidHom
        (isOpen_rationalUnramifiedCharacter_ker G ψ⁻¹) e ≪≫
      rationalUnramifiedTwistMulIso G ψ⁻¹ ψ B ≪≫ ?_⟩
    simpa only [inv_mul_cancel] using rationalUnramifiedTwistOneIso G B
  · rintro ⟨e⟩
    have h : rationalUnramifiedTwist G ψ
        (rationalUnramifiedTwist G (ψ⁻¹ * χ) A) ≅
          rationalUnramifiedTwist G χ A := by
      simpa only [mul_inv_cancel_left] using
        rationalUnramifiedTwistMulIso G ψ (ψ⁻¹ * χ) A
    exact ⟨h.symm ≪≫ SmoothRep.twistIso ψ.val.toMonoidHom
      (isOpen_rationalUnramifiedCharacter_ker G ψ) e⟩

/-- A mixed twist-isomorphism locus is finite when its first representation is
irreducible. No admissibility or irreducibility hypothesis on `B` is needed. -/
theorem rationalUnramifiedTwistIsoLocus_finite
    (hG : GroupScheme.IsConnectedReductive G)
    (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hA : A.IsIrreducible) :
    (rationalUnramifiedTwistIsoLocus G A B).Finite := by
  classical
  by_cases h : (rationalUnramifiedTwistIsoLocus G A B).Nonempty
  · obtain ⟨χ₀, ⟨e₀⟩⟩ := h
    apply Set.Finite.of_injOn
      (f := fun χ => χ₀⁻¹ * χ)
      (t := rationalUnramifiedTwistIsoLocus G A A)
    · intro χ hχ
      obtain ⟨eχ⟩ := hχ
      exact (rationalUnramifiedTwistIso_iff G A A χ χ₀).mp ⟨eχ ≪≫ e₀.symm⟩
    · intro χ _ ψ _ hχψ
      exact mul_left_cancel hχψ
    · exact rationalTwistStabilizerFinite F G hG A hA
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact Set.finite_empty

/-- Near the identity character, an isomorphism `χ ⊗ A ≅ B` forces `χ = 1`
and `A ≅ B`. This is the finite-locus part of Konno's local separation step. -/
theorem exists_isOpen_rationalUnramifiedTwistIso_separation
    (hG : GroupScheme.IsConnectedReductive G)
    (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hA : A.IsIrreducible) :
    ∃ V : Set (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)),
      IsOpen V ∧ 1 ∈ V ∧ ∀ χ ∈ V,
        Nonempty (rationalUnramifiedTwist G χ A ≅ B) ↔
          χ = 1 ∧ Nonempty (A ≅ B) := by
  let S := rationalUnramifiedTwistIsoLocus G A B
  have hS : S.Finite := rationalUnramifiedTwistIsoLocus_finite G hG A B hA
  refine ⟨(S \ {1})ᶜ, (hS.subset Set.sdiff_subset).isClosed.isOpen_compl,
    by simp, ?_⟩
  intro χ hχ
  constructor
  · intro h
    have hχ1 : χ = 1 := by
      by_contra hne
      exact hχ ⟨h, hne⟩
    refine ⟨hχ1, ?_⟩
    subst χ
    obtain ⟨e⟩ := h
    exact ⟨(rationalUnramifiedTwistOneIso G A).symm ≪≫ e⟩
  · rintro ⟨rfl, ⟨e⟩⟩
    exact ⟨rationalUnramifiedTwistOneIso G A ≪≫ e⟩

/-- Pull local isolation back along any character-valued map continuous at the
base point and equal to the identity there. -/
theorem eventually_rationalUnramifiedTwistIso_separation
    (hG : GroupScheme.IsConnectedReductive G)
    (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hA : A.IsIrreducible)
    {T : Type uT} [TopologicalSpace T] (t₀ : T)
    (f : T → unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))
    (hf : ContinuousAt f t₀) (hf₀ : f t₀ = 1) :
    ∀ᶠ t in 𝓝 t₀, Nonempty (rationalUnramifiedTwist G (f t) A ≅ B) ↔
      f t = 1 ∧ Nonempty (A ≅ B) := by
  obtain ⟨V, hV, h1, hsep⟩ :=
    exists_isOpen_rationalUnramifiedTwistIso_separation G hG A B hA
  have ht : Filter.Tendsto f (𝓝 t₀) (𝓝 1) := by
    have h : Filter.Tendsto f (𝓝 t₀) (𝓝 (f t₀)) := hf
    rw [hf₀] at h
    exact h
  filter_upwards [ht (hV.mem_nhds h1)] with t ht
  exact hsep (f t) ht

/-- Two families of twists based at the identity can be isomorphic near the
base point only where their characters agree and their original objects agree. -/
theorem eventually_rationalUnramifiedTwistsIso_separation
    (hG : GroupScheme.IsConnectedReductive G)
    (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hA : A.IsIrreducible)
    {T : Type uT} [TopologicalSpace T] (t₀ : T)
    (f g : T → unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))
    (hf : ContinuousAt f t₀) (hg : ContinuousAt g t₀)
    (hf₀ : f t₀ = 1) (hg₀ : g t₀ = 1) :
    ∀ᶠ t in 𝓝 t₀,
      Nonempty (rationalUnramifiedTwist G (f t) A ≅
        rationalUnramifiedTwist G (g t) B) ↔
          f t = g t ∧ Nonempty (A ≅ B) := by
  have h := eventually_rationalUnramifiedTwistIso_separation G hG A B hA t₀
    (fun t => (g t)⁻¹ * f t) (hg.inv.mul hf) (by simp [hf₀, hg₀])
  filter_upwards [h] with t ht
  rw [rationalUnramifiedTwistIso_iff G A B, ht]
  simp only [inv_mul_eq_one, eq_comm]

end Langlands.CuspidalSupport
