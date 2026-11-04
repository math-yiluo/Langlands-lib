import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedCompactnessStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily

/-!
# Local-field affine boundedness and compactness

Finite-coordinate proof of the local-field specialization of KP Fact 2.2.3.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- A compact scalar set has a nonzero valuative upper bound. -/
theorem IsCompact.exists_valuative_bound [IsValuativeTopology F]
    {C : Set F} (hC : IsCompact C) :
    ∃ b : F, b ≠ 0 ∧ ∀ x ∈ C, x ≤ᵥ b := by
  classical
  let v := ValuativeRel.valuation F
  let U : Fˣ → Set F := fun b => {x | v x ≤ v (b : F)}
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    have hb : v.restrict (b : F) ≠ 0 := by simp
    simpa only [U, Valuation.restrict_le_iff] using v.isOpen_closedBall hb
  have hcover : C ⊆ ⋃ b, U b := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact Set.mem_iUnion.mpr ⟨1, by simp [U]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx0, by simp [U]⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU hcover
  let γ := t.sup (fun b => v (b : F)) ⊔ 1
  obtain ⟨b, hb⟩ := ValuativeRel.valuation_surjective γ
  refine ⟨b, ?_, ?_⟩
  · intro hb0
    have hγ : (1 : ValuativeRel.ValueGroupWithZero F) ≤ γ := le_sup_right
    rw [← hb, hb0, map_zero] at hγ
    exact one_ne_zero (le_antisymm hγ zero_le)
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    apply (v.vle_iff_le).mpr
    exact hxa.trans ((Finset.le_sup ha).trans (le_sup_left.trans_eq hb.symm))

/-- The exact local-field comparison in the canonical rational-point topology. -/
theorem localFieldAffineBoundedCompactness_proof (F : Type u)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : LocalFieldAffineBoundedCompactnessProperty F := by
  intro X _ _
  let : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
  intro B hB
  let e₀ := (rationalPointHomeomorph F X).trans (affineSchemePointHomeomorph F X F)
  constructor
  · intro hbound
    let : T2Space F := by
      let := IsTopologicalAddGroup.rightUniformSpace F
      let := isUniformAddGroup_of_addCommGroup (G := F)
      infer_instance
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType F (AffineCoordinateRing F X))
    let e₁ := AlgPoint.polynomialPointHomeomorph (R := F) (S := F) (Fin n)
    let e : RationalPoint F X → (Fin n → F) := fun p =>
      e₁ (AlgPoint.precomp f (e₀ p))
    have he : IsClosedEmbedding e := e₁.isClosedEmbedding.comp
      ((AlgPoint.isClosedEmbedding_precomp_of_surjective f hf).comp e₀.isClosedEmbedding)
    choose b hb0 hb using fun i : Fin n => hbound (f (MvPolynomial.X i))
    let K : Set (Fin n → F) := Set.pi Set.univ
      (fun i => {x | ValuativeRel.valuation F x ≤ ValuativeRel.valuation F (b i)})
    have hK : IsCompact K := isCompact_univ_pi
      (fun i => IsNonarchimedeanLocalField.isCompact_closedBall F _)
    refine (he.isCompact_preimage hK).of_isClosed_subset hB ?_
    intro p hp i hi
    change ValuativeRel.valuation F
      (rationalPointAlgebraHom F X p (f (MvPolynomial.X i))) ≤
        ValuativeRel.valuation F (b i)
    exact ((ValuativeRel.valuation F).vle_iff_le).mp (hb i p hp)
  · intro hcompact a
    have hc : Continuous (fun p : RationalPoint F X => rationalPointAlgebraHom F X p a) :=
      (AlgPoint.continuous_eval a).comp e₀.continuous
    obtain ⟨b, hb, h⟩ := IsCompact.exists_valuative_bound (hcompact.image hc)
    exact ⟨b, hb, fun p hp => h _ ⟨p, hp, rfl⟩⟩

end Langlands.AlgebraicGeometry.PointTopology
