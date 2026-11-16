import Langlands.GroupScheme.Rational.ConvexRootSymmetricSpan
import Langlands.GroupScheme.Rational.SpanAnnihilatingCocharacter
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.Geometry.Building.FiniteRealTorusSpace
import Langlands.LinearAlgebra.RationalPositiveFunctional

/-! # Cocharacters adapted to a convex root subset -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A convex subset of a finite, negation-stable character set admits an
integral cocharacter nonnegative on the subset and vanishing, among ambient
characters, precisely on its symmetric part. -/
theorem IsConvexRootSubset.exists_cocharacter_nonneg_zero_iff
    (hT : IsSplitTorus T.toGrp)
    {R S : Set (characterLattice T)} (hS : IsConvexRootSubset R S)
    (hR : R.Finite) (hneg : ∀ α ∈ R, -α ∈ R) :
    ∃ ξ : cocharacterLattice T,
      (∀ α ∈ S, 0 ≤ latticePairing T α ξ) ∧
      ∀ α ∈ R, latticePairing T α ξ = 0 ↔ α ∈ parabolicRootLevi S := by
  classical
  have hconv := hS
  obtain ⟨C, hclosed, hCS⟩ := hconv
  let := hT.finite_realCharacterSpace
  let A := parabolicRootUnipotent S
  have hA : A.Finite := hR.subset fun α hα => hS.isClosedRootSubset.1 hα.1
  let := hA.fintype
  have hmem (α : A) : (1 : ℝ) ⊗ₜ[ℤ] (α : characterLattice T) ∈ C :=
    ((Set.ext_iff.mp hCS α).mp α.property.1).2
  have hnot (α : A) : -((1 : ℝ) ⊗ₜ[ℤ] (α : characterLattice T)) ∉ C := by
    intro h
    apply α.property.2
    apply (Set.ext_iff.mp hCS (-α)).mpr
    exact ⟨hneg α (hS.isClosedRootSubset.1 α.property.1),
      by simpa only [TensorProduct.tmul_neg] using h⟩
  obtain ⟨f, hf, hpos⟩ := exists_real_dual_nonneg_positive C hclosed
    (fun α : A => (1 : ℝ) ⊗ₜ[ℤ] (α : characterLattice T)) hmem hnot
  let fr := (f.restrictScalars ℚ).comp (toReal (characterLattice T))
  have hfr (α : characterLattice T) :
      fr (toRat α) = f ((1 : ℝ) ⊗ₜ[ℤ] α) := by
    simp only [fr, LinearMap.comp_apply, LinearMap.restrictScalars_apply, toReal_toRat]
  have hW : symmetricRootRatSpan S ≤ fr.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    change fr (toRat α) = 0
    rw [hfr]
    have hp := hf _ ((Set.ext_iff.mp hCS α).mp hα.1).2
    have hn := hf _ ((Set.ext_iff.mp hCS (-α)).mp hα.2).2
    rw [TensorProduct.tmul_neg, map_neg] at hn
    exact le_antisymm (neg_nonneg.mp hn) hp
  obtain ⟨g, hgW, hgpos⟩ := exists_rat_dual_positive_annihilating
    (symmetricRootRatSpan S) (fun α : A => toRat (α : characterLattice T))
    fr hW (fun α => by rw [hfr]; exact hpos α)
  obtain ⟨d, hd, mu, hmu⟩ := hT.exists_positive_multiple_pairing g
  have hmuzero (α : characterLattice T) (hα : α ∈ parabolicRootLevi S) :
      latticePairing T α mu = 0 := by
    have hz : g (toRat α) = 0 := hgW (toRat_mem_ratSpan hα)
    have h := hmu α
    rw [hz, mul_zero] at h
    exact_mod_cast h
  have hmupos (α : characterLattice T) (hα : α ∈ A) :
      0 < latticePairing T α mu := by
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have h := mul_pos hdq (hgpos ⟨α, hα⟩)
    rw [← hmu α] at h
    exact_mod_cast h
  obtain ⟨eta, hetaW, heta⟩ :=
    hT.exists_cocharacter_zero_iff_mem_subspace (symmetricRootRatSpan S) R hR
  let p := fun α : characterLattice T => (latticePairing T α).toAddMonoidHom
  let N := IntegralPerturbation.bound p hR.toFinset eta
  refine ⟨N • mu + eta, ?_, ?_⟩
  · intro α hα
    have hαR := hS.isClosedRootSubset.1 hα
    have hsign := IntegralPerturbation.signs p hR.toFinset mu eta
      (N := N) le_rfl (hR.mem_toFinset.mpr hαR)
    by_cases hn : -α ∈ S
    · have hm := hmuzero α ⟨hα, hn⟩
      have he := hetaW α (toRat_mem_ratSpan ⟨hα, hn⟩)
      have hz := hsign.2.2.mpr ⟨hm, he⟩
      exact hz.ge
    · exact (hsign.1.mpr (Or.inl (hmupos α ⟨hα, hn⟩))).le
  · intro α hα
    have hsign := IntegralPerturbation.signs p hR.toFinset mu eta
      (N := N) le_rfl (hR.mem_toFinset.mpr hα)
    constructor
    · intro hz
      have he := (hsign.2.2.mp hz).2
      exact (hS.mem_symmetricRootRatSpan_iff hneg hα).mp ((heta α hα).mp he)
    · intro hαS
      exact hsign.2.2.mpr ⟨hmuzero α hαS,
        hetaW α (toRat_mem_ratSpan hαS)⟩

/-- Uniform existence of an integral cocharacter adapted to a finite convex
character subset of a split torus. -/
def ConvexRootCocharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp →
    ∀ R S : Set (characterLattice T), IsConvexRootSubset R S →
      R.Finite → (∀ α ∈ R, -α ∈ R) →
      ∃ ξ : cocharacterLattice T,
        (∀ α ∈ S, 0 ≤ latticePairing T α ξ) ∧
        ∀ α ∈ R, latticePairing T α ξ = 0 ↔ α ∈ parabolicRootLevi S

/-- Closed-cone separation, rational approximation and integral perturbation
give the uniform adapted cocharacter. -/
theorem convexRootCocharacter : ConvexRootCocharacterStatement.{u} := by
  intro k _ T hT R S hS hR hneg
  exact hS.exists_cocharacter_nonneg_zero_iff hT hR hneg

end Langlands.GroupScheme
