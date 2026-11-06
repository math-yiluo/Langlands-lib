import Langlands.VirtualRepresentation.Weil.ExactRealizationProof
import Langlands.Weil.Representation.CharacterLine

/-!
# Reduction of exact degree-zero generation to irreducibles
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- Remove the actual virtual degree using the trivial continuous line. -/
def reducedClass : ContinuousExactGroup.{uG, uV} G →ₗ[ℤ]
    ContinuousExactGroup.{uG, uV} G where
  toFun x := x - ExactGrothendieckGroup.degree _ x •
    ExactGrothendieckGroup.characterClass (1 : G →ₜ* ℂˣ)
  map_add' x y := by
    simp only [map_add, add_smul]
    abel
  map_smul' z x := by
    simp only [map_smul, smul_sub, smul_smul, smul_eq_mul, RingHom.id_apply]

@[simp]
theorem reducedClass_apply (x : ContinuousExactGroup.{uG, uV} G) :
    reducedClass G x = x - ExactGrothendieckGroup.degree _ x •
      ExactGrothendieckGroup.characterClass (1 : G →ₜ* ℂˣ) := rfl

/-- Reduction fixes every element of the genuine degree kernel. -/
theorem reducedClass_eq_self {x : ContinuousExactGroup.{uG, uV} G}
    (hx : x ∈ ExactGrothendieckGroup.degreeZero _) :
    reducedClass G x = x := by
  simp only [reducedClass_apply, ExactGrothendieckGroup.mem_degreeZero] at *
  rw [hx, zero_smul, sub_zero]

/-- Every reduced exact class belongs to a submodule once all reduced
continuous irreducible classes do. -/
theorem reducedClass_mem_of_irreducibles
    (S : Submodule ℤ (ContinuousExactGroup.{uG, uV} G))
    (hS : ∀ (A : FiniteRepresentation.{0, uG, uV} ℂ G)
      (hc : A.IsContinuous), A.IsIrreducible →
      reducedClass G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩) ∈ S)
    (x : ContinuousExactGroup.{uG, uV} G) :
    reducedClass G x ∈ S := by
  have hb (b : IrreducibleBasis.{uG, uV} G) :
      reducedClass G (realizeExact G (generator b)) ∈ S := by
    rw [realizeExact_generator]
    rcases b with ⟨n, ⟨c, hc⟩⟩
    change reducedClass G (ExactGrothendieckGroup.ofClass _
      (forgetIrreducibleClass G c)) ∈ S
    clear hc
    induction c using Quotient.inductionOn with
    | h A =>
      exact hS A.val A.property.1 A.property.2
  obtain ⟨v, rfl⟩ := realizeExact_surjective G x
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using S.zero_mem
  | add v w hv hw =>
    simpa only [map_add] using S.add_mem hv hw
  | single b z =>
    have hz : Finsupp.single b z = z • generator b := by simp [generator]
    rw [hz, map_smul, map_smul]
    exact S.smul_mem z (hb b)

/-- The actual dimension-zero kernel is generated after the irreducible
reduction; no semisimplicity premise is needed. -/
theorem degreeZero_le_of_reduced_irreducibles
    (S : Submodule ℤ (ContinuousExactGroup.{uG, uV} G))
    (hS : ∀ (A : FiniteRepresentation.{0, uG, uV} ℂ G)
      (hc : A.IsContinuous), A.IsIrreducible →
      reducedClass G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩) ∈ S) :
    ExactGrothendieckGroup.degreeZero _ ≤ S := by
  intro x hx
  have h := reducedClass_mem_of_irreducibles G S hS x
  rwa [reducedClass_eq_self G hx] at h

/-- Twisting a reduced virtual class adds only a multiple of a difference
of two character-line classes. -/
theorem reducedClass_continuousTwist (χ : G →ₜ* ℂˣ)
    (x : ContinuousExactGroup.{uG, uV} G) :
    reducedClass G (ExactGrothendieckGroup.continuousTwist χ x) =
      ExactGrothendieckGroup.continuousTwist χ (reducedClass G x) +
        ExactGrothendieckGroup.degree _ x •
          (ExactGrothendieckGroup.characterClass χ -
            ExactGrothendieckGroup.characterClass (1 : G →ₜ* ℂˣ)) := by
  have hd : ExactGrothendieckGroup.degree _
      (ExactGrothendieckGroup.continuousTwist χ x) =
        ExactGrothendieckGroup.degree _ x :=
    ExactGrothendieckGroup.degree_twist _ _ _ _ x
  have ht : ExactGrothendieckGroup.continuousTwist.{uG, uV} χ
      (ExactGrothendieckGroup.characterClass (1 : G →ₜ* ℂˣ)) =
        ExactGrothendieckGroup.characterClass χ := by
    rw [ExactGrothendieckGroup.continuousTwist_characterClass]
    congr 1
    ext g
    simp
  simp only [reducedClass_apply, hd, map_sub, map_smul,
    ht, smul_sub]
  abel

/-- A submodule stable under character twisting and containing differences
of character lines contains twists of every reduced class it contains. -/
theorem reducedClass_twist_mem
    (S : Submodule ℤ (ContinuousExactGroup.{uG, uV} G))
    (htwist : ∀ (χ : G →ₜ* ℂˣ) (x), x ∈ S →
      ExactGrothendieckGroup.continuousTwist χ x ∈ S)
    (hchar : ∀ χ : G →ₜ* ℂˣ,
      ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass (1 : G →ₜ* ℂˣ) ∈ S)
    (χ : G →ₜ* ℂˣ) (x : ContinuousExactGroup.{uG, uV} G)
    (hx : reducedClass G x ∈ S) :
    reducedClass G (ExactGrothendieckGroup.continuousTwist χ x) ∈ S := by
  rw [reducedClass_continuousTwist]
  exact S.add_mem (htwist χ _ hx) (S.smul_mem _ (hchar χ))

/-- Finite-image reduction and twisting reduce degree-zero generation to
the finite-image case. All three substantive premises are explicit. -/
theorem degreeZero_le_of_finiteImage_twists
    (S : Submodule ℤ (ContinuousExactGroup.{uG, uV} G))
    (htwist : ∀ (χ : G →ₜ* ℂˣ) (x), x ∈ S →
      ExactGrothendieckGroup.continuousTwist χ x ∈ S)
    (hchar : ∀ χ : G →ₜ* ℂˣ,
      ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass (1 : G →ₜ* ℂˣ) ∈ S)
    (hfinite : ∀ (A : FiniteRepresentation.{0, uG, uV} ℂ G)
      (hc : A.IsContinuous), A.HasFiniteImage →
      reducedClass G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩) ∈ S)
    (hred : ∀ (A : FiniteRepresentation.{0, uG, uV} ℂ G),
      A.IsContinuous → A.IsIrreducible →
      ∃ (χ : G →ₜ* ℂˣ) (B : FiniteRepresentation.{0, uG, uV} ℂ G),
        B.IsContinuous ∧ B.HasFiniteImage ∧
          Nonempty (FiniteRepresentation.Equiv A
            (FiniteRepresentation.twist χ.toMonoidHom B))) :
    ExactGrothendieckGroup.degreeZero _ ≤ S := by
  apply degreeZero_le_of_reduced_irreducibles G S
  intro A hc hi
  obtain ⟨χ, B, hBc, hBf, ⟨e⟩⟩ := hred A hc hi
  have hA : ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩ =
      ExactGrothendieckGroup.continuousTwist χ
        (ExactGrothendieckGroup.ofRepresentation _ ⟨B, hBc⟩) := by
    change ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩ =
      ExactGrothendieckGroup.twist χ.toMonoidHom _ _ _
        (ExactGrothendieckGroup.ofRepresentation _ ⟨B, hBc⟩)
    rw [ExactGrothendieckGroup.twist_ofRepresentation]
    exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ e
  rw [hA]
  exact reducedClass_twist_mem G S htwist hchar χ _ (hfinite B hBc hBf)

end Langlands.VirtualRepresentation.Weil
