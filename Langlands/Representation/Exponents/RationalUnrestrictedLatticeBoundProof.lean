import Langlands.Representation.Exponents.RationalUnrestrictedLatticeBoundStatement
import Langlands.Representation.Exponents.UnrestrictedCompressedLatticeBoundProof
import Langlands.Representation.Aubert.General.RationalLatticeCoefficientDecayProof
import Langlands.Representation.MatrixCoefficient.CompactTranslateLatticeBoundProof
import Langlands.Representation.Smooth.FixedVectors.OrderProof

/-! # Growth bounds along weakly dominant actual cocharacter lattices -/

noncomputable section

universe u uV uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.Plancherel

open GroupScheme BruhatTits.SpecialCompact Aubert.General Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

/-- A supplied simultaneous standard basis gives the actual unrestricted
finite-lattice bound, including weak chamber and central directions. -/
theorem rationalUnrestrictedLatticeBound :
    RationalUnrestrictedLatticeBoundStatement.{u, uV, uI} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro ν K0 hBasis π hπ I _ _ x hnonneg
  classical
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  have hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν ∅) ζ :=
    ⟨ν, by simpa only [rootSet_empty] using isStandardCocharacter_empty_self i ν⟩
  obtain ⟨B, hB, hBJ⟩ := hBasis
  obtain ⟨-, A₀, q₀, hA₀, hmem₀⟩ :=
    hBJ (rootSet i ν ∅) (rootSet_subset i ν ∅)
  let e : (I → ℕ) →+ cocharacterLattice T :=
    { toFun := fun n => ∑ a, n a • x a
      map_zero' := by simp
      map_add' := by
        intro m n
        simp only [Pi.add_apply, add_nsmul, Finset.sum_add_distrib] }
  let τ : Multiplicative (I → ℕ) →* rationalPoints G :=
    (uniformizerPowers i).comp e.toMultiplicative
  have hch : ∀ n : I → ℕ,
      τ (.ofAdd n) ∈ standardComponentCA i q₀ ∧
        τ (.ofAdd n) ∈ standardComponentCAplus i ν (rootSet i ν ∅) q₀ := by
    intro n
    have hnn : ∀ β, 0 ≤ simpleRootPairing i ν β (∑ a, n a • x a) := by
      intro β
      rw [map_sum]
      apply Finset.sum_nonneg
      intro a _
      rw [map_nsmul]
      exact nsmul_nonneg (hnonneg a β) _
    have hc := RationalCoefficientDecay.uniformizer_mem_chambers i ν hi hfinite
      ∅ hexists hA₀ (∑ a, n a • x a) (by simp) hnn
    exact ⟨hc.1, hc.2.1⟩
  have hlattice : ∀ (φ : SmoothDual π.representation) (v : π),
      ∃ a : I → ℝ, (∀ j, 0 < a j ∧ a j ^ 2 * (0 : ℝ) < 1) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : I → ℕ,
          ‖(φ : Module.Dual ℂ π) (π.representation
            (uniformizerPowers i (.ofAdd (∑ j, n j • x j))) v)‖ ≤
              C * ∏ j, a j ^ n j := by
    intro φ v
    obtain ⟨Kv, hv⟩ := π.isSmooth v
    obtain ⟨Kφ, hφ⟩ := φ.property
    obtain ⟨K, hKB, hKle⟩ := hB.2.mem_iff.mp (Kv ⊓ Kφ).mem_nhds_one
    let Ko : OpenSubgroup (rationalPoints G) := ⟨K, (hB.1 K hKB).2.2.1⟩
    have hle : K ≤ Kv.toSubgroup ⊓ Kφ.toSubgroup := hKle
    have hvK : v ∈ fixedVectors π.representation K :=
      fixedVectors_antitone π.representation (le_trans hle inf_le_left) hv
    have hφK : (φ : Module.Dual ℂ π) ∈ fixedVectors π.representation.dual K :=
      fixedVectors_antitone π.representation.dual (le_trans hle inf_le_right) hφ
    have hmember := hmem₀ K hKB
    have hfactor : ∀ k ∈ Ko,
        ∃ l ∈ Ko.toSubgroup ⊓ standardOppositeUnipotentPoints i ν (rootSet i ν ∅),
        ∃ m ∈ Ko.toSubgroup ⊓ levi i ν ∅,
        ∃ u ∈ Ko.toSubgroup ⊓ unipotent i ν ∅, k = l * m * u := by
      intro k hk
      obtain ⟨⟨l, m, u⟩, heq⟩ := hmember.1.2 ⟨k, hk⟩
      exact ⟨l, l.property, m, m.property, u, u.property,
        (congrArg Subtype.val heq).symm⟩
    have hup : ∀ n u, u ∈ Ko.toSubgroup ⊓ unipotent i ν ∅ →
        τ (.ofAdd n) * u * (τ (.ofAdd n))⁻¹ ∈ Ko := by
      intro n u hu
      exact ((hmember.2.2.1 _ (hch n).2).1 ⟨u, hu, rfl⟩).1
    have hlow : ∀ n l,
        l ∈ Ko.toSubgroup ⊓ standardOppositeUnipotentPoints i ν (rootSet i ν ∅) →
        (τ (.ofAdd n))⁻¹ * l * τ (.ofAdd n) ∈ Ko := by
      intro n l hl
      have h := (hmember.2.2.1 _ (hch n).2).2 ⟨l, hl, rfl⟩
      have h' : (τ (.ofAdd n))⁻¹ * l * ((τ (.ofAdd n))⁻¹)⁻¹ ∈ Ko.toSubgroup := h.1
      rw [inv_inv] at h'
      exact h'
    have hmid : ∀ n m, m ∈ Ko.toSubgroup ⊓ levi i ν ∅ →
        (τ (.ofAdd n))⁻¹ * m * τ (.ofAdd n) ∈ Ko := by
      intro n m hm
      have hm' : m ∈ ambientConjugate (τ (.ofAdd n))
          ((Ko.toSubgroup ⊓ levi i ν ∅ : Subgroup (rationalPoints G)) :
            Set (rationalPoints G)) := by
        rw [hmember.2.1 _ (hch n).1]
        exact hm
      obtain ⟨y, hy, heq⟩ := hm'
      have heq' : (τ (.ofAdd n))⁻¹ * m * τ (.ofAdd n) = y := by
        rw [← heq]
        group
      rw [heq']
      exact hy.1
    obtain ⟨a, ha, hbound⟩ := unrestrictedCompressedLatticeBound
      (rationalPoints G) π I π.representation hπ Ko (hB.1 K hKB).2.2.2
      (unipotent i ν ∅) (levi i ν ∅)
      (standardOppositeUnipotentPoints i ν (rootSet i ν ∅)) hfactor τ hup hlow hmid
    obtain ⟨C, hC, hcoeff⟩ := hbound ⟨v, hvK⟩ (φ : Module.Dual ℂ π) hφK
    exact ⟨a, fun j => ⟨by linarith [ha j], by simp⟩, C, hC, hcoeff⟩
  intro S₁ S₂ F₀ hS₁ hS₂ hF₀ φ v
  obtain ⟨a, ha, C, hC, hcoeff⟩ := compactTranslateLatticeBound
    (rationalPoints G) π π.representation π.isSmooth I
    (fun n => uniformizerPowers i (.ofAdd (∑ j, n j • x j))) (fun _ => 0)
    hlattice S₁ S₂ F₀ hS₁ hS₂ hF₀ φ v
  exact ⟨a, fun j => (ha j).1, C, hC, hcoeff⟩

end Langlands.Plancherel
