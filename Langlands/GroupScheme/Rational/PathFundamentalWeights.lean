import Langlands.LinearAlgebra.RootDatumPathWeights
import Langlands.GroupScheme.Rational.RepresentationNormalizerWeights
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition

/-! # Weights of a highest-weight representation at the first fundamental weight of a path -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitPinning

open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

/-- Every simple root of a pinning has a reflection representative, supplied by the
root-datum structure of the pinning. -/
theorem nonempty_simpleReflectionRepresentative (a : p.base.support) :
    Nonempty (p.SimpleReflectionRepresentative a) := by
  obtain ⟨g, σ, hg, hσ⟩ := p.isRootDatum.2.2 (a : p.rootIndex)
  exact ⟨⟨g, σ, hg, hσ⟩⟩

variable {p} {n : Type} [Fintype n] [DecidableEq n]

/-- Weight multiplicities of an actual representation are invariant under every simple
reflection. -/
theorem finrank_representationWeightSpace_simpleReflection (ρ : MatrixRepresentation G n)
    (a : p.base.support) (μ : characterLattice p.torus) :
    Module.finrank k (p.representationWeightSpace ρ (p.rootDatum.reflection (a : p.rootIndex) μ)) =
      Module.finrank k (p.representationWeightSpace ρ μ) :=
  (p.nonempty_simpleReflectionRepresentative a).some.finrank_representationWeightSpace_reflection
    ρ μ

/-- The actual weight spaces of a representation are independent. -/
theorem iSupIndep_representationWeightSpace (ρ : MatrixRepresentation G n) :
    iSupIndep (p.representationWeightSpace ρ) := by
  let := p.isSplitTorus.isAffineHom
  exact (MatrixRepresentation.characterSpace_iSupIndep (ρ.restrict p.inclusion)).comp
    (rationalCharacters.equivCharacterLattice p.torus).symm.injective

variable {ρ : MatrixRepresentation G n} {L : ℕ} {β : Fin L → p.base.support}
  {lam : characterLattice p.torus}

/-- The Library's fundamental weight at the first vertex of a path component is a path
fundamental weight. -/
theorem isPathFundamental_of_isFundamentalWeight (hβ : IsPathComponent β)
    (h : p.IsFundamentalWeight (β ⟨0, hβ.pos⟩) lam) : IsPathFundamental β lam := by
  refine ⟨fun i => ?_, fun z hz => ?_⟩
  · have hi := h (β i)
    by_cases h0 : (i : ℕ) = 0
    · rw [ite_eq_left h0]
      rw [ite_eq_left (congrArg β (Fin.ext h0))] at hi
      exact hi
    · rw [ite_eq_right h0]
      rw [ite_eq_right (fun e => h0 (by rw [hβ.injective e]))] at hi
      exact hi
  · have hz' := h z
    rw [ite_eq_right (fun e => hz ⟨_, e.symm⟩)] at hz'
    exact hz'

/-- The highest weight of a supplied fundamental representation at the first vertex of a path
component is a path fundamental weight. -/
theorem FundamentalRepresentation.isPathFundamental (hβ : IsPathComponent β)
    (F : p.FundamentalRepresentation (β ⟨0, hβ.pos⟩)) :
    IsPathFundamental β F.highestWeight :=
  isPathFundamental_of_isFundamentalWeight hβ F.isFundamentalWeight

/-- **Weights at the first fundamental weight of a path.** Let `β` be a path component of type
`A_L` of the Dynkin diagram of the pinning and `lam` the fundamental weight at `β 0`. Every weight
of a highest-weight representation at `lam` is a path weight `lam - (α_0 + ⋯ + α_{j-1})`. -/
theorem exists_eq_pathWeight_of_isHighestWeight (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) {μ : characterLattice p.torus}
    (hμ : p.representationWeightSpace ρ μ ≠ ⊥) : ∃ j ≤ L, μ = pathWeight β lam j := by
  refine exists_eq_pathWeight hβ hlam (S := {μ | p.representationWeightSpace ρ μ ≠ ⊥})
    ?_ ?_ hμ
  · intro ν hν γ hbot
    apply hν
    rw [← Submodule.finrank_eq_zero, ← finrank_representationWeightSpace_simpleReflection ρ γ ν]
    exact Submodule.finrank_eq_zero.mpr hbot
  · intro ν hν
    exact hρ.2.2.2 ν hν

/-- Every path weight has a one-dimensional weight space. -/
theorem finrank_pathWeightSpace (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) {j : ℕ} (hj : j ≤ L) :
    Module.finrank k (p.representationWeightSpace ρ (pathWeight β lam j)) = 1 := by
  induction j with
  | zero =>
    rw [pathWeight_zero]
    exact hρ.2.2.1
  | succ j ih =>
    rw [← reflection_pathWeight_self hβ hlam (by omega : j < L),
      finrank_representationWeightSpace_simpleReflection]
    exact ih (by omega)

/-- The weights of a highest-weight representation at `lam` are exactly the path weights. -/
theorem representationWeightSpace_ne_bot_iff (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) (μ : characterLattice p.torus) :
    p.representationWeightSpace ρ μ ≠ ⊥ ↔ ∃ j ≤ L, μ = pathWeight β lam j := by
  refine ⟨exists_eq_pathWeight_of_isHighestWeight hρ hβ hlam, ?_⟩
  rintro ⟨j, hj, rfl⟩ hbot
  have h := finrank_pathWeightSpace hρ hβ hlam hj
  rw [hbot, finrank_bot] at h
  exact zero_ne_one h

/-- The `L + 1` path weight spaces form an internal direct sum decomposition of the
representation space. -/
theorem isInternal_pathWeightSpace (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) :
    DirectSum.IsInternal fun j : Fin (L + 1) =>
      p.representationWeightSpace ρ (pathWeight β lam j) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (iSupIndep_representationWeightSpace ρ).comp fun i j h =>
      Fin.ext (pathWeight_injOn hβ hlam (by omega) (by omega) h)
  · rw [eq_top_iff, ← iSup_representationWeightSpace_eq_top p ρ]
    refine iSup_le fun μ => ?_
    by_cases hμ : p.representationWeightSpace ρ μ = ⊥
    · rw [hμ]
      exact bot_le
    · obtain ⟨j, hj, rfl⟩ := exists_eq_pathWeight_of_isHighestWeight hρ hβ hlam hμ
      exact le_iSup_of_le (⟨j, by omega⟩ : Fin (L + 1)) le_rfl

/-- The index equivalence `(Σ j : Fin (L + 1), Fin 1) ≃ Fin (L + 1)`. -/
private def sigmaFinOneEquiv (m : ℕ) : (Σ _ : Fin m, Fin 1) ≃ Fin m where
  toFun a := a.1
  invFun j := ⟨j, 0⟩
  left_inv a := by
    obtain ⟨j, c⟩ := a
    rw [Fin.fin_one_eq_zero c]
  right_inv _ := rfl

/-- A basis of the representation space indexed by `Fin (L + 1)`, whose `j`-th vector spans the
one-dimensional weight space of the path weight `lam - (α_0 + ⋯ + α_{j-1})`. The vectors are
chosen; only their weight spaces are canonical. -/
def pathWeightBasis (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) : Module.Basis (Fin (L + 1)) k (n → k) :=
  ((isInternal_pathWeightSpace hρ hβ hlam).collectedBasis fun j =>
      Module.finBasisOfFinrankEq k (p.representationWeightSpace ρ (pathWeight β lam j))
        (finrank_pathWeightSpace hρ hβ hlam (by omega : (j : ℕ) ≤ L))).reindex
    (sigmaFinOneEquiv (L + 1))

/-- The `j`-th vector of `pathWeightBasis` has weight `lam - (α_0 + ⋯ + α_{j-1})`. -/
theorem pathWeightBasis_mem (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) (j : Fin (L + 1)) :
    pathWeightBasis hρ hβ hlam j ∈ p.representationWeightSpace ρ (pathWeight β lam j) := by
  have h := (isInternal_pathWeightSpace hρ hβ hlam).collectedBasis_mem
    (fun j => Module.finBasisOfFinrankEq k (p.representationWeightSpace ρ (pathWeight β lam j))
      (finrank_pathWeightSpace hρ hβ hlam (by omega : (j : ℕ) ≤ L))) ⟨j, 0⟩
  have e : pathWeightBasis hρ hβ hlam j =
      (isInternal_pathWeightSpace hρ hβ hlam).collectedBasis
        (fun j => Module.finBasisOfFinrankEq k
          (p.representationWeightSpace ρ (pathWeight β lam j))
          (finrank_pathWeightSpace hρ hβ hlam (by omega : (j : ℕ) ≤ L))) ⟨j, 0⟩ :=
    Module.Basis.reindex_apply _ _ _
  rw [e]
  exact h

/-- The representation has dimension `L + 1`. -/
theorem card_eq_of_isHighestWeight (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) : Fintype.card n = L + 1 := by
  have h := (isInternal_pathWeightSpace hρ hβ hlam).collectedBasis fun j =>
    Module.finBasis k (p.representationWeightSpace ρ (pathWeight β lam j))
  have hcard := Module.finrank_eq_card_basis h
  rw [Module.finrank_fintype_fun_eq_card] at hcard
  rw [hcard, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_congr rfl fun j _ => by
    rw [finrank_pathWeightSpace hρ hβ hlam (by omega : (j : ℕ) ≤ L)]]
  simp

end Langlands.GroupScheme.SplitPinning
