import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof

/-! Algebraic assembly of actual finite products of Tadic building blocks. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The exact finite-product conclusion of Tadic exhaustion, at a supplied rank. -/
def HasTadicFactorization {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  ∃ (B : BlockShape n)
    (σ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, IsTadicBuildingBlock F T (σ i)) ∧
      Nonempty (π ≅ (T.normalizedProductInductionFunctor B).obj σ)

/-- An actual isomorphism preserves the two building-block alternatives. -/
theorem isTadicBuildingBlock_of_iso {n : ℕ} :
    letI := T.topology
    ∀ {π ρ : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)},
      IsTadicBuildingBlock F T π → (π ≅ ρ) → IsTadicBuildingBlock F T ρ := by
  let := T.topology
  intro π ρ hπ e
  rcases hπ with ⟨d, S, h, hS, ⟨eS⟩⟩ | ⟨d, S, α, h, hS, hα0, hα, ⟨eS⟩⟩
  · exact Or.inl ⟨d, S, h, hS, ⟨eS ≪≫ e⟩⟩
  · exact Or.inr ⟨d, S, α, h, hS, hα0, hα, ⟨eS ≪≫ e⟩⟩

namespace HasTadicFactorization

/-- Transport a complete product presentation along an actual isomorphism. -/
theorem of_iso {n : ℕ} :
    letI := T.topology
    ∀ {π ρ : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)},
      HasTadicFactorization π → (π ≅ ρ) → HasTadicFactorization ρ := by
  let := T.topology
  rintro π ρ ⟨B, σ, hσ, ⟨eπ⟩⟩ e
  exact ⟨B, σ, hσ, ⟨e.symm ≪≫ eπ⟩⟩

/-- Preserve the exact presentation through equality of total ranks. -/
theorem rank_transport {n m : ℕ} (h : n = m)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : HasTadicFactorization π) :
    HasTadicFactorization (h ▸ π) := by
  subst m
  exact hπ

end HasTadicFactorization

private def reindexRankIso {ι : Type} (r : ι → ℕ)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (r i) F.Carrier))
    {i j : ι} (h : i = j) :
    letI := T.topology
    (congrArg r h ▸ σ i) ≅ σ j := by
  subst j
  exact Iso.refl _

private def flattenedBlocks {n : ℕ} (B : BlockShape n)
    (S : ∀ i, BlockShape (B.size i))
    (τ : letI := T.topology
      ∀ i k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S i).size k) F.Carrier)) :
    letI := T.topology
    ∀ k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier) :=
  let e := B.flattenBlockEquiv S
  fun k => τ (e.symm k).1 (e.symm k).2

set_option maxHeartbeats 400000 in
private theorem flattenedBlocks_inducedIso {n : ℕ} (B : BlockShape n)
    (S : ∀ i, BlockShape (B.size i))
    (τ : letI := T.topology
      ∀ i k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S i).size k) F.Carrier)) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor (B.flatten S)).obj
      (flattenedBlocks B S τ) ≅
        (T.normalizedProductInductionFunctor B).obj
          (fun i => (T.normalizedProductInductionFunctor (S i)).obj (τ i))) := by
  let := T.topology
  let e := B.flattenBlockEquiv S
  let C := B.flatten S
  let τflat := flattenedBlocks B S τ
  have h (q : (j : Fin B.length) × Fin (S j).length) :
      (S q.1).size q.2 = C.size (e q) :=
    (B.flatten_size_flattenBlockEquiv S q).symm
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF,max uF uV}
    F T n C B S e h
    (fun j k x => B.index_index_eq_flatten S ⟨j,k⟩ x) τflat
  have einner (j : Fin B.length) :
      (T.normalizedProductInductionFunctor (S j)).obj
        (fun k => (h ⟨j,k⟩).symm ▸ τflat (e ⟨j,k⟩)) ≅
      (T.normalizedProductInductionFunctor (S j)).obj (τ j) := by
    apply (T.normalizedProductInductionFunctor (S j)).mapIso
    apply Pi.isoMk
    intro k
    exact reindexRankIso
      (fun q : (j : Fin B.length) × Fin (S j).length => (S q.1).size q.2)
      (fun q => τ q.1 q.2) (e.symm_apply_apply ⟨j,k⟩)
  exact ⟨ereg ≪≫ (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk einner)⟩

set_option maxHeartbeats 400000 in
/-- Flatten a finite family of complete presentations using actual normalized
induction in stages. No irreducibility or unitarity hypothesis is required. -/
theorem hasTadicFactorization_normalizedProduct {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (σ : ∀ i,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, HasTadicFactorization (σ i)) →
        HasTadicFactorization ((T.normalizedProductInductionFunctor B).obj σ) := by
  classical
  let := T.topology
  intro σ hσ
  change ∀ i, ∃ (S : BlockShape (B.size i))
    (τ : ∀ k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (S.size k) F.Carrier)),
    (∀ k, IsTadicBuildingBlock F T (τ k)) ∧
      Nonempty (σ i ≅ (T.normalizedProductInductionFunctor S).obj τ) at hσ
  choose S τ hτ hστ using hσ
  let eστ := fun i => Classical.choice (hστ i)
  obtain ⟨eflat⟩ := flattenedBlocks_inducedIso B S τ
  let e := B.flattenBlockEquiv S
  refine ⟨B.flatten S, flattenedBlocks B S τ,
    fun k => hτ (e.symm k).1 (e.symm k).2, ?_⟩
  exact ⟨(T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk eστ) ≪≫ eflat.symm⟩

end Langlands.Classification
