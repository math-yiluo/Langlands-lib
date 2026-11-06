import Langlands.Representation.Classification.UnitaryGenericStatement
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof

/-! # Flattening actual unitary inducing parameters

Ordered refinement concatenates the local parameter families, preserving
strict exponents and multiplicity-preserving Hermitian symmetry. The actual
normalized products are related by the published ordered regrouping map.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Concatenate actual blocks in the exact ordered refinement coordinates. -/
def flattenedUnitaryBlocks {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (δ : letI := T.topology
      ∀ j k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier)) :
    letI := T.topology
    ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((B.flatten S).size i) F.Carrier) :=
  fun i => δ ((B.flattenBlockEquiv S).symm i).1 ((B.flattenBlockEquiv S).symm i).2

/-- Concatenate the real exponents using the same ordered refinement labels. -/
def flattenedUnitaryExponents {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (s : ∀ j, Fin (S j).length → ℝ) : Fin (B.flatten S).length → ℝ :=
  fun i => s ((B.flattenBlockEquiv S).symm i).1 ((B.flattenBlockEquiv S).symm i).2

private def reindexRankIso {ι : Type} (r : ι → ℕ)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (r i) F.Carrier))
    {i j : ι} (h : i = j) :
    letI := T.topology
    (congrArg r h ▸ δ i) ≅ δ j := by
  subst j
  exact Iso.refl _

private theorem transportIso_of_index_eq {ι : Type} (r : ι → ℕ)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (r i) F.Carrier))
    {a b c d : ι} (hac : a = c) (hbd : b = d)
    (hab : r a = r b) (hcd : r c = r d) :
    letI := T.topology
    Nonempty ((hcd ▸ δ c) ≅ δ d) →
      Nonempty ((hab ▸ δ a) ≅ δ b) := by
  subst c
  subst d
  exact id

private def flattenedUnitaryFactorIso {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)
    (δ : letI := T.topology
      ∀ j k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier))
    (s : ∀ j, Fin (S j).length → ℝ)
    (q : (j : Fin B.length) × Fin (S j).length) :
    letI := T.topology
    ((B.flatten_size_flattenBlockEquiv S q) ▸
      T.segmentFactor (flattenedUnitaryBlocks F T B S δ (B.flattenBlockEquiv S q))
        (flattenedUnitaryExponents B S s (B.flattenBlockEquiv S q))) ≅
      T.segmentFactor (δ q.1 q.2) (s q.1 q.2) := by
  exact reindexRankIso F T
    (fun q : (j : Fin B.length) × Fin (S j).length => (S q.1).size q.2)
    (fun q => T.segmentFactor (δ q.1 q.2) (s q.1 q.2))
    ((B.flattenBlockEquiv S).symm_apply_apply q)

private def flattenedUnitaryInnerIso {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)
    (δ : letI := T.topology
      ∀ j k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier))
    (s : ∀ j, Fin (S j).length → ℝ) (j : Fin B.length) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (S j)).obj (fun k =>
      (B.flatten_size_flattenBlockEquiv S ⟨j,k⟩) ▸
        T.segmentFactor
          (flattenedUnitaryBlocks F T B S δ (B.flattenBlockEquiv S ⟨j,k⟩))
          (flattenedUnitaryExponents B S s (B.flattenBlockEquiv S ⟨j,k⟩))) ≅
      T.twistedProductInduced (S j) (δ j) (s j) := by
  letI := T.topology
  exact (T.normalizedProductInductionFunctor (S j)).mapIso
    (Pi.isoMk fun k => flattenedUnitaryFactorIso F T B S δ s ⟨j,k⟩)

private theorem flattenedUnitaryProduct_nonempty {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (δ : letI := T.topology
      ∀ j k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier))
    (s : ∀ j, Fin (S j).length → ℝ) :
    letI := T.topology
    Nonempty (T.twistedProductInduced (B.flatten S) (flattenedUnitaryBlocks F T B S δ)
      (flattenedUnitaryExponents B S s) ≅
        (T.normalizedProductInductionFunctor B).obj
          (fun j => T.twistedProductInduced (S j) (δ j) (s j))) := by
  let := T.topology
  let e := B.flattenBlockEquiv S
  let h (q : (j : Fin B.length) × Fin (S j).length) :
      (S q.1).size q.2 = (B.flatten S).size (e q) :=
    (B.flatten_size_flattenBlockEquiv S q).symm
  let τ := fun i => T.segmentFactor (flattenedUnitaryBlocks F T B S δ i)
    (flattenedUnitaryExponents B S s i)
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF,max uF uV} F T n
      (B.flatten S) B S e h (fun j k x => B.index_index_eq_flatten S ⟨j,k⟩ x) τ
  exact ⟨ereg ≪≫ (T.normalizedProductInductionFunctor B).mapIso
    (Pi.isoMk fun j => flattenedUnitaryInnerIso F T B S δ s j)⟩

/-- The actual flattened twisted product is the nested normalized product.
No irreducibility or analytic assumption is needed for this isomorphism. -/
def flattenedUnitaryProductIso {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (δ : letI := T.topology
      ∀ j k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier))
    (s : ∀ j, Fin (S j).length → ℝ) :
    letI := T.topology
    T.twistedProductInduced (B.flatten S) (flattenedUnitaryBlocks F T B S δ)
      (flattenedUnitaryExponents B S s) ≅
        (T.normalizedProductInductionFunctor B).obj
          (fun j => T.twistedProductInduced (S j) (δ j) (s j)) :=
  Classical.choice (flattenedUnitaryProduct_nonempty F T B S δ s)

/-- The prescribed multiplicity-preserving local matchings induce a matching
on all flattened blocks. -/
theorem hasHermitianSymmetricParameters_flatten {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)
    (δ : letI := T.topology
      ∀ j k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier))
    (s : ∀ j, Fin (S j).length → ℝ)
    (h : ∀ j, HasHermitianSymmetricParameters F T (S j) (δ j) (s j)) :
    HasHermitianSymmetricParameters F T (B.flatten S)
      (flattenedUnitaryBlocks F T B S δ) (flattenedUnitaryExponents B S s) := by
  classical
  let := T.topology
  choose ej hrj hej using h
  let e := B.flattenBlockEquiv S
  let f := (e.symm.trans (Equiv.sigmaCongrRight ej)).trans e
  have hf (q : (j : Fin B.length) × Fin (S j).length) :
      e.symm (f (e q)) = ⟨q.1, ej q.1 q.2⟩ := by
    simp [f]
  have hr : ∀ i, (B.flatten S).size i = (B.flatten S).size (f i) := by
    intro i
    obtain ⟨q, rfl⟩ := e.surjective i
    change (S (e.symm (e q)).1).size (e.symm (e q)).2 =
      (S (e.symm (f (e q))).1).size (e.symm (f (e q))).2
    rw [e.symm_apply_apply, hf]
    exact hrj q.1 q.2
  refine ⟨f, hr, ?_⟩
  intro i
  obtain ⟨q, rfl⟩ := e.surjective i
  constructor
  · change s (e.symm (e q)).1 (e.symm (e q)).2 =
      -s (e.symm (f (e q))).1 (e.symm (f (e q))).2
    rw [e.symm_apply_apply, hf]
    exact (hej q.1 q.2).1
  · change Nonempty ((hr (e q) ▸ δ (e.symm (e q)).1 (e.symm (e q)).2) ≅
      δ (e.symm (f (e q))).1 (e.symm (f (e q))).2)
    exact transportIso_of_index_eq F T
      (fun q : (j : Fin B.length) × Fin (S j).length => (S q.1).size q.2)
      (fun q => δ q.1 q.2)
      (e.symm_apply_apply q) (hf q) (hr (e q)) (hrj q.1 q.2)
      (hej q.1 q.2).2

/-- Concatenating valid local parameters preserves every condition of the
published unitary-generic datum. -/
theorem isUnitaryGenericDatum_flatten {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)
    (δ : letI := T.topology
      ∀ j k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier))
    (s : ∀ j, Fin (S j).length → ℝ)
    (h : ∀ j, IsUnitaryGenericDatum F T (S j) (δ j) (s j)) :
    IsUnitaryGenericDatum F T (B.flatten S)
      (flattenedUnitaryBlocks F T B S δ) (flattenedUnitaryExponents B S s) := by
  let := T.topology
  refine ⟨?_, ?_, hasHermitianSymmetricParameters_flatten F T B S δ s
    (fun j => (h j).2.2)⟩
  · intro i
    exact (h ((B.flattenBlockEquiv S).symm i).1).1
      ((B.flattenBlockEquiv S).symm i).2
  · intro i
    exact (h ((B.flattenBlockEquiv S).symm i).1).2.1
      ((B.flattenBlockEquiv S).symm i).2

end Langlands.Classification
