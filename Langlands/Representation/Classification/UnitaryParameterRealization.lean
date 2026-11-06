import Langlands.Representation.Classification.UnitaryParameterFlattening

/-! # Actual unitary parameter realizations

Store actual valid inducing parameters for a prescribed smooth representation,
transport them along isomorphisms and exact rank equalities, and assemble
finite products by ordered parameter flattening.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual valid unitary inducing parameters and an actual comparison with
the prescribed representation. This contains data, not an exhaustion premise. -/
structure UnitaryParameterRealization {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) where
  shape : BlockShape n
  blocks : letI := T.topology
    ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (shape.size i) F.Carrier)
  exponent : Fin shape.length → ℝ
  valid : IsUnitaryGenericDatum F T shape blocks exponent
  iso : letI := T.topology
    π ≅ T.twistedProductInduced shape blocks exponent

namespace UnitaryParameterRealization

/-- Pull a parameter realization back along an actual representation isomorphism. -/
def ofIso {n : ℕ}
    {π σ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (e : letI := T.topology; π ≅ σ)
    (R : UnitaryParameterRealization F T σ) : UnitaryParameterRealization F T π := by
  letI := T.topology
  exact { R with iso := e ≪≫ R.iso }

/-- Transport all parameters along an exact equality of total group ranks. -/
def rankTransport {m n : ℕ} (h : m = n)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier))
    (R : UnitaryParameterRealization F T π) :
    UnitaryParameterRealization F T (h ▸ π) := by
  cases h
  exact R

/-- Forgetting the chosen data gives the existential conclusion used in
unitary generic exhaustion. -/
theorem exists_datum {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (R : UnitaryParameterRealization F T π) :
    ∃ (B : BlockShape n)
      (δ : letI := T.topology
        ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (s : Fin B.length → ℝ),
      IsUnitaryGenericDatum F T B δ s ∧
        (letI := T.topology; Nonempty (π ≅ T.twistedProductInduced B δ s)) :=
  ⟨R.shape, R.blocks, R.exponent, R.valid, ⟨R.iso⟩⟩

end UnitaryParameterRealization

private theorem exists_unitaryProductParameters_of_localIso {n : ℕ}
    (B : BlockShape n) (C : BlockRefinement B)
    (σ : letI := T.topology
      ∀ j, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
    (δ : letI := T.topology
      ∀ j k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((C j).size k) F.Carrier))
    (s : ∀ j, Fin (C j).length → ℝ)
    (h : ∀ j, IsUnitaryGenericDatum F T (C j) (δ j) (s j))
    (e : letI := T.topology
      ∀ j, σ j ≅ T.twistedProductInduced (C j) (δ j) (s j)) :
    letI := T.topology
    ∃ (D : BlockShape n)
      (ε : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size i) F.Carrier))
      (t : Fin D.length → ℝ),
      IsUnitaryGenericDatum F T D ε t ∧
        Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
          T.twistedProductInduced D ε t) := by
  let := T.topology
  refine ⟨B.flatten C, flattenedUnitaryBlocks F T B C δ,
    flattenedUnitaryExponents B C s,
    isUnitaryGenericDatum_flatten F T B C δ s h, ?_⟩
  have ef : σ ≅ (fun j => T.twistedProductInduced (C j) (δ j) (s j)) :=
    Pi.isoMk e
  have eo : (T.normalizedProductInductionFunctor B).obj σ ≅
      (T.normalizedProductInductionFunctor B).obj
        (fun j => T.twistedProductInduced (C j) (δ j) (s j)) :=
    (T.normalizedProductInductionFunctor B).mapIso ef
  have eg : T.twistedProductInduced (B.flatten C)
      (flattenedUnitaryBlocks F T B C δ) (flattenedUnitaryExponents B C s) ≅
      (T.normalizedProductInductionFunctor B).obj
        (fun j => T.twistedProductInduced (C j) (δ j) (s j)) :=
    flattenedUnitaryProductIso.{uF,uV} F T B C δ s
  exact ⟨eo ≪≫ eg.symm⟩

/-- Assemble actual local parameter realizations using canonical ordered
flattening, preserving all strict bounds and multiplicities. -/
theorem exists_unitaryProductParameters {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ j, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
    (R : ∀ j, UnitaryParameterRealization.{uF,uV} F T (σ j)) :
    letI := T.topology
    ∃ (C : BlockShape n)
      (δ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (C.size i) F.Carrier))
      (s : Fin C.length → ℝ),
      IsUnitaryGenericDatum F T C δ s ∧
        Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
          T.twistedProductInduced C δ s) := by
  let := T.topology
  exact exists_unitaryProductParameters_of_localIso F T B
    (fun j => (R j).shape) σ (fun j => (R j).blocks)
    (fun j => (R j).exponent) (fun j => (R j).valid) (fun j => (R j).iso)

namespace UnitaryParameterRealization

private theorem product_nonempty {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ j, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
    (R : ∀ j, UnitaryParameterRealization.{uF,uV} F T (σ j)) :
    letI := T.topology
    Nonempty (UnitaryParameterRealization.{uF,uV} F T
      ((T.normalizedProductInductionFunctor B).obj σ)) := by
  obtain ⟨C, δ, s, h, e⟩ := exists_unitaryProductParameters.{uF,uV} F T B σ R
  exact ⟨⟨C, δ, s, h, Classical.choice e⟩⟩

/-- Assemble chosen local realizations into an actual realization of their
entire normalized product. Classical choice selects the comparison map. -/
def product {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ j, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
    (R : ∀ j, UnitaryParameterRealization.{uF,uV} F T (σ j)) :
    letI := T.topology
    UnitaryParameterRealization.{uF,uV} F T
      ((T.normalizedProductInductionFunctor B).obj σ) :=
  Classical.choice (product_nonempty.{uF,uV} F T B σ R)

end UnitaryParameterRealization

end Langlands.Classification
