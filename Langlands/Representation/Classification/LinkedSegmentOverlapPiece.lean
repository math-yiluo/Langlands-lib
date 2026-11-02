import Langlands.Representation.Classification.LinkedSegmentOverlapInduction

/-!
# The identity geometric piece of two overlapping segment socles

The normalized refined Jacquet module of `A₀ ⊗ A₁` along the identity refinement
of the source shape, written as a triple tensor product on
`GL(deg Δ) × GL(deg init) × GL(deg term)`, and its transport to the target refined
Levi.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Classification.QuotientHom

open GeneralLinear Geometric CategoryTheory PadicField.TopologicalData
open scoped TensorProduct

universe uF uV uW

/-- The one-block Levi embedding is the single coordinate. -/
theorem oneBlock_leviEmbedding {R : Type*} [CommRing R] (m : ℕ) (hm : 0 < m)
    (g : (CuspidalSupport.LeviAdmissibility.oneBlock m hm).Levi R) :
    (CuspidalSupport.LeviAdmissibility.oneBlock m hm).leviEmbedding R g =
      g ⟨0, Nat.one_pos⟩ := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  have ha := index_zero_val (CuspidalSupport.LeviAdmissibility.oneBlock m hm) Nat.one_pos a
  have hb := index_zero_val (CuspidalSupport.LeviAdmissibility.oneBlock m hm) Nat.one_pos b
  have h := (CuspidalSupport.LeviAdmissibility.oneBlock m hm).leviEmbedding_apply_same R g
    ⟨0, Nat.one_pos⟩ a b
  rw [Fin.ext ha, Fin.ext hb] at h
  exact h

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData} {n : ℕ}

namespace OverlapConfig

variable (O : OverlapConfig.{uF, uV} T n)

set_option maxHeartbeats 1000000 in
/-- The Jacquet side of the identity piece: given the two-block Jacquet module of
`A₁` along the split of `Δ'`, the refined Jacquet module of `A₀ ⊗ A₁` is the triple
tensor `A₀ ⊗ π₁ ⊗ π₂` pulled back to the source refined Levi. -/
def jacquetPieceEquiv (A : ∀ i, Rep.{uW} ℂ (GeneralLinear (O.B.size i) F.Carrier))
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear O.init.degree F.Carrier) V₁)
    (π₂ : Representation ℂ (GeneralLinear O.term.degree F.Carrier) V₂)
    (E₁ : (T.normalizedJacquet (O.S ⟨1, Nat.one_lt_two⟩) (A ⟨1, Nat.one_lt_two⟩).ρ).Equiv
      (Representation.tprod
        (π₁.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨0, Nat.zero_lt_two⟩))
        (π₂.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨1, Nat.one_lt_two⟩)))) :
    (T.normalizedRefinedJacquet O.B O.S (FiniteTensor.external fun i => (A i).ρ)).Equiv
      ((tripleTensor (A ⟨0, Nat.zero_lt_two⟩).ρ π₁ π₂).comp O.φB) := by
  let i0 : Fin O.B.length := ⟨0, Nat.zero_lt_two⟩
  let i1 : Fin O.B.length := ⟨1, Nat.one_lt_two⟩
  let ψ : refinedLevi F.Carrier O.B O.S →* ∀ i, (O.S i).Levi F.Carrier :=
    (refinedLeviEquiv F.Carrier O.B O.S).symm.toMonoidHom
  let X : ∀ i, Representation ℂ ((O.S i).Levi F.Carrier) _ :=
    fun i => T.normalizedJacquet (O.S i) (A i).ρ
  have hS0 : (O.S i0).length = 1 := rfl
  let E₀ : (T.normalizedJacquet (O.S i0) (A i0).ρ).Equiv
      ((A i0).ρ.comp ((O.S i0).leviEmbedding F.Carrier)) :=
    (T.singleBlockNormalizedJacquetEquiv (O.S i0) hS0 (A i0).ρ).symm
  let e₁ := RefinedJacquetTensor.jacquetEquiv T O.B O.S A
  let e₂ : (FiniteTensor.external X).Equiv
      (Representation.tprod ((X i0).comp (Pi.evalMonoidHom (fun i => (O.S i).Levi F.Carrier) i0))
        ((X i1).comp (Pi.evalMonoidHom (fun i => (O.S i).Levi F.Carrier) i1))) :=
    externalTwoEquiv (H := fun i : Fin 2 => (O.S i).Levi F.Carrier) X
  let e₃ := FiniteTensorFiltration.tprodCongr
    (FiniteTensorFiltration.compCongr E₀ (Pi.evalMonoidHom (fun i => (O.S i).Levi F.Carrier) i0))
    (FiniteTensorFiltration.compCongr E₁ (Pi.evalMonoidHom (fun i => (O.S i).Levi F.Carrier) i1))
  refine ((e₁.trans (FiniteTensorFiltration.compCongr e₂ ψ)).trans
    (FiniteTensorFiltration.compCongr e₃ ψ)).trans (equivOfApplyEq _ _ fun x => ?_)
  have h0 : (O.S i0).leviEmbedding F.Carrier ((refinedLeviEquiv F.Carrier O.B O.S).symm x i0) =
      (refinedLeviEquiv F.Carrier O.B O.S).symm x i0 ⟨0, Nat.one_pos⟩ :=
    oneBlock_leviEmbedding O.Δ.degree O.Δ.degree_pos
      ((refinedLeviEquiv F.Carrier O.B O.S).symm x i0)
  change TensorProduct.map ((A i0).ρ
      ((O.S i0).leviEmbedding F.Carrier ((refinedLeviEquiv F.Carrier O.B O.S).symm x i0))) _ =
    TensorProduct.map ((A i0).ρ
      ((refinedLeviEquiv F.Carrier O.B O.S).symm x i0 ⟨0, Nat.one_pos⟩)) _
  rw [h0]
  rfl

set_option maxHeartbeats 1000000 in
/-- The inner part of the identity geometric piece of `A₀ ⊗ A₁`, given the
two-block Jacquet module of `A₁` along the split of `Δ'`: after the refined Jacquet
module and the intersection transport, it is the triple tensor `A₀ ⊗ π₁ ⊗ π₂`
pulled back along `φC`. -/
theorem nonempty_transportedJacquetEquiv
    (A : letI := T.topology; ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (O.B.size i) F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.term.degree F.Carrier))
    (E₁ : letI := T.topology
      (T.normalizedJacquet (O.S ⟨1, Nat.one_lt_two⟩) (A ⟨1, Nat.one_lt_two⟩).obj.ρ).Equiv
      (Representation.tprod
        (π₁.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨0, Nat.zero_lt_two⟩))
        (π₂.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨1, Nat.one_lt_two⟩)))) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    Nonempty (Representation.Equiv
      ((subgroupEqualityFunctor _ _ O.hR.2.1).obj
        ((intersectionTransportFunctor F.Carrier O.B O.C 1).obj
          ((subgroupEqualityFunctor _ _ O.hS.2.1.symm).obj
            ((T.normalizedRefinedJacquetFunctor O.B O.S).obj
              (FiniteTensor.externalSmoothObject A))))).representation
      ((tripleTensor (A ⟨0, Nat.zero_lt_two⟩).representation π₁.representation
        π₂.representation).comp O.φC)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let τ := tripleTensor (A ⟨0, Nat.zero_lt_two⟩).representation π₁.representation
    π₂.representation
  let X := FiniteTensor.externalSmoothObject A
  let eJ : Representation.Equiv ((T.normalizedRefinedJacquetFunctor O.B O.S).obj X).representation
      (τ.comp O.φB) :=
    O.jacquetPieceEquiv (fun i => (A i).obj) π₁.representation π₂.representation E₁
  exact ⟨O.transportedPieceEquiv X τ eJ⟩

set_option maxHeartbeats 1000000 in
/-- The identity geometric piece of `A₀ ⊗ A₁` is the normalized refined induction of
the target factors `(A₀ ⊗ π₁, π₂)`. -/
theorem nonempty_geometricPiece_refinedEquiv
    (A : letI := T.topology; ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (O.B.size i) F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.term.degree F.Carrier))
    (E₁ : letI := T.topology
      (T.normalizedJacquet (O.S ⟨1, Nat.one_lt_two⟩) (A ⟨1, Nat.one_lt_two⟩).obj.ρ).Equiv
      (Representation.tprod
        (π₁.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨0, Nat.zero_lt_two⟩))
        (π₂.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨1, Nat.one_lt_two⟩)))) :
    letI := T.topology
    Nonempty (Representation.Equiv
      ((geometricPieceFunctor T O.B O.C 1 O.S O.R O.hS.2.1 O.hR.2.1).obj
        (FiniteTensor.externalSmoothObject A)).ρ
      (Parabolic.RefinedInductionTensor.refinedRepresentation F T O.C O.R
        (O.targetFactors (A ⟨0, Nat.zero_lt_two⟩) π₁ π₂))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let Q' := (subgroupEqualityFunctor _ _ O.hR.2.1).obj
    ((intersectionTransportFunctor F.Carrier O.B O.C 1).obj
      ((subgroupEqualityFunctor _ _ O.hS.2.1.symm).obj
        ((T.normalizedRefinedJacquetFunctor O.B O.S).obj
          (FiniteTensor.externalSmoothObject A))))
  obtain ⟨eQ⟩ := O.nonempty_transportedJacquetEquiv A π₁ π₂ E₁
  let e₁ : Representation.Equiv (T.normalizedRefinedInduced O.C O.R Q'.representation)
      (Parabolic.RefinedInductionTensor.refinedRepresentation F T O.C O.R
        (O.targetFactors (A ⟨0, Nat.zero_lt_two⟩) π₁ π₂)) :=
    ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr T O.C O.R
      (eQ.trans (O.inducingEquiv (A ⟨0, Nat.zero_lt_two⟩) π₁ π₂).symm)
  change Nonempty ((T.normalizedRefinedInduced O.C O.R Q'.representation).Equiv _)
  exact ⟨e₁⟩

set_option maxHeartbeats 1000000 in
/-- The identity geometric piece of `A₀ ⊗ A₁`, given the two-block Jacquet module
of `A₁` along the split of `Δ'`: the induced union block from `(A₀, π₁)` tensored
with `π₂`. -/
theorem nonempty_geometricPieceEquiv
    (A : letI := T.topology; ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (O.B.size i) F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.term.degree F.Carrier))
    (E₁ : letI := T.topology
      (T.normalizedJacquet (O.S ⟨1, Nat.one_lt_two⟩) (A ⟨1, Nat.one_lt_two⟩).obj.ρ).Equiv
      (Representation.tprod
        (π₁.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨0, Nat.zero_lt_two⟩))
        (π₂.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨1, Nat.one_lt_two⟩)))) :
    letI := T.topology
    Nonempty (Representation.Equiv
      ((geometricPieceFunctor T O.B O.C 1 O.S O.R O.hS.2.1 O.hR.2.1).obj
        (FiniteTensor.externalSmoothObject A)).ρ
      (Representation.tprod
        ((Parabolic.RefinedInductionTensor.blockRepresentations F T O.C O.R
          (O.targetFactors (A ⟨0, Nat.zero_lt_two⟩) π₁ π₂) (0 : Fin 2)).comp
          (Pi.evalMonoidHom (fun j : Fin 2 => GeneralLinear (O.C.size j) F.Carrier) 0))
        (π₂.representation.comp
          (Pi.evalMonoidHom (fun j : Fin 2 => GeneralLinear (O.C.size j) F.Carrier) 1)))) := by
  let := T.topology
  obtain ⟨e₁⟩ := O.nonempty_geometricPiece_refinedEquiv A π₁ π₂ E₁
  obtain ⟨e₃⟩ := O.nonempty_inducedPieceEquiv (A ⟨0, Nat.zero_lt_two⟩) π₁ π₂
  exact ⟨(e₁.trans (Parabolic.refinedInductionTensor.{uF, uW} p F T n O.C O.R
    (O.targetFactors (A ⟨0, Nat.zero_lt_two⟩) π₁ π₂)).some.val).trans e₃⟩

end OverlapConfig

end Langlands.Classification.QuotientHom
