import Langlands.BaseChange.TwistedCharacter.NestedTraceFamily
import Langlands.BaseChange.TwistedCharacter.StandardTraceComparison
import Langlands.Representation.Parabolic.FlattenedProductInduction

/-! # Nested unramified families agree with the flattened family up to a root of unity -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear Geometric HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v w

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- At unitary parameters the flattened normalized product of twisted irreducible tempered
blocks is irreducible and equivalent to the nested representation. -/
theorem flattened_unitary_irreducible_equiv {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {r : ℕ} (g : ∀ i, Fin (S i).length → Fin r)
    (δ : letI := T.topology;
      ∀ i j, SmoothRep.{0,v,max v w} ℂ (GeneralLinear ((S i).size j) E.Carrier))
    (hirr : letI := T.topology; ∀ i j, (δ i j).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ i j, T.IsTempered (δ i j).representation)
    (z : Fin r → ℂˣ) (hz : ∀ k, ‖(z k : ℂ)‖ = 1) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup n
    let e := B.flattenBlockEquiv S
    (T.normalizedProductInduced (B.flatten S) (fun k =>
        twist (determinantUnramified E.Carrier ((B.flatten S).size k)
          (z (g (e.symm k).1 (e.symm k).2)))
          (Parabolic.flattenedSmoothFamily E T B S δ k).representation)).IsIrreducible ∧
    Nonempty ((T.normalizedProductInduced (B.flatten S) (fun k =>
        twist (determinantUnramified E.Carrier ((B.flatten S).size k)
          (z (g (e.symm k).1 (e.symm k).2)))
          (Parabolic.flattenedSmoothFamily E T B S δ k).representation)).Equiv
      ((LocalFieldData.ofInstances E.Carrier).normalizedParabolicInduced B
        (B.blockTensor (nestedInnerRep B S g (fun i j => (δ i j).representation) z)))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro e
  let δ' := Parabolic.flattenedSmoothFamily E T B S δ
  let g' (k : Fin (B.flatten S).length) : Fin r := g (e.symm k).1 (e.symm k).2
  have hirr' (k : Fin (B.flatten S).length) : (δ' k).representation.IsIrreducible :=
    hirr (e.symm k).1 (e.symm k).2
  have hunit' (k : Fin (B.flatten S).length) : IsUnitarizable (δ' k).representation :=
    isUnitarizable_of_isTempered T ((B.flatten S).positive k) (δ' k) (hirr' k)
      (htemp (e.symm k).1 (e.symm k).2)
  refine ⟨(normalizedProduct_unitaryTwist T (B.flatten S) δ' hirr' hunit' g' z hz).1, ?_⟩
  let C (i : Fin B.length) (j : Fin (S i).length) :
      SmoothRep.{0,v,max v w} ℂ (GeneralLinear ((S i).size j) E.Carrier) :=
    (δ i j).twist (determinantUnramified E.Carrier ((S i).size j) (z (g i j)))
      (isOpen_ker_determinantUnramified E.Carrier _ _)
  let e1 := Parabolic.flattenedProductInducedEquiv E T B S C
  have hinner (i : Fin B.length) : Nonempty ((nestedInnerRep B S g
      (fun i j => (δ i j).representation) z i).Equiv
        (T.normalizedProductInduced (S i) (fun j => (C i j).representation))) :=
    nonempty_familyInduced_equiv (S i) (g i) (fun j => (δ i j).representation)
      (innerHalfModulus B S i) z
  let e2 := T.normalizedProductInducedEquiv B (fun i => (hinner i).some.symm)
  exact ⟨e1.trans e2⟩

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The nested family of irreducible tempered σ-stable blocks with normalized intertwiners is one
root of unity times the unramified family of the flattened shape. -/
theorem nestedTrace_eq_smul_flat {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {r : ℕ} (g : ∀ i, Fin (S i).length → Fin r)
    (δ : letI := T.topology;
      ∀ i j, SmoothRep.{0,v,max v w} ℂ (GeneralLinear ((S i).size j) E.Carrier))
    (hirr : letI := T.topology; ∀ i j, (δ i j).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ i j, T.IsTempered (δ i j).representation)
    (A : letI := T.topology; ∀ i j, SigmaIntertwiner σ ((S i).size j) (δ i j).representation)
    {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1) (hA : ∀ i j, (A i j).toLinearMap ^ d = 1) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant],
      let e := B.flattenBlockEquiv S
      ∃ c : ℂ, c ^ d = 1 ∧ ∀ z,
        nestedTrace σ B S g (fun i j => (δ i j).representation) A μ
            (fun i j => (htemp i j).isAdmissible) z =
          c • blockFamilyTrace T hModule σ (B.flatten S) (fun k => g (e.symm k).1 (e.symm k).2)
            (Parabolic.flattenedSmoothFamily E T B S δ)
            (fun k => (htemp (e.symm k).1 (e.symm k).2).isAdmissible)
            (fun k => A (e.symm k).1 (e.symm k).2) μ z := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _ e
  let δ' := Parabolic.flattenedSmoothFamily E T B S δ
  let g' (k : Fin (B.flatten S).length) : Fin r := g (e.symm k).1 (e.symm k).2
  let A' (k : Fin (B.flatten S).length) :
      SigmaIntertwiner σ ((B.flatten S).size k) (δ' k).representation :=
    A (e.symm k).1 (e.symm k).2
  have hR' (k : Fin (B.flatten S).length) : IsAdmissible (δ' k).representation :=
    (htemp (e.symm k).1 (e.symm k).2).isAdmissible
  have hirr' (k : Fin (B.flatten S).length) : (δ' k).representation.IsIrreducible :=
    hirr (e.symm k).1 (e.symm k).2
  have hA' (k : Fin (B.flatten S).length) : (A' k).toLinearMap ^ d = 1 :=
    hA (e.symm k).1 (e.symm k).2
  have hunit (z : Fin r → ℂˣ) (hz : ∀ k, ‖(z k : ℂ)‖ = 1) :=
    flattened_unitary_irreducible_equiv T B S g δ hirr htemp z hz
  obtain ⟨c, hc, hcomp⟩ := nestedTrace_comparison σ B S g (fun i j => (δ i j).representation) A μ
    (T.isOpen_ker_leviHalfModulus (B.flatten S))
    (leviHalfModulus_leviAut_padic T hModule σ (B.flatten S)) hd hσ
    (fun i j => (htemp i j).isAdmissible) hirr hA hR' hirr' hA' hunit
  refine ⟨c, hc, fun z => ?_⟩
  exact hcomp z

end Padic

end Langlands.BaseChange
