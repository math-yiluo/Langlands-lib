import Langlands.BaseChange.TwistedCharacter.NestedTraceComparison
import Langlands.BaseChange.TwistedCharacter.InducedTraceTransport
import Langlands.BaseChange.TwistedInductionSpans

/-! # Proper induced twisted traces as combinations of unramified block families -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear Geometric HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v w

theorem blockShape_length_pos {m : ℕ} (C : BlockShape m) (hm : 0 < m) : 0 < C.length := by
  by_contra! hz
  have hz' : C.length = 0 := by omega
  have : IsEmpty (Fin C.length) := by rw [hz']; exact Fin.isEmpty
  have hsum := C.sum_eq
  rw [Finset.sum_of_isEmpty] at hsum
  omega

theorem length_le_flatten_length {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    B.length ≤ (B.flatten S).length := by
  change B.length ≤ ∑ i, (S i).length
  calc B.length = ∑ _i : Fin B.length, 1 := by simp
    _ ≤ ∑ i, (S i).length :=
      Finset.sum_le_sum fun i _ => blockShape_length_pos (S i) (B.positive i)

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)

/-- Unramified families of irreducible tempered σ-stable blocks, on shapes with at least two
blocks, evaluated at real exponents. -/
def flatRealFamilySet (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant], Set (Distribution (GeneralLinear n E.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _
  exact {D | ∃ (L : BlockShape n) (_ : 2 ≤ L.length)
    (δ : ∀ k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (L.size k) E.Carrier))
    (_ : ∀ k, (δ k).representation.IsIrreducible)
    (htemp : ∀ k, T.IsTempered (δ k).representation)
    (A : ∀ k, SigmaIntertwiner σ (L.size k) (δ k).representation) (x : Fin L.length → ℝ),
    D = blockFamilyTrace T hModule σ L id δ (fun k => (htemp k).isAdmissible) A μ
      (fun k => realPowerParameter T (x k))}

/-- Unramified families of irreducible tempered σ-stable blocks with intertwiners of order
dividing `d`, on arbitrary shapes, evaluated at real exponents. -/
def normalizedFamilySet (m d : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear m E.Carrier)]
      [LocallyCompactSpace (GeneralLinear m E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear m E.Carrier)]
      [MeasurableSpace (GeneralLinear m E.Carrier)] [BorelSpace (GeneralLinear m E.Carrier)]
      (μ : Measure (GeneralLinear m E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant], Set (Distribution (GeneralLinear m E.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _
  exact {D | ∃ (C : BlockShape m)
    (δ : ∀ k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (C.size k) E.Carrier))
    (_ : ∀ k, (δ k).representation.IsIrreducible)
    (htemp : ∀ k, T.IsTempered (δ k).representation)
    (A : ∀ k, SigmaIntertwiner σ (C.size k) (δ k).representation)
    (_ : ∀ k, (A k).toLinearMap ^ d = 1) (x : Fin C.length → ℝ),
    D = blockFamilyTrace T hModule σ C id δ (fun k => (htemp k).isAdmissible) A μ
      (fun k => realPowerParameter T (x k))}

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every σ-stable irreducible twisted trace of positive rank is a combination of normalized
unramified block families at real exponents. -/
theorem twistedDistribution_mem_span_normalizedFamilySet {m : ℕ} (hm : 0 < m)
    (π : letI := T.topology; SmoothRep.{0,v,max v w} ℂ (GeneralLinear m E.Carrier))
    (hπ : letI := T.topology; π.IsAdmissible) (hirr : letI := T.topology; π.IsIrreducible)
    (Aπ : letI := T.topology; SigmaIntertwiner σ m π.representation)
    {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    letI := T.generalLinearTopologicalGroup m
    ∀ [T2Space (GeneralLinear m E.Carrier)]
      [LocallyCompactSpace (GeneralLinear m E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear m E.Carrier)]
      [MeasurableSpace (GeneralLinear m E.Carrier)] [BorelSpace (GeneralLinear m E.Carrier)]
      (μ : Measure (GeneralLinear m E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant],
      twistedDistribution μ π.representation hπ Aπ.toLinearMap ∈
        Submodule.span ℂ (normalizedFamilySet.{u,v,w} T hModule σ m d μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  let := T.generalLinearTopologicalGroup m
  intro _ _ _ _ _ μ _ _
  refine stableLanglandsTraceSpan.{u,v,w} F p E T hModule σ m hm μ _ ?_ π hπ hirr Aπ
  intro t A
  rw [standardTrace_eq_standardFamilyTrace T hModule σ t μ A]
  have hδ := temperedDatum_blocks_isAdmissible T t
  choose cA hcA using fun i => exists_twistingEquiv_normalizingScalar
    (entrywiseAut σ (t.shape.size i)) (hδ i) (t.irreducible i) (A i) hd
    (entrywiseAut_pow_eq_one σ hσ _)
  let An (i : Fin t.shape.length) :=
    scaleTwistingEquiv (entrywiseAut σ (t.shape.size i)) (cA i) (A i)
  have hscale := unramifiedFamilyTrace_scale σ t.shape id (fun i => (t.blocks i).representation) A
    (T.leviHalfModulus t.shape) (T.isOpen_ker_leviHalfModulus t.shape)
    (leviHalfModulus_leviAut_padic T hModule σ t.shape) μ hδ cA
    (fun i => realPowerParameter T (t.exponent i))
  have hP : (∏ i, ((cA i : ℂˣ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _
  have hmem : unramifiedFamilyTrace σ t.shape id (fun i => (t.blocks i).representation) An
      (T.leviHalfModulus t.shape) (T.isOpen_ker_leviHalfModulus t.shape)
      (leviHalfModulus_leviAut_padic T hModule σ t.shape) μ hδ
      (fun i => realPowerParameter T (t.exponent i)) ∈
        Submodule.span ℂ (normalizedFamilySet.{u,v,w} T hModule σ m d μ) :=
    Submodule.subset_span ⟨t.shape, t.blocks, t.irreducible, t.tempered, An, hcA, t.exponent, rfl⟩
  rw [hscale] at hmem
  have h := Submodule.smul_mem _ (∏ i, ((cA i : ℂˣ) : ℂ))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hP, one_smul] at h

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized transfer of the external tensor of unramified block families at real
exponents is a multiple of a flat family at real exponents. -/
theorem transfer_externalFamily_mem {n : ℕ} (B : BlockShape n) (hB : 2 ≤ B.length)
    (C : ∀ i, BlockShape (B.size i))
    (δ : letI := T.topology;
      ∀ i j, SmoothRep.{0,v,max v w} ℂ (GeneralLinear ((C i).size j) E.Carrier))
    (hirr : letI := T.topology; ∀ i j, (δ i j).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ i j, T.IsTempered (δ i j).representation)
    (A : letI := T.topology; ∀ i j, SigmaIntertwiner σ ((C i).size j) (δ i j).representation)
    {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1) (hA : ∀ i j, (A i j).toLinearMap ^ d = 1)
    (x : ∀ i, Fin (C i).length → ℝ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant]
      [∀ i, MeasurableSpace (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, BorelSpace (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, T2Space (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, SecondCountableTopology (GeneralLinear (B.size i) E.Carrier)]
      (μi : ∀ i, Measure (GeneralLinear (B.size i) E.Carrier)) [∀ i, (μi i).IsHaarMeasure]
      (Ttr : Distribution (B.Levi E.Carrier) →ₗ[ℂ] Distribution (GeneralLinear n E.Carrier)),
      (∀ (X : Type (max v w)) [AddCommGroup X] [Module ℂ X]
        (Ξ : Representation ℂ (B.Levi E.Carrier) X) (hΞ : IsAdmissible Ξ)
        (AΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
        (hI : IsAdmissible ((LocalFieldData.ofInstances E.Carrier).normalizedParabolicInduced B Ξ)),
        Ttr (twistedDistribution (Measure.pi μi) Ξ hΞ AΞ.toLinearMap) =
          twistedDistribution μ _ hI (normalizedParabolicSigmaIntertwiner σ B Ξ AΞ).toLinearMap) →
      Ttr (twistedDistribution (Measure.pi μi)
        (FiniteTensor.external (fun i => Induction.smoothInduced ((C i).parabolic E.Carrier)
          ((twist (leviUnramified E.Carrier (C i) id (fun j => realPowerParameter T (x i j)))
            (familyInducing (C i) (fun j => (δ i j).representation) (innerHalfModulus B C i))).comp
              ((C i).leviProjection E.Carrier))))
        (FiniteTensor.isAdmissible_external _ (fun i => isAdmissible_familyInduced (C i) id
          (fun j => (δ i j).representation) (innerHalfModulus B C i)
          (isOpen_ker_innerHalfModulus B C i) (fun j => (htemp i j).isAdmissible)
          (fun j => realPowerParameter T (x i j))))
        (PiTensorProduct.map (fun i => (TwistedPaleyWiener.inducedSigmaIntertwiner σ (C i)
          (twist (leviUnramified E.Carrier (C i) id (fun j => realPowerParameter T (x i j)))
            (familyInducing (C i) (fun j => (δ i j).representation) (innerHalfModulus B C i)))
          (twistTwistedIntertwiner (leviAut σ (C i))
            (leviUnramified E.Carrier (C i) id (fun j => realPowerParameter T (x i j)))
            (leviUnramified_leviAut E.Carrier (C i) id σ (fun j => realPowerParameter T (x i j)))
            (familyInducingIntertwiner σ (C i) (fun j => (δ i j).representation) (A i)
              (innerHalfModulus B C i) (leviHalfModulus_leviAut σ (C i))))).toLinearMap))) ∈
        Submodule.span ℂ (flatRealFamilySet.{u,v,w} T hModule σ n μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _ _ _ _ _ _ _ μi _ Ttr hT
  let e := B.flattenBlockEquiv C
  let g (i : Fin B.length) (j : Fin (C i).length) : Fin (B.flatten C).length := e ⟨i, j⟩
  let X (q : (i : Fin B.length) × Fin (C i).length) : ℝ := x q.1 q.2
  let z (k : Fin (B.flatten C).length) : ℂˣ := realPowerParameter T (X (e.symm k))
  have hw (i : Fin B.length) (j : Fin (C i).length) :
      z (g i j) = realPowerParameter T (x i j) := by
    change realPowerParameter T (X (e.symm (e ⟨i, j⟩))) = _
    rw [Equiv.symm_apply_apply]
  have hR (i : Fin B.length) (j : Fin (C i).length) : IsAdmissible (δ i j).representation :=
    (htemp i j).isAdmissible
  have hrep := external_nestedInner_reparam σ B C g (fun i j => (δ i j).representation) A μi hR z
    (fun i j => realPowerParameter T (x i j)) hw
  rw [← hrep]
  have hT' := hT _ (B.blockTensor (nestedInnerRep B C g (fun i j => (δ i j).representation) z))
    (FiniteTensor.isAdmissible_external _
      (isAdmissible_nestedInnerRep B C g (fun i j => (δ i j).representation) hR z))
    (leviTensorIntertwiner σ B (nestedInnerIntertwiner σ B C g
      (fun i j => (δ i j).representation) A z))
    (isAdmissible_nestedRep B C g (fun i j => (δ i j).representation) hR z)
  change Ttr (twistedDistribution (Measure.pi μi)
    (B.blockTensor (nestedInnerRep B C g (fun i j => (δ i j).representation) z))
    (FiniteTensor.isAdmissible_external _
      (isAdmissible_nestedInnerRep B C g (fun i j => (δ i j).representation) hR z))
    (leviTensorIntertwiner σ B (nestedInnerIntertwiner σ B C g
      (fun i j => (δ i j).representation) A z)).toLinearMap) ∈ _
  rw [hT']
  change nestedTrace σ B C g (fun i j => (δ i j).representation) A μ hR z ∈ _
  obtain ⟨c, -, hc⟩ := nestedTrace_eq_smul_flat T hModule σ B C g δ hirr htemp A hd hσ hA μ
  rw [hc z, blockFamilyTrace_reindex T hModule σ (B.flatten C)]
  have hz : (fun k => z (g (e.symm k).1 (e.symm k).2)) =
      fun k => realPowerParameter T (X (e.symm k)) := by
    funext k
    change z (e (e.symm k)) = _
    rw [Equiv.apply_symm_apply]
  rw [hz]
  refine Submodule.smul_mem _ c (Submodule.subset_span ?_)
  exact ⟨B.flatten C, hB.trans (length_le_flatten_length B C),
    Parabolic.flattenedSmoothFamily E T B C δ, fun k => hirr (e.symm k).1 (e.symm k).2,
    fun k => htemp (e.symm k).1 (e.symm k).2, fun k => A (e.symm k).1 (e.symm k).2,
    fun k => X (e.symm k), rfl⟩

/-- Admissibility of the unramified family representation at real exponents. -/
theorem isAdmissible_familyRep_padic {m : ℕ} (C : BlockShape m)
    (δ : letI := T.topology; ∀ j, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (C.size j) E.Carrier))
    (htemp : letI := T.topology; ∀ j, T.IsTempered (δ j).representation) (x : Fin C.length → ℝ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    IsAdmissible (Induction.smoothInduced (C.parabolic E.Carrier)
      ((twist (leviUnramified E.Carrier C id (fun j => realPowerParameter T (x j)))
        (familyInducing C (fun j => (δ j).representation)
          ((LocalFieldData.ofInstances E.Carrier).leviHalfModulus C))).comp
            (C.leviProjection E.Carrier))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact @isAdmissible_familyInduced E.Carrier _ T.valuativeRel T.topology T.localField m C _ id _ _ _
    (fun j => (δ j).representation)
    ((LocalFieldData.ofInstances E.Carrier).leviHalfModulus C)
    ((LocalFieldData.ofInstances E.Carrier).isOpen_ker_leviHalfModulus C)
    (fun j => (htemp j).isAdmissible) (fun j => realPowerParameter T (x j))

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized transfer of the twisted trace of a σ-stable irreducible admissible
representation of a Levi with at least two blocks is a combination of flat families at real
exponents. -/
theorem levi_transfer_mem_span {n : ℕ} (B : BlockShape n) (hB : 2 ≤ B.length)
    (Ξ : letI := T.topology; SmoothRep.{0,v,max v w} ℂ (B.Levi E.Carrier))
    (hadm : letI := T.topology; Ξ.IsAdmissible) (hirr : letI := T.topology; Ξ.IsIrreducible)
    (AΞ : letI := T.topology;
      Ξ.representation.Equiv (Ξ.representation.comp (leviAut σ B).toMonoidHom))
    {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant]
      [∀ i, MeasurableSpace (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, BorelSpace (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, T2Space (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E.Carrier)]
      [∀ i, SecondCountableTopology (GeneralLinear (B.size i) E.Carrier)]
      (μi : ∀ i, Measure (GeneralLinear (B.size i) E.Carrier)) [∀ i, (μi i).IsHaarMeasure]
      (Ttr : Distribution (B.Levi E.Carrier) →ₗ[ℂ] Distribution (GeneralLinear n E.Carrier)),
      (∀ (X : Type (max v w)) [AddCommGroup X] [Module ℂ X]
        (Ξ : Representation ℂ (B.Levi E.Carrier) X) (hΞ : IsAdmissible Ξ)
        (AΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
        (hI : IsAdmissible ((LocalFieldData.ofInstances E.Carrier).normalizedParabolicInduced B Ξ)),
        Ttr (twistedDistribution (Measure.pi μi) Ξ hΞ AΞ.toLinearMap) =
          twistedDistribution μ _ hI (normalizedParabolicSigmaIntertwiner σ B Ξ AΞ).toLinearMap) →
      Ttr (twistedDistribution (Measure.pi μi) Ξ.representation hadm AΞ.toLinearMap) ∈
        Submodule.span ℂ (flatRealFamilySet.{u,v,w} T hModule σ n μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _ _ _ _ _ _ _ μi _ Ttr hT
  have hn : 0 < n := (show 0 < B.length by omega).trans_le B.length_le
  obtain ⟨Af, hAfirr, hAfadm, ⟨eΞ⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization.{v, max v w} p E T n hn B Ξ hirr hadm
  have hfac := blockFactors_sigmaStable σ B Af hAfirr ⟨leviIntertwinerTransport σ B AΞ eΞ⟩
  let Ai (i : Fin B.length) : SigmaIntertwiner σ (B.size i) (Af i).representation := (hfac i).some
  let ρ := B.blockTensor fun i => (Af i).representation
  have hρadm : IsAdmissible ρ := FiniteTensor.isAdmissible_external _ hAfadm
  have hρirr : ρ.IsIrreducible := (isIrreducible_iff_of_equiv eΞ).mp hirr
  obtain ⟨a, ha⟩ := exists_twistedDistribution_eq_smul_of_equiv (Measure.pi μi) (leviAut σ B)
    hρadm hρirr hadm eΞ.symm (leviTensorIntertwiner σ B Ai) AΞ
  rw [ha, map_smul]
  refine Submodule.smul_mem _ a ?_
  have hfactor (i : Fin B.length) :=
    twistedDistribution_mem_span_normalizedFamilySet.{u,v,w} T hModule σ (B.positive i) (Af i)
      (hAfadm i) (hAfirr i) (Ai i) hd hσ (μi i)
  choose N f gs hsum using fun i => Submodule.mem_span_set'.mp (hfactor i)
  choose Cs δs hirrs htemps As hAs xs heqs using fun i k => (gs i k).2
  have hexp := twistedDistribution_external_eq_sum μi (fun i => (Af i).representation) hAfadm
    (fun i => (Ai i).toLinearMap) (S := fun i => Fin (N i)) f
    (σ := fun i k => Induction.smoothInduced ((Cs i k).parabolic E.Carrier)
      ((twist (leviUnramified E.Carrier (Cs i k) id (fun j => realPowerParameter T (xs i k j)))
        (familyInducing (Cs i k) (fun j => (δs i k j).representation)
          ((LocalFieldData.ofInstances E.Carrier).leviHalfModulus (Cs i k)))).comp
            ((Cs i k).leviProjection E.Carrier)))
    (fun i k => isAdmissible_familyRep_padic T (Cs i k) (δs i k) (htemps i k) (xs i k))
    (fun i k => (TwistedPaleyWiener.inducedSigmaIntertwiner σ (Cs i k)
      (twist (leviUnramified E.Carrier (Cs i k) id (fun j => realPowerParameter T (xs i k j)))
        (familyInducing (Cs i k) (fun j => (δs i k j).representation)
          ((LocalFieldData.ofInstances E.Carrier).leviHalfModulus (Cs i k))))
      (twistTwistedIntertwiner (leviAut σ (Cs i k))
        (leviUnramified E.Carrier (Cs i k) id (fun j => realPowerParameter T (xs i k j)))
        (leviUnramified_leviAut E.Carrier (Cs i k) id σ (fun j => realPowerParameter T (xs i k j)))
        (familyInducingIntertwiner σ (Cs i k) (fun j => (δs i k j).representation) (As i k)
          ((LocalFieldData.ofInstances E.Carrier).leviHalfModulus (Cs i k))
          (leviHalfModulus_leviAut σ (Cs i k))))).toLinearMap)
    (fun i => by
      rw [← hsum i]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [heqs i k]
      rfl)
  change Ttr (twistedDistribution (Measure.pi μi) (FiniteTensor.external fun i => (Af i).representation)
    (FiniteTensor.isAdmissible_external _ hAfadm)
    (PiTensorProduct.map fun i => (Ai i).toLinearMap)) ∈ _
  rw [hexp, map_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  exact transfer_externalFamily_mem T hModule σ B hB (fun i => Cs i (t i)) (fun i => δs i (t i))
    (fun i => hirrs i (t i)) (fun i => htemps i (t i)) (fun i => As i (t i)) hd hσ
    (fun i => hAs i (t i)) (fun i => xs i (t i)) μ μi Ttr hT

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every proper σ-induced twisted trace is a combination of unramified families of irreducible
tempered σ-stable blocks, on shapes with at least two blocks, at real exponents. -/
theorem sigmaProperInducedSpan_le_span_flatRealFamilySet {n : ℕ} {d : ℕ} (hd : 0 < d)
    (hσ : σ ^ d = 1) :
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
      sigmaProperInducedSpan.{u,v,w} σ μ ≤
        Submodule.span ℂ (flatRealFamilySet.{u,v,w} T hModule σ n μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _
  apply Submodule.span_le.mpr
  rintro _ ⟨B, hB, X, iAdd, iMod, Ξ, hΞ, hΞirr, BΞ, hI, rfl⟩
  let := iAdd
  let := iMod
  let H (i : Fin B.length) := GeneralLinear (B.size i) E.Carrier
  let _ (i : Fin B.length) : MeasurableSpace (H i) := borel _
  have _ (i : Fin B.length) : BorelSpace (H i) := ⟨rfl⟩
  let _ (i : Fin B.length) : T2Space (H i) := LocalFieldTopology.generalLinear_t2Space E.Carrier _
  let _ (i : Fin B.length) : LocallyCompactSpace (H i) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier _
  let _ (i : Fin B.length) : TotallyDisconnectedSpace (H i) :=
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier _
  let _ (i : Fin B.length) : SecondCountableTopology (H i) :=
    LocalFieldTopology.generalLinear_secondCountableTopology E.Carrier _
  let μi (i : Fin B.length) : Measure (H i) := Measure.haar
  have _ (i : Fin B.length) : (μi i).IsMulRightInvariant :=
    generalLinear_isMulRightInvariant E.Carrier _ (μi i)
  obtain ⟨Ttr, hT⟩ := sigmaNormalizedTraceTransfer.{u,v,max v w} σ B μ (Measure.pi μi) hd hσ
  let Ξu := universeLiftRepresentation.{v} Ξ
  have hΞu : IsAdmissible Ξu := (isAdmissible_universeLift_iff Ξ).mpr hΞ
  have hJ := isAdmissible_smoothInduced_levi B Ξu hΞu
  rw [twistedDistribution_inducedSigma_of_equiv σ B μ Ξ Ξu (universeLiftEquiv.{v} Ξ) BΞ hI hJ]
  let κ := (LocalFieldData.ofInstances E.Carrier).leviHalfModulus B
  have hκinv : IsOpen ((κ⁻¹).ker : Set (B.Levi E.Carrier)) := by
    have hk : (κ⁻¹).ker = κ.ker := by
      ext m
      simp
    rw [hk]
    exact (LocalFieldData.ofInstances E.Carrier).isOpen_ker_leviHalfModulus B
  let Ξ0 := twist κ⁻¹ Ξu
  have hΞ0 : IsAdmissible Ξ0 := (isAdmissible_twist_iff _ _ hκinv).mpr hΞu
  have hN := isAdmissible_normalizedParabolicInduced B Ξ0 hΞ0
  rw [twistedDistribution_inducedSigma_eq_normalized σ B μ Ξu _ hJ hN]
  rw [← hT _ Ξ0 hΞ0 _ hN]
  have hirr0 : Ξ0.IsIrreducible :=
    (isIrreducible_twist_iff _ _).mpr ((isIrreducible_universeLift_iff Ξ).mpr hΞirr)
  exact levi_transfer_mem_span.{u,v,w} T hModule σ B hB (SmoothRep.of Ξ0 hΞ0.1) hΞ0 hirr0 _ hd hσ
    μ μi Ttr hT

end Padic

end Langlands.BaseChange
