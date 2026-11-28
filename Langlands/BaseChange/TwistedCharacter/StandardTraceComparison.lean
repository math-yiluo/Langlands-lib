import Langlands.BaseChange.TwistedCharacter.ExponentGrouping
import Langlands.BaseChange.TwistedCharacter.SemidirectReduction
import Langlands.Representation.Classification.RegularLanglandsDataUniquenessProof

/-! # Comparing induced twisted traces with σ-stable standard traces -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v w

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)

set_option maxHeartbeats 1600000 in
/-- Normalized products over shapes matched by an order isomorphism with equal sizes and
isomorphic blocks are equivalent after the same unramified twists. -/
theorem nonempty_normalizedProduct_twist_equiv_of_matching {n : ℕ} (B B' : BlockShape n)
    (a : Fin B.length ≃o Fin B'.length) (h : ∀ i, B.size i = B'.size (a i))
    (δ : letI := T.topology; ∀ i, SmoothRep.{0,v,w} ℂ (GeneralLinear (B.size i) E.Carrier))
    (δ' : letI := T.topology; ∀ i, SmoothRep.{0,v,w} ℂ (GeneralLinear (B'.size i) E.Carrier))
    (he : letI := T.topology; ∀ i, Nonempty ((h i ▸ δ i) ≅ δ' (a i)))
    (z : Fin B.length → ℂˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup n
    Nonempty ((T.normalizedProductInduced B (fun i =>
        twist (determinantUnramified E.Carrier (B.size i) (z i)) (δ i).representation)).Equiv
      (T.normalizedProductInduced B' (fun j =>
        twist (determinantUnramified E.Carrier (B'.size j) (z (a.symm j)))
          (δ' j).representation))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  cases B with
  | mk l s hp hs =>
    cases B' with
    | mk l' s' hp' hs' =>
      have hl : l = l' := by
        simpa using Fintype.card_congr a.toEquiv
      subst hl
      have ha : a = OrderIso.refl _ := Subsingleton.elim _ _
      subst ha
      have hss : s = s' := funext h
      subst hss
      exact ⟨T.normalizedProductInducedEquiv _ (fun i =>
        twistEquiv _ (SmoothRep.equivOfIso (he i).some))⟩

variable (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)

/-- The unramified family of the twisted tempered blocks of a shape, with the half modulus
of the supplied realization. -/
abbrev blockFamilyTrace {n : ℕ} (B : BlockShape n) {r : ℕ} (g : Fin B.length → Fin r)
    (δ : letI := T.topology; ∀ i, SmoothRep.{0,v,w} ℂ (GeneralLinear (B.size i) E.Carrier))
    (hδ : letI := T.topology; ∀ i, IsAdmissible (δ i).representation)
    (A : letI := T.topology; ∀ i, SigmaIntertwiner σ (B.size i) (δ i).representation) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant], (Fin r → ℂˣ) → Distribution (GeneralLinear n E.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _ z
  exact unramifiedFamilyTrace σ B g (fun i => (δ i).representation) A (T.leviHalfModulus B)
    (T.isOpen_ker_leviHalfModulus B) (leviHalfModulus_leviAut_padic T hModule σ B) μ hδ z

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two unramified families of irreducible tempered σ-stable block data whose unitary
specializations are equivalent normalized products differ by one nonzero scalar. -/
theorem blockFamilyTrace_comparison {n : ℕ} (B B' : BlockShape n) {r : ℕ}
    (g : Fin B.length → Fin r) (g' : Fin B'.length → Fin r)
    (δ : letI := T.topology; ∀ i, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (B.size i) E.Carrier))
    (δ' : letI := T.topology; ∀ i, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (B'.size i) E.Carrier))
    (hirr : letI := T.topology; ∀ i, (δ i).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ i, T.IsTempered (δ i).representation)
    (hirr' : letI := T.topology; ∀ i, (δ' i).representation.IsIrreducible)
    (htemp' : letI := T.topology; ∀ i, T.IsTempered (δ' i).representation)
    (A : letI := T.topology; ∀ i, SigmaIntertwiner σ (B.size i) (δ i).representation)
    (A' : letI := T.topology; ∀ i, SigmaIntertwiner σ (B'.size i) (δ' i).representation)
    {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1)
    (hequiv : ∀ z : Fin r → ℂˣ, (∀ k, ‖(z k : ℂ)‖ = 1) →
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.generalLinearTopologicalGroup n
      Nonempty ((T.normalizedProductInduced B (fun i =>
          twist (determinantUnramified E.Carrier (B.size i) (z (g i))) (δ i).representation)).Equiv
        (T.normalizedProductInduced B' (fun j =>
          twist (determinantUnramified E.Carrier (B'.size j) (z (g' j)))
            (δ' j).representation)))) :
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
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z,
        blockFamilyTrace T hModule σ B' g' δ' (fun i => (htemp' i).isAdmissible) A' μ z =
          c • blockFamilyTrace T hModule σ B g δ (fun i => (htemp i).isAdmissible) A μ z := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _
  have hδ (i : Fin B.length) : IsAdmissible (δ i).representation := (htemp i).isAdmissible
  have hδ' (i : Fin B'.length) : IsAdmissible (δ' i).representation := (htemp' i).isAdmissible
  choose cA hcA using fun i => exists_twistingEquiv_normalizingScalar
    (entrywiseAut σ (B.size i)) (hδ i) (hirr i) (A i) hd (entrywiseAut_pow_eq_one σ hσ _)
  choose cA' hcA' using fun i => exists_twistingEquiv_normalizingScalar
    (entrywiseAut σ (B'.size i)) (hδ' i) (hirr' i) (A' i) hd (entrywiseAut_pow_eq_one σ hσ _)
  let An (i : Fin B.length) := scaleTwistingEquiv (entrywiseAut σ (B.size i)) (cA i) (A i)
  let An' (i : Fin B'.length) := scaleTwistingEquiv (entrywiseAut σ (B'.size i)) (cA' i) (A' i)
  have hunit (z : Fin r → ℂˣ) (hz : ∀ k, ‖(z k : ℂ)‖ = 1) :=
    normalizedProduct_unitaryTwist T B δ hirr
      (fun i => isUnitarizable_of_isTempered T (B.positive i) (δ i) (hirr i) (htemp i)) g z hz
  obtain ⟨c, hc, hcomp⟩ := unramifiedFamilyTrace_comparison (σ := σ) (C := B) (g := g)
    (R := fun i => (δ i).representation) (A := An) (κ := T.leviHalfModulus B)
    (hκ := T.isOpen_ker_leviHalfModulus B) (hκσ := leviHalfModulus_leviAut_padic T hModule σ B)
    (μ := μ) (C' := B') (g' := g') (R' := fun i => (δ' i).representation) (A' := An')
    (κ' := T.leviHalfModulus B') (hκ' := T.isOpen_ker_leviHalfModulus B')
    (hκσ' := leviHalfModulus_leviAut_padic T hModule σ B') hd hσ hδ hirr hcA hδ' hirr' hcA'
    (fun z hz => ⟨(hunit z hz).1, hequiv z hz⟩)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hc
    exact zero_ne_one hc
  refine ⟨(∏ i, ((cA' i : ℂˣ) : ℂ))⁻¹ * c * ∏ i, ((cA i : ℂˣ) : ℂ), ?_, fun z => ?_⟩
  · refine mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) hc0) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _
  · have h1 := unramifiedFamilyTrace_scale σ B g (fun i => (δ i).representation) A
      (T.leviHalfModulus B) (T.isOpen_ker_leviHalfModulus B)
      (leviHalfModulus_leviAut_padic T hModule σ B) μ hδ cA z
    have h2 := unramifiedFamilyTrace_scale σ B' g' (fun i => (δ' i).representation) A'
      (T.leviHalfModulus B') (T.isOpen_ker_leviHalfModulus B')
      (leviHalfModulus_leviAut_padic T hModule σ B') μ hδ' cA' z
    have hz := hcomp z
    change unramifiedFamilyTrace σ B' g' _ An' _ _ _ μ hδ' z =
      c • unramifiedFamilyTrace σ B g _ An _ _ _ μ hδ z at hz
    rw [h1, h2] at hz
    change unramifiedFamilyTrace σ B' g' _ A' _ _ _ μ hδ' z =
      _ • unramifiedFamilyTrace σ B g _ A _ _ _ μ hδ z
    have hP' : (∏ i, ((cA' i : ℂˣ) : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _
    calc unramifiedFamilyTrace σ B' g' _ A' _ _ _ μ hδ' z
        = (∏ i, ((cA' i : ℂˣ) : ℂ))⁻¹ • ((∏ i, ((cA' i : ℂˣ) : ℂ)) •
            unramifiedFamilyTrace σ B' g' _ A' _ _ _ μ hδ' z) := by
          rw [smul_smul, inv_mul_cancel₀ hP', one_smul]
      _ = _ := by
          rw [hz, smul_smul, smul_smul]

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Uniqueness of standard traces per Langlands head: two σ-stable tempered data whose heads are
isomorphic have proportional standard twisted traces, for any block intertwiners. -/
theorem standardTrace_eq_smul_of_head {n : ℕ} (hn : 0 < n)
    (t t' : T.TemperedLanglandsDatum.{max v w} n)
    (π π' : letI := T.topology; SmoothRep.{0,v,max v w} ℂ (GeneralLinear n E.Carrier))
    (hπ : t.IsLanglandsHead π) (hπ' : t'.IsLanglandsHead π') (he : Nonempty (π ≅ π'))
    (A : letI := T.topology; ∀ i, SigmaIntertwiner σ (t.shape.size i) (t.blocks i).representation)
    (A' : letI := T.topology; ∀ i, SigmaIntertwiner σ (t'.shape.size i) (t'.blocks i).representation)
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
      [μ.IsMulLeftInvariant],
      ∃ c : ℂ, c ≠ 0 ∧
        twistedDistribution μ t'.standardModule.representation (temperedStandard_isAdmissible T t')
            (temperedStandardSigmaIntertwiner T hModule σ t' A').toLinearMap =
          c • twistedDistribution μ t.standardModule.representation (temperedStandard_isAdmissible T t)
            (temperedStandardSigmaIntertwiner T hModule σ t A).toLinearMap := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _
  obtain ⟨a, h, hdata⟩ := glRegularLanglandsDataUniqueness.{v,w} p E T n hn t t' π π'
    hπ.isLanglandsQuotient hπ'.isLanglandsQuotient he
  have hequiv (z : Fin t.shape.length → ℂˣ) (_ : ∀ k, ‖(z k : ℂ)‖ = 1) :=
    nonempty_normalizedProduct_twist_equiv_of_matching T t.shape t'.shape a h t.blocks t'.blocks
      (fun i => (hdata i).2) z
  obtain ⟨c, hc, hcomp⟩ := blockFamilyTrace_comparison T hModule σ t.shape t'.shape id a.symm
    t.blocks t'.blocks t.irreducible t.tempered t'.irreducible t'.tempered A A' hd hσ hequiv μ
  refine ⟨c, hc, ?_⟩
  rw [standardTrace_eq_standardFamilyTrace T hModule σ t μ A,
    standardTrace_eq_standardFamilyTrace T hModule σ t' μ A']
  have hz : (fun j => realPowerParameter T (t'.exponent j)) =
      fun j => (fun i => realPowerParameter T (t.exponent i)) (a.symm j) := by
    funext j
    show realPowerParameter T (t'.exponent j) = realPowerParameter T (t.exponent (a.symm j))
    rw [(hdata (a.symm j)).1, OrderIso.apply_symm_apply]
  have hc' := hcomp (fun i => realPowerParameter T (t.exponent i))
  change unramifiedFamilyTrace σ t'.shape a.symm _ A' _ _ _ μ _ _ =
    c • unramifiedFamilyTrace σ t.shape id _ A _ _ _ μ _ _ at hc'
  rw [hz]
  exact hc'

theorem blockFamilyTrace_reindex {n : ℕ} (B : BlockShape n) {r : ℕ} (g : Fin B.length → Fin r)
    (δ : letI := T.topology; ∀ i, SmoothRep.{0,v,w} ℂ (GeneralLinear (B.size i) E.Carrier))
    (hδ : letI := T.topology; ∀ i, IsAdmissible (δ i).representation)
    (A : letI := T.topology; ∀ i, SigmaIntertwiner σ (B.size i) (δ i).representation) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant] (z : Fin r → ℂˣ),
      blockFamilyTrace T hModule σ B g δ hδ A μ z =
        blockFamilyTrace T hModule σ B id δ hδ A μ (fun i => z (g i)) := by
  intros
  rfl

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unramified family of irreducible tempered σ-stable blocks at real exponents is a
nonzero multiple of the σ-stable standard trace of the datum obtained by grouping equal
exponents. The grouping map and the unitary-point equivalences are retained. -/
theorem exists_standardTrace_eq_smul_blockFamilyTrace {n : ℕ} (hn : 0 < n) (L : BlockShape n)
    (δ : letI := T.topology; ∀ k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (L.size k) E.Carrier))
    (hirr : letI := T.topology; ∀ k, (δ k).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ k, T.IsTempered (δ k).representation)
    (A : letI := T.topology; ∀ k, SigmaIntertwiner σ (L.size k) (δ k).representation)
    {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1) (x : Fin L.length → ℝ) :
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
      ∃ (t : T.TemperedLanglandsDatum.{max v w} n)
        (A' : ∀ j, SigmaIntertwiner σ (t.shape.size j) (t.blocks j).representation)
        (q : Fin L.length → Fin t.shape.length) (c : ℂ), c ≠ 0 ∧
        (∀ k, x k = t.exponent (q k)) ∧
        (∀ z : Fin t.shape.length → ℂˣ, (∀ j, ‖(z j : ℂ)‖ = 1) →
          letI := T.generalLinearTopologicalGroup n
          Nonempty ((T.normalizedProductInduced L (fun k =>
              twist (determinantUnramified E.Carrier (L.size k) (z (q k)))
                (δ k).representation)).Equiv
            (T.normalizedProductInduced t.shape (fun j =>
              twist (determinantUnramified E.Carrier (t.shape.size j) (z j))
                (t.blocks j).representation)))) ∧
        blockFamilyTrace T hModule σ L id δ (fun k => (htemp k).isAdmissible) A μ
            (fun k => realPowerParameter T (x k)) =
          c • twistedDistribution μ t.standardModule.representation
            (temperedStandard_isAdmissible T t)
            (temperedStandardSigmaIntertwiner T hModule σ t A').toLinearMap := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _
  have hδ (k : Fin L.length) : IsAdmissible (δ k).representation := (htemp k).isAdmissible
  choose cA hcA using fun k => exists_twistingEquiv_normalizingScalar
    (entrywiseAut σ (L.size k)) (hδ k) (hirr k) (A k) hd (entrywiseAut_pow_eq_one σ hσ _)
  let An (k : Fin L.length) := scaleTwistingEquiv (entrywiseAut σ (L.size k)) (cA k) (A k)
  obtain ⟨t, A', q, -, hx, hunit⟩ :=
    exists_groupedTemperedDatum T σ hModule hn L δ hirr htemp An hσ hcA x
  obtain ⟨c, hc, hcomp⟩ := blockFamilyTrace_comparison T hModule σ L t.shape q id δ t.blocks
    hirr htemp t.irreducible t.tempered A A' hd hσ hunit μ
  refine ⟨t, A', q, c⁻¹, inv_ne_zero hc, hx, hunit, ?_⟩
  have h1 := hcomp (fun j => realPowerParameter T (t.exponent j))
  have hxz : (fun k => realPowerParameter T (x k)) =
      fun k => (fun j => realPowerParameter T (t.exponent j)) (q k) := by
    funext k
    show realPowerParameter T (x k) = realPowerParameter T (t.exponent (q k))
    rw [hx k]
  rw [standardTrace_eq_standardFamilyTrace T hModule σ t μ A']
  change _ = c⁻¹ • blockFamilyTrace T hModule σ t.shape id t.blocks
    (fun j => (t.tempered j).isAdmissible) A' μ (fun j => realPowerParameter T (t.exponent j))
  rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul, hxz,
    blockFamilyTrace_reindex T hModule σ L q δ]

end Padic

end Langlands.BaseChange
