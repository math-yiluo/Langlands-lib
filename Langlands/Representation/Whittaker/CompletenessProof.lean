import Langlands.Representation.Whittaker.CompletenessStatement
import Langlands.Representation.Whittaker.CompletenessOrthogonality
import Langlands.Representation.Whittaker.CompletenessCut
import Langlands.Representation.Whittaker.CompletenessTwistFiniteness
import Langlands.Representation.RankinSelberg.SupercuspidalProductCompletenessProof

/-!
# Completeness of Whittaker functions (proof)

Jacquet and Shalika 1985, Lemma (3.2): a function `H` on `GL_(n+1)(F)` with
`H(ug) = ψ_N(u)⁻¹ H(g)`, smooth and compactly supported modulo `N`, orthogonal to every
Whittaker function of every irreducible generic representation, vanishes.

The proof reduces the statement to the published completeness against normalized products
of supercuspidals (`supercuspidalProductCompleteness`, for the character `ψ⁻¹`). Orthogonality
to every such product is proved by strong induction on the number of linked pairs of
its supercuspidal blocks. With no linked pair the product is irreducible and generic. Otherwise
the blocks after a cut separating a linked pair are twisted by `|det|^u`; for real `u ≠ 0` near
`0` the twisted product has fewer linked pairs, and the deformation of Whittaker functions of
JPSS 1983, Section (4.5), passes to `u = 0`.
-/

noncomputable section

namespace Langlands.Whittaker.CompletenessProof

open MeasureTheory HarmonicAnalysis GeneralLinear RankinSelberg Filter
open CompletenessOrthogonality CompletenessCut
open scoped _root_.Topology

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance completenessProofTopologicalSpace : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance completenessProofValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance completenessProofIsNonarchimedeanLocalField :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

section Induction

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {t k : ℕ} (m : Fin k → ℕ)
  (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The products of the two parts of a cut of irreducible supercuspidal blocks are of
Whittaker type. -/
theorem isOfWhittakerType_partProduct (C : Cut k)
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i)) (j : Fin 2) :
    IsOfWhittakerType (C.size m j) (standardCharacter ψ (C.size m j))
      (C.partProduct m F τ j) :=
  normalizedProductWhittakerType p F ψ (C.size m j) (C.length j) (fun l => m (C.index j l))
    (C.sum_eq_size_add_one m j) (fun l => τ (C.index j l)) fun _ =>
      isOfWhittakerType_of_supercuspidalKirillov supercuspidalKirillov (hsc _) (hirr _)

variable [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  [OpensMeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  {H : WhittakerFunctions ψ t} (hH : IsCompactWhittakerTestFunction ψ t H)
  (μ : Measure (LeftUnipotentQuotient t F.Carrier)) [IsFiniteMeasureOnCompacts μ]

omit [OpensMeasurableSpace (LeftUnipotentQuotient t F.Carrier)] [IsFiniteMeasureOnCompacts μ] in
/-- Orthogonality to the cut product with its tail twisted by `|det|^u` is orthogonality to
the deformed two-block representation of the tail and head products. -/
theorem orthogonal_cutTwist_iff (C : Cut k)
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hs : ∀ i, IsSmooth (τ i)) (u : ℝ) :
    Orthogonal ψ μ H (F.canonicalNormalizedProductInduced (succBlockShape m h)
        (C.cutTwist m F τ u)) ↔
      Orthogonal ψ μ H (twoBlockDeformedInduced F (C.size m) (C.sum_size m h)
        (C.partProduct m F τ) (u : ℂ)) :=
  (C.cutEquiv m F τ h hs u).elim fun E => orthogonal_iff_of_equiv E

include hH in
/-- Orthogonality to the irreducible normalized products of irreducible supercuspidal blocks
gives orthogonality to all of them. The proof is by strong induction on the number of linked
pairs of blocks. -/
theorem orthogonal_of_irreducible
    (hbase : ∀ τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i),
      (∀ i, IsSmooth (τ i)) → (∀ i, Representation.IsIrreducible (τ i)) →
      (∀ i, GeneralLinear.IsSupercuspidal (τ i)) →
      Representation.IsIrreducible (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) →
      Orthogonal ψ μ H (F.canonicalNormalizedProductInduced (succBlockShape m h) τ))
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hs : ∀ i, IsSmooth (τ i)) (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i)) :
    Orthogonal ψ μ H (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) := by
  suffices key : ∀ N, ∀ (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier)
      (W i)) (hs : ∀ i, IsSmooth (τ i)) (hirr : ∀ i, Representation.IsIrreducible (τ i))
      (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i)),
      linkedCount (blockDatum τ hs hirr hsc) = N →
        Orthogonal ψ μ H (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) from
    key _ τ hs hirr hsc rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro τ hs hirr hsc hN
  by_cases h0 : linkedCount (blockDatum τ hs hirr hsc) = 0
  · exact hbase τ hs hirr hsc
      (isIrreducible_canonicalNormalizedProductInduced_of_unlinked m h τ hs hirr hsc
        ((linkedCount_eq_zero_iff _).mp h0))
  obtain ⟨j, a, b, hab, hl⟩ := exists_crossing_of_linkedCount_ne_zero _ h0
  have hjk : j.val + 1 < k := by
    have ha := a.isLt
    have hb := b.isLt
    by_cases hja : j < a
    · have := Fin.lt_def.mp hja
      omega
    · have hjb : j < b := by
        by_contra hjb
        exact hab (iff_of_false hja hjb)
      have := Fin.lt_def.mp hjb
      omega
  obtain ⟨C, hC⟩ : ∃ C : Cut k, C.c = j.val + 1 := ⟨⟨j.val + 1, Nat.succ_pos _, hjk⟩, rfl⟩
  let S : Fin k → Prop := fun i => C.c ≤ i.val
  let hS : DecidablePred S := fun i => Nat.decLe _ _
  have hSiff : ∀ i, S i ↔ j < i := fun i => by
    change C.c ≤ i.val ↔ j < i
    rw [hC, Fin.lt_def]
    omega
  have hcross : ∃ a b, ¬(S a ↔ S b) ∧
      blockDatum τ hs hirr hsc a = (blockDatum τ hs hirr hsc b).twist 1 :=
    ⟨a, b, by rwa [hSiff, hSiff], hl⟩
  have hσ := isOfWhittakerType_partProduct ψ m C τ hirr hsc
  -- orthogonality to the deformed two-block representations for `u ≠ 0` near `0`
  have hev : ∀ᶠ u : ℝ in 𝓝[≠] 0, Orthogonal ψ μ H
      (twoBlockDeformedInduced F (C.size m) (C.sum_size m h) (C.partProduct m F τ)
        (u : ℂ)) := by
    filter_upwards [eventually_linkedCount_twistOn_lt S _ hcross] with u hu
    let c : Fin k → ℝ := fun i => if S i then u else 0
    have hlt : linkedCount (blockDatum (twistBlocks c τ) (isSmooth_twistBlocks c τ hs)
        (isIrreducible_twistBlocks c τ hirr) (isSupercuspidal_twistBlocks c τ hsc)) < N := by
      rw [← hN]
      exact hu
    have ho := ih _ hlt (twistBlocks c τ) (isSmooth_twistBlocks c τ hs)
      (isIrreducible_twistBlocks c τ hirr) (isSupercuspidal_twistBlocks c τ hsc) rfl
    have hc : twistBlocks c τ = C.cutTwist m F τ u := rfl
    rw [hc] at ho
    exact (orthogonal_cutTwist_iff ψ m h μ C τ hs u).mp ho
  have hzero := orthogonal_twoBlockDeformedInduced_zero ψ (C.size m) (C.sum_size m h)
    (C.partProduct m F τ) hσ hH μ hev
  have hres := (orthogonal_cutTwist_iff ψ m h μ C τ hs 0).mpr
    (by simpa only [Complex.ofReal_zero] using hzero)
  rwa [C.cutTwist_zero] at hres

end Induction

section Assembly

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {t : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  [OpensMeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  (μ : Measure (LeftUnipotentQuotient t F.Carrier)) [IsFiniteMeasureOnCompacts μ]

/-- Under the hypotheses of Jacquet–Shalika 1985, Lemma (3.2), with the pairing taken for
an arbitrary measure `μ` finite on compacts, the function `H`, viewed as a Whittaker function
for `ψ⁻¹ = ψ.scale (-1)`, is orthogonal to every normalized product of irreducible
supercuspidal blocks. -/
theorem orthogonal_canonicalNormalizedProductInduced (H : InverseWhittakerFunctions ψ t)
    (hK : ∃ K : OpenSubgroup (Langlands.GeneralLinear (t + 1) F.Carrier),
      ∀ g k, k ∈ K → H.val (g * k) = H.val g)
    (hC : ∃ C : Set (Langlands.GeneralLinear (t + 1) F.Carrier), IsCompact C ∧
      ∀ g, H.val g ≠ 0 → ∃ u : upperUnipotent (t + 1) F.Carrier, ∃ c ∈ C, g = u.val * c)
    (hH : ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) V),
      IsGeneric ψ t π →
        ∀ (ℓ : glFunctionals ψ t π) (w : (coefficientModel π ℓ).toSubmodule),
          ∫ x, whittakerProductIntegrand ψ w.val H x ∂μ = 0)
    {k : ℕ} (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hs : ∀ i, IsSmooth (τ i)) (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i)) :
    Orthogonal (ψ.scale (-1)) μ (InducedTailIntermediate.inverseAsScaledStandard ψ H)
      (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) :=
  orthogonal_of_irreducible (ψ.scale (-1)) m h
    (isCompactWhittakerTestFunction_inverseAsScaledStandard ψ H hK hC) μ
    (fun τ' _ hirr' hsc' hprod => orthogonal_scale_neg_one_of_isGeneric ψ μ H hH _
      (isGeneric_canonicalNormalizedProductInduced ψ m h τ' hirr' hsc' hprod))
    τ hs hirr hsc

end Assembly

/-- Jacquet and Shalika 1985, Lemma (3.2): completeness of Whittaker functions. -/
theorem whittakerCompleteness : WhittakerCompletenessStatement.{uF, uV} := by
  intro p _ F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro ψ n
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro H hK hC hH g
  have hzero : InducedTailIntermediate.inverseAsScaledStandard ψ H = 0 :=
    supercuspidalProductCompleteness.{uF, uV} p F (ψ.scale (-1)) n
      (unipotentQuotientHaar F.Carrier n) (unipotentQuotientHaar_isCompatible F.Carrier n) _
      (isCompactWhittakerTestFunction_inverseAsScaledStandard ψ H hK hC)
      fun _ m h _ _ _ τ hs hirr hsc => orthogonal_iff_forall_coefficientModel.mp
        (orthogonal_canonicalNormalizedProductInduced ψ _ H hK hC hH m h τ hs hirr hsc)
  -- `inverseAsScaledStandard ψ H` has the underlying function of `H`
  have hg := congrArg (fun f : WhittakerFunctions (ψ.scale (-1)) n => f.val g) hzero
  simpa [InducedTailIntermediate.inverseAsScaledStandard] using hg

end Langlands.Whittaker.CompletenessProof
