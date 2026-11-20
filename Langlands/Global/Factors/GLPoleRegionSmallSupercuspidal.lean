import Langlands.Global.Factors.GLPoleRegionSupercuspidal
import Langlands.Representation.Classification.SegmentTensorStabilizerProof
import Langlands.Representation.Classification.UnlinkedSocleProductIrreducibilityProof
import Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionProof
import Langlands.Representation.RankinSelberg.SquareIntegrablePoleOrderCharacterizationReduction
import Langlands.Representation.RankinSelberg.SquareIntegrableDataLFactorProof
import Langlands.Representation.RankinSelberg.SegmentHeadFactorProof
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.RankinSelberg.HighlyRamified.PairInductionGenericity
import Langlands.Representation.RankinSelberg.HighlyRamified.ShellExpansion
import Langlands.Representation.RankinSelberg.AdjacentRankClearingKernel
import Langlands.Representation.RankinSelberg.LanglandsPairLFactorExistenceProof
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Classification.SegmentHeadProductContragredient
import Langlands.Correspondence.AutomorphicActualGamma

/-!
# The GL pole region with a supercuspidal second member

Over the canonical realization of a p-adic field, let `π` be generic irreducible and
`σ` irreducible supercuspidal, of any ranks. The p-adic L-polynomial `P` of `π × σ`
and the L-polynomial `Pd` of `π^∨ × σ^∨` have no reflected common zero. A common
zero gives poles at `s = 0` of the L-functions of `π` and of `π^∨` against unramified
twists of `σ` and `σ^∨`. Through the Zelevinsky datum of `π` and the pole-order
formula for products of segment heads, these poles give segments `Δ_i`, `Δ_j` of `π`
with `Δ_j` beginning at the unit twist of the end of `Δ_i`. A segment cannot begin
at the unit twist of its own end, so `i ≠ j`, and the two segments are juxtaposed,
which genericity excludes. The wrapper
`hasNoReflectedCommonZero_of_supercuspidal_le` restates this for the pair relations
used by the unequal-rank case of `GLPairPoleRegionStatement`.
-/

noncomputable section

namespace Langlands.Global.GLPoleRegion

universe uF uV uW

open PadicField.TopologicalData Classification

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- If the beginning of `Γ` is the unit twist of the end of `Δ`, the members of `Γ`
continue those of `Δ`. -/
theorem member_eq_of_base_eq_last_twist_one {Δ Γ : T.Segment.{uV, uF}}
    (h : Γ.base = Δ.last.twist 1) (i : ℕ) :
    Γ.member i = Δ.member (Δ.length + i) := by
  have hl := Δ.length_pos
  simp only [Segment.member, Segment.last, h, CuspidalDatum.twist_twist]
  congr 1
  have : ((Δ.length - 1 : ℕ) : ℝ) = (Δ.length : ℝ) - 1 := by
    rw [Nat.cast_sub hl]; simp
  rw [this]; push_cast; ring

/-- A segment beginning at the unit twist of the end of `Δ` is juxtaposed to `Δ`, so
the two are linked. -/
theorem isLinked_of_base_eq_last_twist_one {Δ Γ : T.Segment.{uV, uF}}
    (h : Γ.base = Δ.last.twist 1) : Δ.IsLinked Γ := by
  have hm := member_eq_of_base_eq_last_twist_one h
  have hinj := segment_member_injective F T Δ
  have hl := Δ.length_pos
  refine ⟨?_, ?_, ?_⟩
  · intro hsub
    obtain ⟨i, _, hi⟩ := hsub (Δ.member_mem_support hl)
    rw [hm] at hi
    have := hinj hi
    omega
  · intro hsub
    obtain ⟨i, hi, he⟩ := hsub (Γ.member_mem_support Γ.length_pos)
    rw [hm] at he
    have := hinj he
    omega
  · refine ⟨⟨Δ.base, Δ.length + Γ.length, by omega⟩, ?_⟩
    ext ρ
    constructor
    · rintro ⟨i, hi, rfl⟩
      change i < Δ.length + Γ.length at hi
      by_cases hi' : i < Δ.length
      · exact Or.inl ⟨i, hi', rfl⟩
      · refine Or.inr ⟨i - Δ.length, by omega, ?_⟩
        rw [hm, Nat.add_sub_cancel' (by omega)]
        rfl
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨i, by change i < Δ.length + Γ.length; omega, rfl⟩
      · refine ⟨Δ.length + i, by change Δ.length + i < Δ.length + Γ.length; omega, ?_⟩
        rw [hm]
        rfl

/-- No segment begins at the unit twist of its own end. -/
theorem base_ne_last_twist_one (Δ : T.Segment.{uV, uF}) : Δ.base ≠ Δ.last.twist 1 := by
  intro h
  have h0 := member_eq_of_base_eq_last_twist_one h 0
  rw [Segment.member_zero, add_zero] at h0
  have := segment_member_injective F T Δ ((Segment.member_zero Δ).trans h0)
  have hl := Δ.length_pos
  omega

section PoleAtOne

open RankinSelberg Classification.CuspidalProductContragredient Polynomial
open CategoryTheory GeneralLinear Whittaker HarmonicAnalysis

variable {F' : PadicField.{uF} p}

/-- Rank transports along two equalities compose. -/
theorem castRank_castRank (T' : F'.TopologicalData) {a b c : ℕ} (h₁ : a = b) (h₂ : b = c)
    (h₃ : a = c)
    (A : letI := T'.topology; SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear a F'.Carrier)) :
    T'.castRank h₂ (T'.castRank h₁ A) = T'.castRank h₃ A := by
  subst h₁ h₂
  rfl

/-- An isomorphism out of a rank transport gives an equivalence into the reverse
transport. -/
theorem nonempty_equiv_cast_of_iso (T' : F'.TopologicalData) {a b : ℕ} (h : a = b)
    (X : letI := T'.topology; SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear a F'.Carrier))
    (Y : letI := T'.topology; SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear b F'.Carrier))
    (f : letI := T'.topology; (h ▸ X) ≅ Y) :
    letI := T'.topology
    Nonempty (X.representation.Equiv (h.symm ▸ Y).representation) := by
  let := T'.topology
  subst h
  exact ⟨SmoothRep.equivOfIso f⟩

/-- **A pole at `s = 0` against a supercuspidal representation.** Let `π` be an
irreducible quotient of a precedence-ordered product of segment heads `St(Δ_i)` of
`GL_(n+1)(F)`, and let `A` represent the cuspidal datum `c` of `GL_(t+1)(F)`. If an
L-polynomial `P` of `π × A` vanishes at `1`, some `Δ_i` ends at the dual `c^∨`. -/
theorem exists_last_eq_dualDatum_of_eval_one_eq_zero
    {ψ : letI := F'.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F'.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F'.canonicalTopologicalData ψ) {n t : ℕ}
    (π : letI := F'.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (n + 1) F'.Carrier))
    (d : F'.canonicalTopologicalData.SegmentProductDatum.{max uF uV, uF} (n + 1))
    (hd : d.IsLanglandsQuotient π)
    (c : F'.canonicalTopologicalData.CuspidalDatum.{max uF uV, uF}) (hc : c.rank = t + 1)
    (A : letI := F'.canonicalTopologicalData.topology
      SupercuspidalRep.{uF, max uF uV} (F := F'.Carrier) (n := c.rank))
    (hA : c.IsRepresentedBy A) {P : ℂ[X]}
    (hP : IsLanglandsPairLPolynomial.{uF, uV, uV} F' ψ ν.val π
      (F'.canonicalTopologicalData.castRank hc A.obj) P)
    (h1 : P.eval 1 = 0) :
    ∃ i, (d.segments i).last = dualDatum c := by
  classical
  let Fr := F'.canonicalTopologicalData
  let := Fr.topology
  obtain ⟨e, ⟨iso⟩, σ, hσ⟩ := Classification.orderedSegmentSquareIntegrableConversion.{uF, uV}
    F' Fr (n + 1) n.succ_pos d hd.1 hd.2.1
  have he : e.IsLanglandsQuotient π :=
    Classification.IsIrreducibleQuotient.of_equiv (SmoothRep.equivOfIso iso) hd.2.2
  have key : ∀ i k, σ i = k → ∃ h : (d.segments i).degree = e.shape.size k,
      Fr.IsSegmentHead (d.segments i) (h.symm ▸ e.blocks k) := by
    rintro i k rfl
    obtain ⟨h, ⟨f⟩⟩ := hσ i
    obtain ⟨g⟩ := nonempty_equiv_cast_of_iso Fr h _ _ f
    exact ⟨h, (hd.2.1 i).of_equiv g⟩
  let Δ : Fin e.shape.length → Fr.Segment.{max uF uV, uF} := fun k => d.segments (σ.symm k)
  have hΔ : ∀ k, ∃ h : (Δ k).degree = e.shape.size k,
      Fr.IsSegmentHead (Δ k) (h.symm ▸ e.blocks k) :=
    fun k => key (σ.symm k) k (σ.apply_symm_apply k)
  let D := Fr.singletonSegment c
  have hD : D.degree = t + 1 := (Fr.singletonSegment_degree c).trans hc
  have hσD := HighlyRamified.singletonSegment_isSegmentHead c A hA
  obtain ⟨ρ, hρ, hesi, ⟨eρ⟩⟩ :=
    exists_isEssentiallySquareIntegrable_equiv_of_isSegmentHead.{uF, uV, uV} D hD _ hσD
  rw [castRank_castRank Fr _ hD hc] at eρ
  have hρ' : Representation.IsIrreducible (Fr.castRank hc A.obj).representation :=
    (isIrreducible_iff_of_equiv eρ).mpr hρ
  have hesi' : Fr.IsEssentiallySquareIntegrable (Fr.castRank hc A.obj).representation :=
    (Fr.isEssentiallySquareIntegrable_iff_of_equiv eρ).mpr hesi
  have hW : ∀ (r : ℕ) (A : SupercuspidalRep.{uF, max uF uV} (F := F'.Carrier) (n := r + 1)),
      IsOfWhittakerType r (standardCharacter ψ r) A.obj.representation := fun r A =>
    isOfWhittakerType_of_supercuspidalKirillov
      Langlands.supercuspidalKirillov.{uF, max uF uV} A.property.2 A.property.1
  have hpole := lPolynomialPoleOrderAtZero_eq_poleLinkCount ν
    squareIntegrableDataLFactor.{uF, uV, uV} segmentHeadLFactor supercuspidalEqualRankLFactor
    supercuspidalUnequalRankLFactor hW π e he Δ hΔ (Fr.castRank hc A.obj) hρ' hesi' D _ hσD hD
    ⟨by rw [castRank_castRank Fr _ hD hc]; exact Representation.Equiv.refl _⟩ hP
  have hpos : 0 < poleLinkCount (Finset.univ.val.map Δ) D.dual := by
    rw [← hpole, lPolynomialPoleOrderAtZero]
    exact (rootMultiplicity_pos hP.ne_zero).mpr h1
  rw [poleLinkCount_map_univ] at hpos
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  have hlink : SegmentPoleLink (Δ k) D.dual := by
    by_contra h
    simp [h] at hk
  obtain ⟨-, j, hj, hjeq⟩ := hlink
  have hj0 : j = 0 := by
    have : j < 1 := hj
    omega
  subst hj0
  refine ⟨σ.symm k, ?_⟩
  change (Δ k).last = _
  rw [← hjeq, Segment.member_zero]
  change dualDatum (c.twist ((1 - 1 : ℕ) : ℝ)) = dualDatum c
  simp

/-- A p-adic pair L-polynomial of two generic representations is their L-polynomial
through the Langlands classification. -/
theorem isLanglandsPairLPolynomial_of_isPadicSymmetricLPolynomial
    {ψ : letI := F'.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F'.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F'.canonicalTopologicalData ψ) {r t : ℕ}
    (π : letI := F'.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F'.Carrier))
    (σ : letI := F'.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F'.Carrier))
    (hπ : letI := F'.canonicalTopologicalData.topology; IsGeneric ψ r π.representation)
    (hσ : letI := F'.canonicalTopologicalData.topology; IsGeneric ψ t σ.representation)
    {P : ℂ[X]}
    (hP : letI := F'.canonicalTopologicalData.topology
      IsPadicSymmetricLPolynomial F' ψ ν.val π.representation σ.representation P) :
    IsLanglandsPairLPolynomial.{uF, uV, uW} F' ψ ν.val π σ P := by
  let := F'.canonicalTopologicalData.topology
  obtain ⟨Q, hQ⟩ := langlandsPairLFactorExistence.{uF, uV, uW} p F' ψ ν r t π σ hπ.1 hπ.2.1
    hσ.1 hσ.2.1
  rwa [(hQ.isPadicSymmetricLPolynomial hπ hσ).unique hP] at hQ

/-- **Zelevinsky data of a generic representation and of its smooth dual.** A generic
irreducible `π` of `GL_(r+1)(F)` is the Langlands quotient of a product of segment
heads with unlinked segments, and its smooth dual is that of the dual datum. -/
theorem exists_unlinked_isLanglandsQuotient_dual
    {ψ : letI := F'.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F'.Carrier}
    {r : ℕ}
    (π : letI := F'.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F'.Carrier))
    (hπ : letI := F'.canonicalTopologicalData.topology; IsGeneric ψ r π.representation) :
    ∃ d : F'.canonicalTopologicalData.SegmentProductDatum.{max uF uV, uF} (r + 1),
      d.multisegment.IsUnlinked ∧ d.IsLanglandsQuotient π ∧
        (letI := F'.canonicalTopologicalData.topology;
          letI := F'.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1);
          d.dual.IsLanglandsQuotient π.contragredient) := by
  let Fr := F'.canonicalTopologicalData
  let := Fr.topology
  let := Fr.generalLinearTopologicalGroup (r + 1)
  obtain ⟨d, hh, hu, ⟨a⟩⟩ := (Classification.genericSegmentProductExhaustion.{uF, uV} Fr ψ r π).mp hπ
  have hmem : ∀ i, d.segments i ∈ d.multisegment := fun i => by
    simp [SegmentProductDatum.multisegment]
  have ho : d.IsPrecedenceOrdered := by
    intro i j _ hp
    exact hu _ (hmem i) _ (hmem j) hp.isLinked
  have hq : d.IsLanglandsQuotient π := by
    refine ⟨ho, hh, hπ.1, ?_⟩
    exact ⟨(SmoothRep.equivOfIso a.symm).toIntertwiningMap,
      (SmoothRep.equivOfIso a.symm).surjective⟩
  refine ⟨d, hu, hq, ?_⟩
  have hod : d.dual.IsPrecedenceOrdered := by
    intro i j _ hp
    exact hu _ (hmem i) _ (hmem j)
      (Classification.UnlinkedSocleProduct.isLinked_of_dual (F := F') (T := Fr) hp.isLinked)
  have hirr : Representation.IsIrreducible π.contragredient.representation :=
    (isGeneric_contragredient hπ).1
  let b : π.contragredient ≅ d.dual.induced :=
    (SmoothRep.contragredientFunctor.mapIso a.op).symm ≪≫ d.contragredientInducedIso hh
  refine ⟨hod, hh.dual, hirr, ?_⟩
  exact ⟨(SmoothRep.equivOfIso b.symm).toIntertwiningMap,
    (SmoothRep.equivOfIso b.symm).surjective⟩

/-- **A supercuspidal member: no reflected common zero.** Let `π` be generic for `ψ`
on `GL_(r+1)(F)` and `σ` irreducible supercuspidal on `GL_(t+1)(F)`, of any ranks.
The L-polynomial `P` of `π × σ` and the L-polynomial `Pd` of `π^∨ × σ^∨` have no
reflected common zero. A common zero `z` with `z = q^(-u)` gives a pole at `s = 0`
of `L(s, π × σ|det|^u)` and of `L(s, π^∨ × σ^∨|det|^(1-u))`. The first makes a
segment `Δ_i` of `π` end at `(σ|det|^u)^∨ = σ^∨|det|^(-u)`. The second makes the
base of a segment `Δ_j` represent `(σ|det|^u)^∨ ⊗ |det| = σ^∨|det|^(1-u)`, the unit
twist of the end of `Δ_i`. No segment begins at the unit twist of its own end, so
`i ≠ j`, and then `Δ_i` and `Δ_j` are juxtaposed, against genericity. -/
theorem hasNoReflectedCommonZero_of_supercuspidal_right
    {ψ : letI := F'.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F'.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F'.canonicalTopologicalData ψ) {r t : ℕ}
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F'.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F'.Carrier) W}
    (hπ : letI := F'.canonicalTopologicalData.topology; IsGeneric ψ r π)
    (hiσ : Representation.IsIrreducible σ)
    (hscσ : letI := F'.canonicalTopologicalData.topology; IsSupercuspidal σ)
    {P Pd : ℂ[X]}
    (hP : letI := F'.canonicalTopologicalData.topology
      IsPadicSymmetricLPolynomial F' ψ ν.val π σ P)
    (hPd : letI := F'.canonicalTopologicalData.topology;
      letI := F'.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1);
      letI := F'.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1);
      IsPadicSymmetricLPolynomial F' ψ ν.val (smoothContragredient π)
        (smoothContragredient σ) Pd) :
    HasNoReflectedCommonZero F'.canonicalTopologicalData.residueCardinality P Pd := by
  classical
  let Fr := F'.canonicalTopologicalData
  let := Fr.topology
  let := Fr.generalLinearTopologicalGroup (r + 1)
  let := Fr.generalLinearTopologicalGroup (t + 1)
  have hq : 1 < Fr.residueCardinality := Fr.residueCardinality_gt_one
  rintro z hz ⟨h1, h2⟩
  -- `π` as a bundled representation with carrier in `max uF uV`
  let π₀ := SmoothRep.of π hπ.2.1.1
  let πs : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F'.Carrier) :=
    SmoothRep.universeLift.{uF} π₀
  let eπ : π.Equiv πs.representation := SmoothRep.universeLiftEquiv.{uF} π₀
  have hπs : IsGeneric ψ r πs.representation := (Whittaker.isGeneric_iff_of_equiv ψ r eπ).1 hπ
  obtain ⟨d, hun, hd, hdd⟩ := exists_unlinked_isLanglandsQuotient_dual (ψ := ψ) πs hπs
  -- the test representation `σ|det|^u`, with `q^(-u) = z`
  obtain ⟨u, hzu, -⟩ := HighlyRamified.exists_spectralPoint_eq hq hz
  let χ := Fr.determinantComplexPower (t + 1) u
  have hχ : IsOpen (χ.ker : Set (Langlands.GeneralLinear (t + 1) F'.Carrier)) :=
    Fr.isOpen_ker_determinantComplexPower (t + 1) u
  have hdetχ : (determinant : Langlands.GeneralLinear (t + 1) F'.Carrier →* F'.Carrierˣ).ker ≤
      χ.ker :=
    Fr.ker_determinant_le_ker_determinantUnramifiedCharacter (t + 1) _
  let ρ := Langlands.twist χ σ
  have hiρ : Representation.IsIrreducible ρ := (isIrreducible_twist_iff χ σ).2 hiσ
  have hscρ : IsSupercuspidal ρ := (isSupercuspidal_twist_iff χ hχ hdetχ σ).2 hscσ
  obtain ⟨A₀, hA₀, ⟨eA⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, uW, max uF uV} p F' Fr (t + 1)
      (SmoothRep.of ρ hscρ.1.1) hiρ
  let A : SupercuspidalRep.{uF, max uF uV} (F := F'.Carrier) (n := t + 1) :=
    ⟨A₀, hA₀, isSupercuspidal_of_equiv eA hscρ⟩
  let c : Fr.CuspidalDatum.{max uF uV, uF} := ⟨t + 1, t.succ_pos, A.isoClass⟩
  have hA : c.IsRepresentedBy A := rfl
  have hW : ∀ (m : ℕ) (B : SupercuspidalRep.{uF, max uF uV} (F := F'.Carrier) (n := m + 1)),
      IsGeneric ψ m B.obj.representation := fun m B => by
    have htype : IsOfWhittakerType m (standardCharacter ψ m) B.obj.representation :=
      isOfWhittakerType_of_supercuspidalKirillov
        Langlands.supercuspidalKirillov.{uF, max uF uV} B.property.2 B.property.1
    exact ⟨B.property.1, htype.1, htype.exists_ne_zero⟩
  -- the pole of `L(s, π × σ|det|^u)` at `s = 0`
  have hPρ := Padic.symmetricLPolynomial_determinantComplexPower F' ψ ν π σ u P hP
  have hPA : IsPadicSymmetricLPolynomial F' ψ ν.val πs.representation A.obj.representation
      (P.comp (C (spectralPoint Fr.residueCardinality u) * X)) :=
    (IsPadicSymmetricLPolynomial.congr_equiv eπ eA).1 hPρ
  have hLA := isLanglandsPairLPolynomial_of_isPadicSymmetricLPolynomial.{uF, uV, uV}
    ν πs A.obj hπs (hW t A) hPA
  obtain ⟨i, hi⟩ := exists_last_eq_dualDatum_of_eval_one_eq_zero ν πs d hd c rfl A hA hLA
    (by simp [eval_comp, hzu, h1])
  -- the pole of `L(s, π^∨ × σ^∨|det|^(1-u))` at `s = 0`
  have hPdρ := Padic.symmetricLPolynomial_determinantComplexPower F' ψ ν
    (smoothContragredient π) (smoothContragredient σ) (1 - u) Pd hPd
  let A' := twistedDualRep Fr 1 A
  have hchar : Fr.determinantPowerCharacter (t + 1) 1 * χ⁻¹ =
      Fr.determinantComplexPower (t + 1) (1 - u) := by
    have h₁ := Fr.determinantComplexPower_ofReal (t + 1) 1
    rw [Complex.ofReal_one] at h₁
    rw [sub_eq_add_neg, Fr.determinantComplexPower_add, Fr.determinantComplexPower_neg, h₁]
  have e₁ : (Langlands.twist (Fr.determinantComplexPower (t + 1) (1 - u))
      (smoothContragredient σ)).Equiv
      (Langlands.twist (Fr.determinantPowerCharacter (t + 1) 1)
        (smoothContragredient A₀.representation)) := by
    rw [← hchar, ← twist_twist]
    exact twistEquiv _ ((smoothContragredientTwistEquiv χ σ hχ).symm.trans
      (smoothContragredientEquiv eA).symm)
  have hPA' : IsPadicSymmetricLPolynomial F' ψ ν.val πs.contragredient.representation
      A'.obj.representation
      (Pd.comp (C (spectralPoint Fr.residueCardinality (1 - u)) * X)) :=
    (IsPadicSymmetricLPolynomial.congr_equiv (smoothContragredientEquiv eπ).symm e₁).1 hPdρ
  have hLA' := isLanglandsPairLPolynomial_of_isPadicSymmetricLPolynomial.{uF, uV, uV}
    ν πs.contragredient A'.obj (isGeneric_contragredient hπs) (hW t A') hPA'
  have hz' : spectralPoint Fr.residueCardinality (1 - u) = (Fr.residueCardinality : ℂ)⁻¹ * z⁻¹ := by
    rw [spectralPoint_one_sub hq, hzu, div_eq_mul_inv]
  obtain ⟨j, hj⟩ := exists_last_eq_dualDatum_of_eval_one_eq_zero ν πs.contragredient d.dual hdd
    ((dualDatum c).twist 1) rfl A' (twistedDualRep_represents 1 hA) hLA'
    (by simp only [eval_comp, eval_mul, eval_C, eval_X, mul_one, hz']; exact h2)
  -- `Δ_j` begins where `Δ_i` ends, twisted by `|det|`
  have hj' : (d.segments j).base = (d.segments i).last.twist 1 := by
    have h := congrArg dualDatum hj
    change dualDatum ((d.segments j).dual.last) = _ at h
    rw [Segment.dual_last, dualDatum_dualDatum, dualDatum_twist, dualDatum_dualDatum] at h
    rw [h, hi, dualDatum_twist, neg_neg]
  by_cases hij : i = j
  · subst hij
    exact base_ne_last_twist_one _ hj'
  · have hmem : ∀ k, d.segments k ∈ d.multisegment := fun k => by
      simp [SegmentProductDatum.multisegment]
    exact hun _ (hmem i) _ (hmem j) (isLinked_of_base_eq_last_twist_one hj')

/-- **Unequal rank, `σ` supercuspidal of the smaller rank**, in the form produced by
the reduction lemma `isPadicPairLPolynomial_of_unequalRank`: `P` is the p-adic pair
L-polynomial of `(π, σ)` for `ψ` and `Pd` that of `(π^ι, σ^ι)` for `ψ⁻¹`, both at the
self-dual measure of `ψ`. -/
theorem hasNoReflectedCommonZero_of_supercuspidal_le
    {ψ : letI := F'.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F'.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F'.canonicalTopologicalData ψ) {r t : ℕ}
    (htr : t ≤ r) {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F'.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F'.Carrier) W}
    (hπ : letI := F'.canonicalTopologicalData.topology; IsGeneric ψ r π)
    (hiσ : Representation.IsIrreducible σ)
    (hscσ : letI := F'.canonicalTopologicalData.topology; IsSupercuspidal σ)
    {P Pd : ℂ[X]}
    (hP : IsPadicPairLPolynomial F' ψ ν.val π σ P)
    (hPd : letI := F'.canonicalTopologicalData.topology
      letI := F'.canonicalTopologicalData.valuativeRel
      letI := F'.canonicalTopologicalData.localField
      IsPadicPairLPolynomial F' (ψ.scale (-1)) ν.val (inverseTransposePullback π)
        (inverseTransposePullback σ) Pd) :
    HasNoReflectedCommonZero F'.canonicalTopologicalData.residueCardinality P Pd := by
  let := F'.canonicalTopologicalData.topology
  let := F'.canonicalTopologicalData.valuativeRel
  let := F'.canonicalTopologicalData.localField
  let := F'.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
  let := F'.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  refine hasNoReflectedCommonZero_of_supercuspidal_right ν hπ hiσ hscσ
    ((isPadicSymmetricLPolynomial_of_le htr).2 hP) ?_
  have h := ((isPadicSymmetricLPolynomial_of_le htr).2 hPd).characterChange (-1)
  have hs : (ψ.scale (-1)).scale (-1) = ψ := by
    rw [UnitaryAdditiveCharacter.scale_scale]
    simp
  rw [hs] at h
  exact (isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient F' hπ.2.1
    hscσ.1 hπ.1 hiσ).1 h

end PoleAtOne

end Langlands.Global.GLPoleRegion
