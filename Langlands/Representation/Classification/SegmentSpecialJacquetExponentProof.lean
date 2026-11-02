import Langlands.Representation.Classification.SegmentSpecialJacquetExponentStatement
import Langlands.Representation.Classification.SegmentQuotientJacquetFactorsProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Exponents.DescendingIntervalBlockScalarProof
import Langlands.Representation.Exponents.ScalarGeneralizedEigencharacterProof

/-!
# Norms of normalized Jacquet exponents of weak segment special quotients

The actual all-shape Jacquet factors, their central scalar characters and generic
scalar detection give the descending-interval formula without analytic hypotheses.
-/

noncomputable section

namespace Langlands

open scoped BigOperators

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem segmentScalarCharacter_eq_descendingInterval (ω : F.Carrierˣ →* ℂˣ)
    (r m K k : ℕ) (h : K + k ≤ m) :
    (ω * (T.determinantPowerCharacter r ((m - K - k : ℕ) : ℝ)).comp
      GeneralLinear.scalar) ^ k *
      (T.determinantPowerCharacter (k * r) (((k : ℝ) - 1) / 2)).comp
        GeneralLinear.scalar =
    ∏ j : Fin k, ω * (T.determinantPowerCharacter r
      ((m - 1 - (K + (j : ℕ)) : ℕ) : ℝ)).comp GeneralLinear.scalar := by
  rw [← T.prod_twistedScalarCharacter _ r k _
    (Classification.sum_fin_rev_val_real k)]
  apply Finset.prod_congr rfl
  intro j _
  have hj := j.isLt
  have he : m - 1 - (K + (j : ℕ)) = (m - K - k) + (k - 1 - (j : ℕ)) := by
    omega
  rw [he, Nat.cast_add]
  change (ω * (realPowerCharacter (T.determinantNorm r)
      ((m - K - k : ℕ) : ℝ)).comp GeneralLinear.scalar) *
      (realPowerCharacter (T.determinantNorm r)
        ((k - 1 - (j : ℕ) : ℕ) : ℝ)).comp GeneralLinear.scalar =
    ω * (realPowerCharacter (T.determinantNorm r)
      (((m - K - k : ℕ) : ℝ) + ((k - 1 - (j : ℕ) : ℕ) : ℝ))).comp
        GeneralLinear.scalar
  rw [realPowerCharacter_add, MonoidHom.mul_comp]
  exact mul_assoc ω _ _

private theorem hasScalarCharacter_intervalSegmentQuotient :
    letI := T.topology
    ∀ (Δ : T.Segment.{max uF uV, uF})
      (A : GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := Δ.rank))
      (ω : F.Carrierˣ →* ℂˣ),
      Δ.base.IsRepresentedBy A →
      Classification.HasScalarCharacter A.obj.representation GeneralLinear.scalar ω →
      ∀ (K k : ℕ) (hk : 0 < k), K + k ≤ Δ.length →
      let E : T.Segment.{max uF uV, uF} :=
        { base := Δ.member (Δ.length - K - k), length := k, length_pos := hk }
      ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear E.degree F.Carrier)),
      T.IsSegmentQuotient E π →
      Classification.HasScalarCharacter π.representation GeneralLinear.scalar
        (∏ j : Fin k, ω * (T.determinantPowerCharacter Δ.rank
          ((Δ.length - 1 - (K + (j : ℕ)) : ℕ) : ℝ)).comp
            GeneralLinear.scalar) := by
  let := T.topology
  intro Δ A ω hA hω K k hk hK E π hπ
  let s : ℝ := ((Δ.length - K - k : ℕ) : ℝ)
  let A' := GeneralLinear.SupercuspidalRep.twist
    (T.determinantPowerCharacter Δ.rank s)
    (T.isOpen_ker_determinantPowerCharacter Δ.rank s)
    (T.ker_determinant_le_ker_determinantPowerCharacter Δ.rank s) A
  have hA' : E.base.IsRepresentedBy A' := by
    exact congrArg (T.supercuspidalClassRealPowerTwist Δ.rank s) hA
  have hω' : Classification.HasScalarCharacter A'.obj.representation GeneralLinear.scalar
      (ω * (T.determinantPowerCharacter Δ.rank s).comp GeneralLinear.scalar) :=
    Classification.hasScalarCharacter_twist _ hω
  have hs := ((Classification.segmentConstituentCentralCharacter.{uF, max uF uV}
    F T E _ A' hA' hω').2.2 π (Or.inr hπ))
  change Classification.HasScalarCharacter π.representation GeneralLinear.scalar
    ((ω * (T.determinantPowerCharacter Δ.rank
      ((Δ.length - K - k : ℕ) : ℝ)).comp GeneralLinear.scalar) ^ k *
      (T.determinantPowerCharacter (k * Δ.rank) (((k : ℝ) - 1) / 2)).comp
        GeneralLinear.scalar) at hs
  rw [T.segmentScalarCharacter_eq_descendingInterval ω Δ.rank Δ.length K k hK] at hs
  exact hs

private theorem hasScalarCharacter_intervalSegmentQuotient_of_eq :
    letI := T.topology
    ∀ (Δ : T.Segment.{max uF uV, uF})
      (A : GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := Δ.rank))
      (ω : F.Carrierˣ →* ℂˣ),
      Δ.base.IsRepresentedBy A →
      Classification.HasScalarCharacter A.obj.representation GeneralLinear.scalar ω →
      ∀ (E : T.Segment.{max uF uV, uF}) (K k : ℕ) (_hk : 0 < k),
      K + k ≤ Δ.length →
      E.base = Δ.member (Δ.length - K - k) →
      E.length = k →
      ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear E.degree F.Carrier)),
      T.IsSegmentQuotient E π →
      Classification.HasScalarCharacter π.representation GeneralLinear.scalar
        (∏ j : Fin k, ω * (T.determinantPowerCharacter Δ.rank
          ((Δ.length - 1 - (K + (j : ℕ)) : ℕ) : ℝ)).comp
            GeneralLinear.scalar) := by
  let := T.topology
  intro Δ A ω hA hω E K k hk hK hb hl
  rcases E with ⟨base, length, length_pos⟩
  dsimp only at hb hl
  subst base
  subst length
  exact T.hasScalarCharacter_intervalSegmentQuotient Δ A ω hA hω K k hk hK

private theorem hasScalarCharacter_smooth_rank_transport :
    letI := T.topology
    ∀ {n n' : ℕ} (h : n = n')
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (c : F.Carrierˣ →* ℂˣ),
      Classification.HasScalarCharacter (h ▸ π).representation GeneralLinear.scalar c ↔
        Classification.HasScalarCharacter π.representation GeneralLinear.scalar c := by
  let := T.topology
  intro n n' h π c
  cases h
  rfl

private theorem norm_generalizedEigencharacter_of_blockTensor_equiv {n : ℕ}
    (B : GeneralLinear.BlockShape n) {W : Type uV} [AddCommGroup W] [Module ℂ W]
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {ρ : Representation ℂ (B.Levi F.Carrier) W}
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
    (e : ρ.Equiv (B.blockTensor σ))
    (ω : F.Carrierˣ →* ℂˣ) (r m : ℕ) (k : Fin B.length → ℕ)
    (hk : ∑ i, k i = m)
    (hσ : ∀ i, Classification.HasScalarCharacter (σ i) GeneralLinear.scalar
      (∏ j : Fin (k i), ω * (T.determinantPowerCharacter r
        ((m - 1 - ((∑ l : Fin B.length with l < i, k l) + (j : ℕ)) : ℕ) : ℝ)).comp
          GeneralLinear.scalar))
    {χ : (Fin B.length → F.Carrierˣ) →* ℂˣ}
    (hχ : IsGeneralizedEigencharacter (ρ.comp (B.blockScalarLevi F.Carrier)) χ)
    (a : Fin B.length → F.Carrierˣ) :
    ‖(χ a : ℂ)‖ =
      ∏ i, (‖(ω (a i) : ℂ)‖ ^ k i *
        T.normalizedAbs (a i : F.Carrier) ^
          ((r : ℝ) * (k i : ℝ) *
            (((2 * (m : ℝ) - (k i : ℝ) - 1) / 2) -
              ((∑ j : Fin B.length with j < i, k j : ℕ) : ℝ)))) := by
  have hs := B.hasScalarCharacter_blockTensor_splitCentre F.Carrier hσ
  have hρ := hs.of_injective e.toIntertwiningMap e.toLinearEquiv.injective
  rw [scalar_generalized_character_eq hρ hχ]
  exact T.norm_prod_blockDescendingIntervalScalarCharacter ω r m k hk a

end PadicField.TopologicalData

namespace Classification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every generalized normalized Jacquet exponent of a weak segment special quotient
has the norm of its successive descending intervals. -/
theorem segmentSpecialJacquetExponentNormFormula :
    SegmentSpecialJacquetExponentNormFormula.{uF, uV} F T := by
  let := T.topology
  intro Δ A ω hA hω π hπ B χ hχ
  rcases segmentQuotientJacquetFactors.{uF, uV} F T Δ π hπ B with hz |
    ⟨k, Γ, hdeg, σ, hk, hsize, hsum, hlength, hbase, hquot, ⟨e⟩⟩
  · let := hz
    obtain ⟨l, v, hv, -⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ.2
    exact (hv (Subsingleton.elim _ _)).elim
  · refine ⟨k, hk, hsize, hsum, ?_⟩
    intro a
    refine T.norm_generalizedEigencharacter_of_blockTensor_equiv B e
      ω Δ.rank Δ.length k hsum ?_ hχ.2 a
    intro i
    have hs := T.hasScalarCharacter_intervalSegmentQuotient_of_eq
      Δ A ω hA hω (Γ i) (∑ j : Fin B.length with j < i, k j) (k i) (hk i)
      ((prefix_add_le_sum k i).trans_eq hsum) (hbase i) (hlength i)
      ((hdeg i).symm ▸ σ i) (hquot i)
    exact (T.hasScalarCharacter_smooth_rank_transport
      (hdeg i).symm (σ i) _).mp hs

end Classification

end Langlands
