import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof

/-! Actual transports from length-one special blocks to untwisted products. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData)

private theorem supercuspidal_castRank {r s : ℕ} (h : r = s)
    (A : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (hA : letI := T.topology; GeneralLinear.IsSupercuspidal A.representation) :
    letI := T.topology
    GeneralLinear.IsSupercuspidal (T.castRank h A).representation := by
  subst s
  exact hA

/-- If every exponent vanishes, the entire twisted normalized product is
isomorphic to the normalized product of the same original blocks. -/
def twistedProductInducedZeroIso {n : ℕ} (B : GeneralLinear.BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ) (hs : ∀ i, s i = 0) :
    letI := T.topology
    T.twistedProductInduced B A s ≅ (T.normalizedProductInductionFunctor B).obj A := by
  letI := T.topology
  apply (T.normalizedProductInductionFunctor B).mapIso
  apply Pi.isoMk
  intro i
  change T.segmentFactor (A i) (s i) ≅ A i
  rw [hs i]
  exact Langlands.Classification.segmentFactorZeroIso F T (A i)

/-- A quotient of a length-one segment is equivalent to the original
supercuspidal representative, with only the required exact rank transport. -/
theorem IsSegmentQuotient.exists_equiv_castRank_of_length_one
    {Δ : T.Segment.{uV,uF}}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentQuotient Δ π) (h1 : Δ.length = 1) :
    letI := T.topology
    ∃ A : GeneralLinear.SupercuspidalRep.{uF,uV}
        (F := F.Carrier) (n := Δ.rank),
      Δ.base.IsRepresentedBy A ∧ ∀ h : Δ.rank = Δ.degree,
        Nonempty ((T.castRank h A.obj).representation.Equiv π.representation) := by
  let := T.topology
  obtain ⟨ρ, m, hm⟩ := Δ
  change m = 1 at h1
  subst m
  obtain ⟨A, hA, hirr, q, hq⟩ := hπ
  refine ⟨A, hA, fun h => ?_⟩
  let e := T.singletonSegmentInducedEquiv ρ.rank_pos A.obj
  let g := q.comp e.symm.toIntertwiningMap
  have hg : Function.Surjective g := hq.comp e.symm.surjective
  have := T.isIrreducible_castRank (Nat.one_mul ρ.rank).symm A.obj A.property.1
  have : Nontrivial π := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hirr.bot_ne_top
    ext v
    simp [Subsingleton.elim v 0]
  have hinj : Function.Injective g := by
    rcases Representation.IsIrreducible.injective_or_eq_zero g with hinj | hzero
    · exact hinj
    · exfalso
      obtain ⟨w, hw⟩ := exists_ne (0 : π)
      obtain ⟨v, hv⟩ := hg w
      apply hw
      rw [← hv, hzero]
      rfl
  exact ⟨Representation.IntertwiningMap.ofBijective g ⟨hinj, hg⟩⟩

/-- In particular, a length-one special quotient is itself supercuspidal
on its supplied carrier and action. -/
theorem IsSegmentQuotient.supercuspidal_of_length_one
    {Δ : T.Segment.{uV,uF}}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentQuotient Δ π) (h1 : Δ.length = 1) :
    letI := T.topology
    π.IsIrreducible ∧ GeneralLinear.IsSupercuspidal π.representation := by
  let := T.topology
  have hirr : π.IsIrreducible := by
    obtain ⟨A, hA, hirr, q, hq⟩ := hπ
    exact hirr
  have hr : Δ.rank = Δ.degree := by
    change Δ.rank = Δ.length * Δ.rank
    rw [h1, one_mul]
  obtain ⟨A, hA, he⟩ := hπ.exists_equiv_castRank_of_length_one T h1
  have hsc := supercuspidal_castRank T hr A.obj A.property.2
  exact ⟨hirr, GeneralLinear.isSupercuspidal_of_equiv (he hr).some hsc⟩

end Langlands.PadicField.TopologicalData
