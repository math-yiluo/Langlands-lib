import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Classification.SegmentSocleProductData
import Langlands.Representation.Classification.SupercuspidalSupport

/-! Actual one-term segment socles and cuspidal-product data. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData)

/-- A cuspidal class viewed as a segment with one member. -/
def singletonSegment (ρ : CuspidalDatum.{uV, uF} T) : Segment.{uV, uF} T :=
  ⟨ρ, 1, Nat.one_pos⟩

@[simp] theorem singletonSegment_degree (ρ : CuspidalDatum.{uV, uF} T) :
    (T.singletonSegment ρ).degree = ρ.rank := Nat.one_mul _

/-- Transport a smooth representation along an exact equality of GL ranks. -/
def castRank {r s : ℕ} (h : r = s)
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear s F.Carrier) := h ▸ A

/-- Exact rank transport agrees with the published matrix reindexing. -/
def castRankEquiv {r s : ℕ} (h : r = s)
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    Representation.Equiv (A.representation.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom)
      (T.castRank h A).representation := by
  letI := T.topology
  subst s
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ A) ?_
  intro g
  have hg : (GeneralLinear.reindex (R := F.Carrier) (finCongr (rfl : r = r))).symm g = g := by
    apply Units.ext
    ext a b
    rfl
  change A.representation ((GeneralLinear.reindex (R := F.Carrier)
    (finCongr (rfl : r = r))).symm g) = A.representation g
  rw [hg]

/-- Actual normalized induction of a one-term segment is its sole factor. -/
def singletonSegmentInducedEquiv {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    (T.segmentInduced A 1 hr).representation.Equiv
      (T.castRank (Nat.one_mul r).symm A).representation := by
  letI := T.topology
  let B := GeneralLinear.BlockShape.uniform 1 r hr
  let i0 : Fin B.length := ⟨0, Nat.one_pos⟩
  let τ := fun i => (T.segmentFactors A 1 hr i).representation
  let e := T.singleBlockNormalizedProductEquiv B rfl τ
    (fun i => (T.segmentFactors A 1 hr i).isSmooth) i0
  have hτ : τ i0 = A.representation := by
    change twist (T.determinantPowerCharacter r ((0 : ℕ) : ℝ)) A.representation = A.representation
    rw [Nat.cast_zero]
    rw [show T.determinantPowerCharacter r 0 = 1 from realPowerCharacter_zero _]
    exact twist_one _
  have hτe : (τ i0).Equiv A.representation := equivOfRepresentationEq hτ
  refine e.trans ?_
  refine (Representation.Equiv.mk hτe.toLinearEquiv ?_).trans
    (T.castRankEquiv (Nat.one_mul r).symm A)
  intro g
  exact hτe.isIntertwining' _

/-- Rank transport preserves irreducibility. -/
theorem isIrreducible_castRank {r s : ℕ} (h : r = s)
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) :
    letI := T.topology; (T.castRank h A).IsIrreducible := by
  subst s
  exact hA

/-- A saturated supercuspidal representative is the actual strong socle
of the induced representation of its one-term segment. -/
theorem singletonSegment_isSegmentSocle (ρ : CuspidalDatum.{max uF uV, uF} T)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) :
    T.IsSegmentSocle (T.singletonSegment ρ)
      (T.castRank (T.singletonSegment_degree ρ).symm A.obj) := by
  let := T.topology
  let e := T.singletonSegmentInducedEquiv ρ.rank_pos A.obj
  have hB := T.isIrreducible_castRank (T.singletonSegment_degree ρ).symm A.obj A.property.1
  refine ⟨A, hA, ?_⟩
  exact Classification.IsIrreducibleSubrepresentation.isIrreducibleSocle_of_irreducible
    ⟨hB, e.symm.toIntertwiningMap, e.symm.injective⟩
    ((Weil.IsomorphismInvariance.irreducible_iff e).mpr hB)

/-- Changing the numerical presentation of every block by exact rank equality
commutes with actual normalized product induction. -/
def normalizedProductRankCastIso {k n : ℕ} (r s : Fin k → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hrs : ∀ i, r i = s i) (hrsum : ∑ i, r i = n) (hssum : ∑ i, s i = n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (r i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor ⟨k, s, hs, hssum⟩).obj
      (fun i => T.castRank (hrs i) (A i)) ≅
    (T.normalizedProductInductionFunctor ⟨k, r, hr, hrsum⟩).obj A := by
  cases funext hrs
  exact Iso.refl _

namespace SegmentProductDatum

/-- Keep a cuspidal product's actual factors, viewed as one-term segment socles. -/
def ofCuspidals {k n : ℕ} (ρ : Fin k → CuspidalDatum.{max uF uV, uF} T)
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := (ρ i).rank)) : SegmentProductDatum.{max uF uV, uF} T n where
  length := k
  segments i := T.singletonSegment (ρ i)
  degree_sum := by simpa only [singletonSegment_degree] using h
  blocks i := T.castRank (T.singletonSegment_degree (ρ i)).symm (A i).obj

/-- Every supplied actual block is the strong socle of its one-term segment. -/
theorem ofCuspidals_hasSegmentSocles {k n : ℕ}
    (ρ : Fin k → CuspidalDatum.{max uF uV, uF} T) (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i)) :
    (ofCuspidals T ρ h A).HasSegmentSocles :=
  fun i => T.singletonSegment_isSegmentSocle (ρ i) (A i) (hA i)

/-- The resulting normalized product is the original cuspidal product,
with every factor and its order retained. -/
def ofCuspidalsInducedIso {k n : ℕ}
    (ρ : Fin k → CuspidalDatum.{max uF uV, uF} T) (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    (ofCuspidals T ρ h A).induced ≅ T.cuspidalProductInduced ρ h A :=
  T.normalizedProductRankCastIso (fun i => (ρ i).rank)
    (fun i => (T.singletonSegment (ρ i)).degree)
    (fun i => (ρ i).rank_pos) (fun i => (T.singletonSegment (ρ i)).degree_pos)
    (fun i => (T.singletonSegment_degree (ρ i)).symm) h
    (by simpa only [singletonSegment_degree] using h) (fun i => (A i).obj)

end SegmentProductDatum

/-- An actual cuspidal-product embedding supplies actual segment-socle product
data with the same full-product embedding. No order is asserted. -/
theorem IsCuspidalSubrepresentation.exists_segmentSocleProduct {k n : ℕ}
    {ρ : Fin k → CuspidalDatum.{max uF uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : T.IsCuspidalSubrepresentation ρ π) :
    ∃ d : SegmentProductDatum.{max uF uV, uF} T n, d.HasSegmentSocles ∧
      (letI := T.topology;
        Classification.IsIrreducibleSubrepresentation d.induced.representation π.representation) := by
  let := T.topology
  obtain ⟨h, A, hA, hsub⟩ := hπ
  refine ⟨SegmentProductDatum.ofCuspidals T ρ h A,
    SegmentProductDatum.ofCuspidals_hasSegmentSocles T ρ h A hA, ?_⟩
  exact hsub.of_equiv (SmoothRep.equivOfIso
    (SegmentProductDatum.ofCuspidalsInducedIso T ρ h A).symm)

end Langlands.PadicField.TopologicalData
