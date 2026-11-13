import Langlands.Representation.Classification.TadicSpehHeads
import Langlands.Representation.Classification.TadicSocleIndependence
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Classification.TadicRectangleCombinatorics

/-!
# Unitarity of `⟨a(n,1)^ρ⟩`

For a unitary cuspidal `ρ`, the special head `L(Δ[n]^ρ)` of the centered segment is the
Zelevinsky socle of the one-element segments `a(n,1)^ρ` (it is the socle of the decreasing
product of the cuspidal twists), and it is square-integrable and unitarizable. Hence every
Zelevinsky socle of `a(n,1)^ρ` is unitarizable.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.TadicBlockSteinberg

open PadicField.TopologicalData GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The one-element segments `{ν^(n-1-i) ρ₀}`, `i < n`, in decreasing order. -/
def downSegments (ρ₀ : T.CuspidalDatum.{max uF uV, uF}) (n : ℕ) (i : Fin n) :
    T.Segment.{max uF uV, uF} :=
  T.singletonSegment (ρ₀.twist ((n - 1 - (i : ℕ) : ℕ) : ℝ))

theorem downSegments_degree_sum (ρ₀ : T.CuspidalDatum.{max uF uV, uF}) (n : ℕ) :
    ∑ i, (downSegments ρ₀ n i).degree = n * ρ₀.rank := by
  simp [downSegments, singletonSegment_degree]

/-- The decreasing product of the one-element segment socles, as a segment-product datum. -/
def downDatum (ρ₀ : T.CuspidalDatum.{max uF uV, uF})
    (A : letI := T.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ρ₀.rank)) (n : ℕ) :
    T.SegmentProductDatum.{max uF uV, uF} (n * ρ₀.rank) where
  length := n
  segments := downSegments ρ₀ n
  degree_sum := downSegments_degree_sum ρ₀ n
  blocks i := T.castRank (T.singletonSegment_degree _).symm
    (T.segmentFactorsDown A.obj n ρ₀.rank_pos i)

/-- The datum's product is the decreasing segment induction. -/
def downDatumInducedIso (ρ₀ : T.CuspidalDatum.{max uF uV, uF})
    (A : letI := T.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ρ₀.rank)) (n : ℕ) :
    letI := T.topology
    (downDatum ρ₀ A n).induced ≅ T.segmentInducedDown A.obj n ρ₀.rank_pos :=
  T.normalizedProductRankCastIso (fun _ => ρ₀.rank)
    (fun i => (downSegments ρ₀ n i).degree) (fun _ => ρ₀.rank_pos)
    (fun i => (downSegments ρ₀ n i).degree_pos)
    (fun i => (T.singletonSegment_degree _).symm) (by simp) (downSegments_degree_sum ρ₀ n)
    (T.segmentFactorsDown A.obj n ρ₀.rank_pos)

theorem downDatum_hasSegmentSocles (ρ₀ : T.CuspidalDatum.{max uF uV, uF})
    (A : letI := T.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ρ₀.rank))
    (hA : ρ₀.IsRepresentedBy A) (n : ℕ) : (downDatum ρ₀ A n).HasSegmentSocles := by
  let := T.topology
  intro i
  let k : ℝ := ((n - 1 - (i : ℕ) : ℕ) : ℝ)
  let Ak := SupercuspidalRep.twist (T.determinantPowerCharacter ρ₀.rank k)
    (T.isOpen_ker_determinantPowerCharacter ρ₀.rank k)
    (T.ker_determinant_le_ker_determinantPowerCharacter ρ₀.rank k) A
  have hAk : (ρ₀.twist k).IsRepresentedBy Ak := by
    change Ak.isoClass = T.supercuspidalClassRealPowerTwist ρ₀.rank k ρ₀.cls
    rw [← show A.isoClass = ρ₀.cls from hA]
    rfl
  exact T.singletonSegment_isSegmentSocle (ρ₀.twist k) Ak hAk

theorem downDatum_isPrecedenceOrdered (ρ₀ : T.CuspidalDatum.{max uF uV, uF})
    (A : letI := T.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ρ₀.rank)) (n : ℕ) :
    (downDatum ρ₀ A n).IsPrecedenceOrdered := by
  intro i j hij hprec
  obtain ⟨-, k, hk, hb⟩ := hprec
  change ρ₀.twist ((n - 1 - (j : ℕ) : ℕ) : ℝ) =
    (ρ₀.twist ((n - 1 - (i : ℕ) : ℕ) : ℝ)).twist (k : ℝ) at hb
  rw [CuspidalDatum.twist_twist] at hb
  have h := cuspidalDatum_twist_injective ρ₀ hb
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  have hij' : (i : ℕ) < j := hij
  have h2 : n - 1 - (j : ℕ) = k + (n - 1 - (i : ℕ)) := by exact_mod_cast h
  omega

theorem downDatum_multisegment (ρ : T.CuspidalDatum.{max uF uV, uF})
    {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := (tadicCenteredSegment ρ n hn 0).base.rank)) :
    (downDatum (tadicCenteredSegment ρ n hn 0).base A n).multisegment =
      tadicMultisegment ρ n 1 Nat.one_pos := by
  classical
  have hseg : ∀ i : Fin n, downSegments (tadicCenteredSegment ρ n hn 0).base n i =
      tadicCenteredSegment ρ 1 Nat.one_pos
        (((n - 1 - (i : ℕ) : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) := by
    intro i
    simp only [downSegments, tadicCenteredSegment, singletonSegment, CuspidalDatum.twist_twist]
    congr 2
    push_cast
    ring
  have hinj : ∀ x y : ℝ, tadicCenteredSegment ρ 1 Nat.one_pos x =
      tadicCenteredSegment ρ 1 Nat.one_pos y → x = y :=
    fun x y h => tadicCenteredSegment_injective ρ Nat.one_pos h
  apply (Multiset.Nodup.ext ?_ ?_).mpr
  · intro Δ
    simp only [SegmentProductDatum.multisegment, Multiset.mem_coe, List.mem_ofFn,
      tadicMultisegment, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      have hi : (i : ℕ) < n := i.isLt
      refine ⟨n - 1 - (i : ℕ), by omega, ?_⟩
      exact (hseg i).symm
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨n - 1 - j, show n - 1 - j < n by omega⟩, ?_⟩
      change downSegments _ n ⟨n - 1 - j, _⟩ = _
      rw [hseg]
      congr 1
      simp only
      rw [show n - 1 - (n - 1 - j) = j by omega]
  · simp only [SegmentProductDatum.multisegment, Multiset.coe_nodup]
    refine List.nodup_ofFn.mpr fun i i' h => ?_
    change downSegments _ n i = downSegments _ n i' at h
    rw [hseg, hseg] at h
    have h' := hinj _ _ h
    have hi : (i : ℕ) < n := i.isLt
    have hi' : (i' : ℕ) < n := i'.isLt
    have h2 : n - 1 - (i : ℕ) = n - 1 - (i' : ℕ) := by
      have : ((n - 1 - (i : ℕ) : ℕ) : ℝ) = ((n - 1 - (i' : ℕ) : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    exact Fin.ext (by omega)
  · refine Multiset.Nodup.map_on (fun x _ y _ h => ?_) (Multiset.nodup_range n)
    have := hinj _ _ h
    exact_mod_cast (show (x : ℝ) = y by linarith)

/-- **The Steinberg-type representation.** The special head `L(Δ[n]^ρ)` is a Zelevinsky
socle of `a(n,1)^ρ`. -/
theorem isZelevinskySocle_tadicSegmentHead (ρ : T.CuspidalDatum.{max uF uV, uF})
    {n : ℕ} (hn : 0 < n) :
    (tadicMultisegment ρ n 1 Nat.one_pos).IsZelevinskySocle (tadicSegmentHead ρ hn) := by
  let := T.topology
  let Δ := tadicCenteredSegment ρ n hn 0
  obtain ⟨A, hA⟩ := Quotient.exists_rep Δ.base.cls
  have hAΔ : Δ.base.IsRepresentedBy A := hA
  have hsoc := (isSegmentHead_tadicSegmentHead ρ hn).isIrreducibleSocle_down A hAΔ
  refine ⟨downDatum Δ.base A n, downDatum_multisegment ρ hn A,
    downDatum_isPrecedenceOrdered Δ.base A n, downDatum_hasSegmentSocles Δ.base A hAΔ n, ?_⟩
  exact hsoc.of_equiv (SmoothRep.equivOfIso (downDatumInducedIso Δ.base A n).symm)

/-- **Unitarity of `⟨a(n,1)^ρ⟩`** for unitary `ρ` (Tadić §2.14, from square-integrability). -/
theorem isUnitarizable_of_isZelevinskySocle_one {ρ : T.CuspidalDatum.{max uF uV, uF}}
    (hρ : ρ.IsUnitary) {n : ℕ} (hn : 0 < n) {N : ℕ}
    {σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hσ : (tadicMultisegment ρ n 1 Nat.one_pos).IsZelevinskySocle σ) :
    letI := T.topology; IsUnitarizable σ.representation := by
  let := T.topology
  have hN : N = n * ρ.rank := by
    rw [tadicMultisegment_rank_eq_of_isZelevinskySocle hσ, Nat.one_mul]
  subst hN
  have hδ := isZelevinskySocle_tadicSegmentHead ρ hn
  obtain ⟨e⟩ := nonempty_iso_of_isZelevinskySocle hσ hδ
  have hu := (tadicSpehDatum_isDiscreteSeries ρ hn hρ 1 Nat.one_pos).2.1
  exact (isUnitarizable_iff_of_equiv (SmoothRep.equivOfIso e)).mpr hu

end Langlands.Classification.TadicBlockSteinberg
