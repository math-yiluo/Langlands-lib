import Langlands.Representation.Classification.SegmentReplacementInversions
import Langlands.Representation.Classification.SegmentHeadJacquetStatement
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

/-!
# Splitting the earlier segment of an overlapping precedence pair

If `Δ'` precedes `Δ` and the two overlap with intersection `J`, then `Δ'` is the
union of an initial piece `init`, juxtaposed with `Δ` and preceding it, and the
terminal piece `J`; moreover `init ∪ Δ` is the union `U` of `Δ` and `Δ'`.
-/

noncomputable section

namespace Langlands.Classification.QuotientHom

open PadicField.TopologicalData PadicField.TopologicalData.Segment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Ze80 4.6, step (2), segment part: for `Δ' = [a, b]` preceding `Δ = [c, d]` with
nonempty intersection `J = [c, b]`, the cut `q = c - a` splits `Δ'` into the initial
piece `[a, c - 1]` and the terminal piece `J`. -/
theorem exists_overlap_split {Δ Δ' U J : Segment.{uV, uF} T}
    (hp : Δ'.Precedes Δ)
    (hs : Δ.IsUnionIntersectionReplacement Δ' U (some J)) :
    ∃ (q : ℕ) (hq : 0 < q) (hqm : q < Δ'.length),
      Δ'.terminal q hqm = J ∧
      (Δ'.initial q hq).Precedes Δ ∧
      (Δ'.initial q hq).IsJuxtaposed Δ ∧
      Δ.IsUnionIntersectionReplacement (Δ'.initial q hq) U none ∧
      U.degree = Δ.degree + (Δ'.initial q hq).degree := by
  have hfree := cuspidalIntegralTwistFreeness.{uF, uV} F T
  have hs' : Δ'.IsUnionIntersectionReplacement Δ U (some J) :=
    ⟨hs.1.trans (Set.union_comm _ _), hs.2.trans (Set.inter_comm _ _)⟩
  obtain ⟨ρ, a, b, c, d, hΔ', hΔ, ⟨hac, -, hbd⟩, hU, hJ⟩ := hs'.coordinates hfree hp
  have hJ := hJ J rfl
  have hcb := hJ.lower_le_upper
  have hlen' := hΔ'.2
  set q := (c - a).toNat with hq_def
  have hqc : (q : ℤ) = c - a := Int.toNat_of_nonneg (by omega)
  have hq : 0 < q := by omega
  have hqm : q < Δ'.length := by omega
  have hbase : ∀ k : ℕ, Δ'.base.twist (k : ℝ) = ρ.twist ((a + k : ℤ) : ℝ) := by
    intro k
    rw [hΔ'.1, CuspidalDatum.twist_twist]
    congr 1
    push_cast
    ring
  have hterm : (Δ'.terminal q hqm).HasIntegralCoordinates ρ c b := by
    refine ⟨?_, ?_⟩
    · change Δ'.base.twist (q : ℝ) = _
      rw [hbase, hqc]
      congr 2
      ring
    · change b = c + ((Δ'.length - q : ℕ) : ℤ) - 1
      omega
  have hinit : (Δ'.initial q hq).HasIntegralCoordinates ρ a (c - 1) := by
    refine ⟨hΔ'.1, ?_⟩
    change c - 1 = a + (q : ℤ) - 1
    omega
  have hpre : (Δ'.initial q hq).Precedes Δ :=
    (hinit.precedes_iff hfree hΔ).mpr ⟨hac, by omega, by omega⟩
  have hdisj : Disjoint (Δ'.initial q hq).support Δ.support := by
    rw [Set.disjoint_left]
    intro σ hσ hσ'
    obtain ⟨k, -, hk, rfl⟩ := hinit.mem_support_iff.mp hσ
    have := (hΔ.twist_mem_support_iff hfree).mp hσ'
    omega
  have hUeq : U.support = Δ.support ∪ (Δ'.initial q hq).support := by
    rw [Set.union_comm, ← hinit.support_union_eq hΔ (by omega) (by omega) (by omega)]
    exact (hU.support_eq_iff hfree (ofIntegralInterval_hasIntegralCoordinates _ _ _ _)).mpr
      ⟨rfl, rfl⟩
  have hrank : ∀ {X : Segment.{uV, uF} T} {x y : ℤ}, X.HasIntegralCoordinates ρ x y →
      X.rank = ρ.rank := by
    intro X x y hX
    change X.base.rank = _
    rw [hX.1]
    rfl
  refine ⟨q, hq, hqm, ?_, hpre, ⟨hpre.isLinked, hdisj⟩, ⟨hUeq, ?_⟩, ?_⟩
  · exact eq_of_support_eq hfree ((hterm.support_eq_iff hfree hJ).mpr ⟨rfl, rfl⟩)
  · exact Set.disjoint_iff_inter_eq_empty.mp hdisj.symm
  · have hUl := hU.2
    have hΔl := hΔ.2
    have hlen : U.length = Δ.length + q := by omega
    change U.length * U.rank = Δ.length * Δ.rank + q * Δ'.rank
    rw [hrank hU, hrank hΔ, hrank hΔ', hlen, Nat.add_mul]

end Langlands.Classification.QuotientHom
