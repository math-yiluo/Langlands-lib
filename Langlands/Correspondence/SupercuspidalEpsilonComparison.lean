import Langlands.Correspondence.SupercuspidalSpecification

/-!
# Common epsilon tests for supercuspidal families

The comparison relation retains actual JPSS factor witnesses. The local
converse theorem, rank-one agreement and surjectivity remain explicit inputs
to the rank induction. Arithmetic comparisons here use one fixed system.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA uV uW

open LocalFactor LocalFactor.CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- In the rank order used by local converse, the symmetric class relation is
the published candidate-first class relation. -/
theorem isSupercuspidalPairEpsilonFactor_iff_class
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    {r n : ℕ} (hnr : n ≤ r)
    (π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r))
    (τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n))
    (e : ℂˣ × ℤ) :
    IsSupercuspidalPairEpsilonFactor F ψ ν π τ e ↔
      RankinSelberg.IsClassEpsilonFactor F ψ ν π τ e := by
  let := F.canonicalTopologicalData.topology
  refine Quotient.inductionOn₂ π τ ?_
  intro A B
  change RankinSelberg.IsPadicSymmetricEpsilonFactor F ψ ν
      A.obj.representation B.obj.representation e ↔
    RankinSelberg.IsPadicPairEpsilonFactor F ψ ν
      A.obj.representation B.obj.representation e
  exact RankinSelberg.isPadicSymmetricEpsilonFactor_of_le hnr

/-- At a fixed reciprocity family and local-constant system, two arithmetic
epsilon certificates for the same pair have the same coefficient and exponent.
The existence clauses in the relation provide the common comparison datum. -/
theorem IsArithmeticPairEpsilonFactor.unique
    {eC : ReciprocityFamily F} {ε : NonabelianSystem.Assignment.{uF, uV} F}
    {hε : NonabelianSystem.IsSystem F eC ε}
    {ψ : NontrivialAdditiveCharacter F} {X Y : LocalPairClass.{uF, uP} F}
    {c c' : ℂˣ} {m m' : ℤ}
    (h : IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y c m)
    (h' : IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y c' m') :
    c = c' ∧ m = m' := by
  obtain ⟨ψ', μ, A, B, hd, hA, hB⟩ := h.1
  obtain ⟨Φ⟩ := h.2.1
  have heq (s : ℂ) :
      RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality c m s =
        RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality
          c' m' s :=
    (h.2.2 ψ' μ A B hd hA hB Φ s).symm.trans
      (h'.2.2 ψ' μ A B hd hA hB Φ s)
  have hq := F.canonicalTopologicalData.residueCardinality_gt_one
  have hU : (Set.range (fun t : ℝ =>
      RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality t)).Infinite :=
    Set.infinite_range_of_injective (RankinSelberg.spectralPoint_ofReal_injective hq)
  apply RankinSelberg.unitMonomial_eq_of_infinite hU
  · rintro x ⟨t, rfl⟩
    exact RankinSelberg.spectralPoint_ne_zero hq _
  · rintro x ⟨t, rfl⟩
    exact heq t

/-- For every candidate rank at least two and each strictly lower positive
test rank, the corresponding image pairs possess one common epsilon value.
Both families are evaluated on the same actual irreducible Weil classes. -/
def CommonSupercuspidalEpsilonFactors
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (c d : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ (k r : ℕ), r ≤ k →
    ∀ (σ : IrreducibleWeilClass.{uF, uP} F (k + 1).succPNat)
      (τ : IrreducibleWeilClass.{uF, uP} F r.succPNat),
      ∃ e : ℂˣ × ℤ,
        IsSupercuspidalPairEpsilonFactor F ψ ν
          (c (k + 1).succPNat σ) (c r.succPNat τ) e ∧
        IsSupercuspidalPairEpsilonFactor F ψ ν
          (d (k + 1).succPNat σ) (d r.succPNat τ) e

/-- Separate pair-factor compatibility for one fixed arithmetic system supplies
the common epsilon tests, at every supplied self-dual measure. -/
theorem commonSupercuspidalEpsilonFactors_of_pairFactors
    {eC : ReciprocityFamily F} {ε : NonabelianSystem.Assignment.{uF, uP} F}
    {hε : NonabelianSystem.IsSystem F eC ε}
    {c d : SupercuspidalMap.{uF, uP, uA} F}
    (hc : SupercuspidalPairFactorCompatibility F eC ε hε c)
    (hd : SupercuspidalPairFactorCompatibility F eC ε hε d)
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν) :
    CommonSupercuspidalEpsilonFactors F ψ ν c d := by
  intro k r hr σ τ
  obtain ⟨e, he, ha⟩ := ((hc ψ (k + 1) r σ τ).2 ν hν).2
  obtain ⟨e', he', ha'⟩ := ((hd ψ (k + 1) r σ τ).2 ν hν).2
  have heq : e = e' := Prod.ext (ha.unique F ha').1 (ha.unique F ha').2
  exact ⟨e, he, heq ▸ he'⟩

/-- Henniart's rank induction on the actual correspondence domains. Local
converse is an input. Agreement in rank one, surjectivity of the first family,
and common lower-rank epsilon tests identify the whole families. -/
theorem supercuspidalMap_eq_of_commonEpsilonFactors
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA})
    (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {c d : SupercuspidalMap.{uF, uP, uA} F}
    (hOne : c 1 = d 1)
    (hsurj : ∀ n, Function.Surjective (c n))
    (hcommon : CommonSupercuspidalEpsilonFactors F ψ ν.val c d) :
    c = d := by
  have heq : ∀ n : ℕ, c n.succPNat = d n.succPNat := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => exact hOne
      | succ k =>
        funext σ
        apply hconverse p F ψ ν k
        intro r hr τ
        obtain ⟨τW, rfl⟩ := hsurj r.succPNat τ
        obtain ⟨e, hc, hd⟩ := hcommon k r hr σ τW
        have htest : c r.succPNat τW = d r.succPNat τW :=
          congrFun (ih r (by omega)) τW
        refine ⟨e,
          (isSupercuspidalPairEpsilonFactor_iff_class F ψ ν.val (by omega) _ _ e).mp hc,
          ?_⟩
        rw [htest]
        exact (isSupercuspidalPairEpsilonFactor_iff_class F ψ ν.val
          (by omega) _ _ e).mp hd
  funext n
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt n.pos)
  have hn : n = m.succPNat := Subtype.ext hm
  rw [hn]
  exact heq m

/-- The fixed-system specialization consumes the existing separate L/epsilon
compatibility predicate; its epsilon component supplies all induction tests. -/
theorem supercuspidalMap_eq_of_pairFactors
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA})
    (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {eC : ReciprocityFamily F} {ε : NonabelianSystem.Assignment.{uF, uP} F}
    {hε : NonabelianSystem.IsSystem F eC ε}
    {c d : SupercuspidalMap.{uF, uP, uA} F}
    (hOne : c 1 = d 1)
    (hsurj : ∀ n, Function.Surjective (c n))
    (hc : SupercuspidalPairFactorCompatibility F eC ε hε c)
    (hd : SupercuspidalPairFactorCompatibility F eC ε hε d) :
    c = d :=
  supercuspidalMap_eq_of_commonEpsilonFactors F hconverse ψ ν hOne hsurj
    (commonSupercuspidalEpsilonFactors_of_pairFactors F hc hd ψ ν.val ν.property)

end Langlands.Correspondence
