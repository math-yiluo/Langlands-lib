import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.Representation.Classification.MirabolicDerivativeContragredient
import Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement

/-!
# Proof of the mirabolic support shift for cuspidal products

BZ77 Lemma 4.7(b), mirabolic form. The highest-derivative pairing of BZ77 3.8 pairs
the highest derivative of `W ⊆ π|P` with the same derivative of `(ν π̃)|P`, which
gives a nonzero map from a derivative of `ν ρ̃_1 × ⋯ × ν ρ̃_r` to `σ̃`. The quotient
form of Lemma 4.7(a) for that product bounds the support of `σ̃`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.CuspidalProductMirabolicSupportShiftProof

open GeneralLinear PadicField.TopologicalData Derivative CuspidalProductContragredient
  MirabolicDerivativeContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

section Support

/-- A representation of `GL_0` has only the empty supercuspidal support. -/
theorem eq_zero_of_isSupercuspidalSupport {n : ℕ} (hn : n = 0)
    {σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset T.CuspidalDatum.{uV, uF}} (hs : T.IsSupercuspidalSupport σ s) : s = 0 := by
  obtain ⟨l, ρ, rfl, h, -⟩ := hs
  cases l with
  | zero => rfl
  | succ l =>
    have := Finset.single_le_sum (f := fun i => (ρ i).rank) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (0 : Fin (l + 1)))
    have := (ρ 0).rank_pos
    omega

/-- Lemma 4.7(a), quotient form, for supports: if `0 < k < n` and an irreducible `τ`
receives a nonzero morphism from the order-`k` derivative of a cuspidal product
`ρ_1 × ⋯ × ρ_r`, then every supercuspidal support of `τ` is contained in
`ρ_1 + ⋯ + ρ_r`. -/
theorem le_of_derivative_hom
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF}) {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i)) {k : ℕ} (hk : k ≤ n) (hk0 : 0 < k)
    (hkn : k < n)
    (τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (q : letI := T.topology
      (generalLinearDerivative T ψ n k hk).obj (T.cuspidalProductInduced ρ h A) ⟶ τ)
    (hq : letI := T.topology; SmoothRep.hom q ≠ 0)
    {s : Multiset T.CuspidalDatum.{uV, uF}} (hs : T.IsSupercuspidalSupport τ s) :
    s ≤ (List.ofFn ρ : Multiset T.CuspidalDatum.{uV, uF}) := by
  let := T.topology
  obtain ⟨l, ρ'', hcon, hle⟩ :=
    CuspidalProductDerivativeQuotientSupport.derivative_quotient_support.{uF, uV} T ψ hk hk0
      hkn ρ h A hA τ hτ (SmoothRep.hom q).toLinearMap
      (fun hz => hq (by ext v; exact LinearMap.congr_fun hz v))
      (fun g v => LinearMap.congr_fun ((SmoothRep.hom q).isIntertwining' g) v)
  have huniq := glSupercuspidalSupportUniqueness.{uV, uF} p F T (n - k) (by omega) τ hτ
    s (List.ofFn ρ'') hs ⟨l, ρ'', rfl, hcon⟩
  rw [huniq]
  exact hle

end Support

end Langlands.Classification.CuspidalProductMirabolicSupportShiftProof

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData Derivative CuspidalProductContragredient
  MirabolicDerivativeContragredient CuspidalProductMirabolicSupportShiftProof

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- BZ77 Lemma 4.7(b), mirabolic form: if `W ⊆ (ρ_1 × ⋯ × ρ_r)|P` has highest
derivative `W^(k)`, `k > 0`, then `ν · supp σ ≤ ρ_1 + ⋯ + ρ_r` for every irreducible
subrepresentation `σ` of `W^(k)`. -/
theorem cuspidalProductMirabolicSupportShift :
    CuspidalProductMirabolicSupportShift.{uF, uV} F T := by
  let := T.topology
  intro ψ N r ρ h A hA W f hf k hk hlevel σ hσ s hs
  rcases Nat.lt_or_ge k (N + 1) with hkn | hkn
  · let := T.generalLinearTopologicalGroup (N + 1)
    let := T.generalLinearTopologicalGroup (N + 1 - k)
    obtain ⟨Φ⟩ := nonempty_twistedDual_cuspidalProductEquiv 1 ρ h A
    obtain ⟨β, hβ⟩ := exists_determinant_pairing (T.cuspidalProductInduced ρ h A)
      (T.cuspidalProductInduced (twistedDualData 1 ρ) h (fun i => twistedDualRep T 1 (A i)))
      Φ W f hf
    obtain ⟨q, hq⟩ := exists_derivative_hom_contragredient ψ _ W β hβ k hk hlevel σ hσ
    have hadm : σ.IsAdmissible :=
      (CuspidalSupport.cuspidalEmbedding.{uF, max uF uV} F T _ σ hσ.1).1
    have hirr : σ.contragredient.IsIrreducible :=
      (SmoothRep.isIrreducible_contragredient_iff (compactOpen_cofinal F T _) σ hadm).mpr hσ.1
    apply twist_le_of_dual_le ρ s
    exact le_of_derivative_hom ψ (twistedDualData 1 ρ) h (fun i => twistedDualRep T 1 (A i))
      (fun i => twistedDualRep_represents 1 (hA i)) hk.2 hk.1 hkn σ.contragredient hirr q hq
      (isSupercuspidalSupport_contragredient hs)
  · obtain rfl : k = N + 1 := le_antisymm hk.2 hkn
    rw [eq_zero_of_isSupercuspidalSupport (Nat.sub_self (N + 1)) hs]
    simp

end Langlands.Classification
