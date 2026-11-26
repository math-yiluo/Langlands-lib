import Langlands.Correspondence.HenniartPadicArtinTransport
import Langlands.Correspondence.HenniartWeilElementaryLayer
import Langlands.Correspondence.HenniartNumericalReductionProof
import Langlands.LocalFactor.Ramification.InertiaPresentationProof
import Mathlib.Data.Set.Card.Arithmetic

/-! # Counting reduction for the integer Weil conductor step -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence VirtualRepresentation Ramification.Padic
open scoped BigOperators

universe uK uW uQ
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- The natural Artin conductor is unique, independently of the representative and
finite inertia presentation used in `HasArtinConductor`. -/
theorem hasArtinConductor_unique {k a b : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    (ha : HasArtinConductor K σ a) (hb : HasArtinConductor K σ b) : a = b := by
  obtain ⟨A, P, hP, hA, ha⟩ := (hasArtinConductor_iff_exists_padicPresentation K σ a).mp ha
  obtain ⟨B, Q, hQ, hB, hb⟩ := (hasArtinConductor_iff_exists_padicPresentation K σ b).mp hb
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff A B).mp (hA.trans hB.symm)
  have h := (finiteInertiaConductorEquivalence K A B e P Q hP hQ).1
  rw [ha, hb] at h
  exact_mod_cast h

/-- Unramified twisting leaves the Artin conductor unchanged. -/
theorem hasArtinConductor_unramifiedTwist {k a : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    (ha : HasArtinConductor K σ a) (z : ℂˣ) :
    HasArtinConductor K (weilUnramifiedTwist K k z σ) a := by
  obtain ⟨A, P, hP, hA, ha⟩ := (hasArtinConductor_iff_exists_padicPresentation K σ a).mp ha
  let χ := Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) z
  let B := FiniteRepresentation.twist χ.toMonoidHom A
  have hr : localInertiaRepresentation K A = localInertiaRepresentation K B := by
    ext i v
    have hi := Weil.Local.unramifiedCharacter_on_kernel (Weil.Local.localDegree K) z i.property
    change A.representation i.val v = (χ i.val : ℂ) • A.representation i.val v
    rw [show χ i.val = 1 from hi, Units.val_one, one_smul]
  let Q : FiniteInertiaPresentation K B := FiniteInertiaPresentation.mk P.extension (by
    rw [← hr]
    exact P.kernel_le)
  refine (hasArtinConductor_iff_exists_padicPresentation K _ a).mpr ⟨B, Q, hP, ?_, ?_⟩
  · calc
      FiniteRepresentation.classOf B =
          FiniteRepresentation.twistClass χ.toMonoidHom (FiniteRepresentation.classOf A) := rfl
      _ = FiniteRepresentation.twistClass χ.toMonoidHom (weilClassForget K σ) :=
        congrArg (FiniteRepresentation.twistClass χ.toMonoidHom) hA
      _ = weilClassForget K (weilUnramifiedTwist K k z σ) :=
        (FiniteRepresentation.forget_continuousIrreducibleTwistEquiv χ (k + 1) σ).symm
  · let T := (absoluteFiniteExtension K P.extension).canonicalTopologicalData
    let π := (weilInertiaRestriction K P.extension).toMonoidHom
    have h := artinConductorOfQuotient_equiv T K.Carrier π hP P.kernel_le Q.kernel_le
      (hr ▸ Representation.Equiv.refl (localInertiaRepresentation K A))
    exact h.symm.trans ha

/-- At fixed rank an unramified-twist orbit determines at most one Swan exponent. -/
theorem weilRefinedStratum_swan_unique {k s t f g : ℕ}
    {c : Weil.UnramifiedOrbitClasses.{uK, uW} (Weil.Local.localDegree K)}
    (hs : c ∈ weilRefinedStratum K k s f) (ht : c ∈ weilRefinedStratum K k t g) : s = t := by
  obtain ⟨σ, hσ, ⟨a, ha, rfl⟩, -⟩ := hs
  obtain ⟨τ, hτ, ⟨b, hb, rfl⟩, -⟩ := ht
  obtain ⟨z, hz⟩ := (weilOrbitClass_eq_iff K τ σ).mp (hτ.trans hσ.symm)
  have hab := hasArtinConductor_unique K (hz ▸ hasArtinConductor_unramifiedTwist K ha z) hb
  rw [hab]

/-- The torsion-one orbits of rank `k+1` with Swan exponent strictly less than `b`. -/
def weilSwanBelow (k b : ℕ) :
    Set (Weil.UnramifiedOrbitClasses.{uK, uW} (Weil.Local.localDegree K)) :=
  ⋃ s ∈ (↑(Finset.range b) : Set ℕ), weilRefinedStratum K k s 1

theorem mem_weilSwanBelow {k b : ℕ}
    {c : Weil.UnramifiedOrbitClasses.{uK, uW} (Weil.Local.localDegree K)} :
    c ∈ weilSwanBelow K k b ↔ ∃ s < b, c ∈ weilRefinedStratum K k s 1 := by
  simp [weilSwanBelow]

theorem encard_weilSwanBelow (k b : ℕ) :
    (weilSwanBelow.{uK, uW} K k b).encard =
      ∑ s ∈ Finset.range b, weilTwistIrreducibleCount.{uK, uW} K k s := by
  have h := (Finset.range b).finite_toSet.encard_biUnion
    (s := fun s => weilRefinedStratum.{uK, uW} K k s 1) (by
      intro s _ t _ hst
      exact Set.disjoint_left.mpr fun _ hs ht => hst (weilRefinedStratum_swan_unique K hs ht))
  rw [finsum_mem_eq_finite_toFinset_sum _ (Finset.range b).finite_toSet,
    Finset.finite_toSet_toFinset] at h
  exact h

private theorem cutoffs {d n l : ℕ} (hd : 0 < d) (hdn : d ≤ n) (hl : 0 < l) :
    d * (n * l) / n = d * l ∧ d * (n * l - 1) / n + 1 = d * l := by
  have hn : 0 < n := hd.trans_le hdn
  have hdl : 0 < d * l := Nat.mul_pos hd hl
  have hprod : d * (n * l) = (d * l) * n := by ac_rfl
  refine ⟨by rw [hprod, Nat.mul_div_cancel _ hn], ?_⟩
  have hmul : d * (n * l - 1) = (d * l) * n - d := by
    rw [Nat.mul_sub_left_distrib, hprod, mul_one]
  have hlo : (d * l - 1) * n ≤ d * (n * l - 1) := by
    rw [hmul, Nat.mul_sub_right_distrib, one_mul]
    omega
  have hhi : d * (n * l - 1) < (d * l) * n := by
    rw [hmul]
    exact Nat.sub_lt (Nat.mul_pos hdl hn) hd
  have hlo' := (Nat.le_div_iff_mul_le hn).mpr hlo
  have hhi' := (Nat.div_lt_iff_lt_mul hn).mpr hhi
  omega

/-- A rank-wise equivalence with a common factor of cardinality `q_K` gives the
integer step in the summed conductor count. The existence of such equivalences
is a separate ramification and twisting input. -/
theorem weilConductorCountStep_of_equiv {r l : ℕ} (hl : 1 ≤ l) (Q : Type uQ)
    (hQ : ENat.card Q = (K.canonicalTopologicalData.residueCardinality : ℕ∞))
    (he : ∀ d ∈ (p ^ r).divisors,
      Nonempty (Q × weilSwanBelow.{uK, uW} K (d - 1) (d * l) ≃
        weilSwanBelow.{uK, uW} K (d - 1) (d * l + 1))) :
    weilConductorCount.{uK, uW} K (p ^ r - 1) (p ^ r * l) =
      (K.canonicalTopologicalData.residueCardinality : ℕ∞) *
        weilConductorCount.{uK, uW} K (p ^ r - 1) (p ^ r * l - 1) := by
  have hn : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos _
  have hn' : p ^ r - 1 + 1 = p ^ r := by omega
  simp only [weilConductorCount, hn']
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd := (Nat.mem_divisors.mp hd).1
  obtain ⟨hb, hs⟩ := cutoffs (Nat.pos_of_dvd_of_pos hdvd hn) (Nat.le_of_dvd hn hdvd) hl
  rw [hb, hs, ← encard_weilSwanBelow, ← encard_weilSwanBelow]
  obtain ⟨e⟩ := he d hd
  simpa only [ENat.card_prod, ENat.card_coe_set_eq, hQ] using (ENat.card_congr e).symm

end Langlands.Henniart.Numerical
