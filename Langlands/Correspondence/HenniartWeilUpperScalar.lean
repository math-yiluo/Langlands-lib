import Langlands.Correspondence.HenniartWeilTorsionInertia
import Langlands.LocalFactor.Ramification.Herbrand.WildInertiaStructure
import Langlands.LocalFactor.Ramification.InflationProof
import Langlands.VirtualRepresentation.Weil.GroupTransport

/-! # Scalar action at a positive upper bound -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation Weil.Local
open Ramification Ramification.Padic Ramification.HerbrandBridge
open VirtualRepresentation.LocalWeil.Ramification CyclicRestriction

universe uK uW
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
variable (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K))

/-- The actual upper group acts through an algebraic scalar character. -/
def HasUpperScalarAction (a : ℝ) : Prop :=
  ∃ χ : upperGroup K a →* ℂˣ, ∀ w : upperGroup K a,
    A.representation w = (χ w : ℂ) • (1 : Module.End ℂ A)

private theorem presentation_trivial_at (P : FiniteInertiaPresentation K A)
    (hP : Function.Surjective (weilInertiaRestriction K P.extension))
    {b : ℝ} (hb : 0 ≤ b) (ht : IsTrivialAt K A b)
    (g : inertia (absoluteFiniteExtension K P.extension).canonicalTopologicalData K.Carrier)
    (hg : g.val ∈ Padic.upperRamificationGroup
      (absoluteFiniteExtension K P.extension).canonicalTopologicalData K.Carrier b) :
    P.representation hP g = 1 := by
  have hfix := (upperFixedSpace_eq_top_iff K A b).mpr ht
  rw [presentationUpperFixedComparison K A P hP b hb] at hfix
  apply LinearMap.ext
  intro v
  have hv : v ∈ inertiaUpperFixedVectors
      (absoluteFiniteExtension K P.extension).canonicalTopologicalData K.Carrier
        (P.representation hP) b := hfix ▸ Submodule.mem_top
  let T := (absoluteFiniteExtension K P.extension).canonicalTopologicalData
  change ∀ t : (Padic.upperRamificationGroup T K.Carrier b).subgroupOf (inertia T K.Carrier),
    P.representation hP t.val v = v at hv
  exact hv ⟨g, hg⟩

private theorem upper_element_scalar_of_trivialAbove (hc : A.IsContinuous)
    (hi : (localInertiaRepresentation K A).IsIrreducible)
    {i : ℕ} (hn : A.rank = p ^ i) {a : ℝ} (ha : 0 < a)
    (ht : ∀ b : ℝ, a < b → IsTrivialAt K A b) (w : upperGroup K a) :
    ∃ z : ℂˣ, A.representation w = (z : ℂ) • (1 : Module.End ℂ A) := by
  obtain ⟨P⟩ := continuousWeilFiniteInertiaPresentation K A hc
  let T := (absoluteFiniteExtension K P.extension).canonicalTopologicalData
  let I := inertia T K.Carrier
  have hP := weilInertiaRestriction_surjective K P.extension
  let π := (weilInertiaRestriction K P.extension).toMonoidHom
  let R := P.representation hP
  have hR : R.comp π = localInertiaRepresentation K A :=
    MonoidHom.ext fun x => P.representation_apply hP x
  let B := FiniteRepresentation.of R
  have hiR : R.IsIrreducible := by
    apply (isIrreducible_restrict_iff π hP B).mp
    change Representation.IsIrreducible (R.comp π)
    rwa [hR]
  let N := inertiaLowerGroup T K.Carrier 1
  let : N.Normal := inertiaLowerGroup_isNormal T K.Carrier 1
  let : Finite I := Finite.of_injective (fun g : I => (g : Gal(P.extension/K.Carrier)))
    Subtype.val_injective
  let : Finite N := Finite.of_injective (fun g : N => (g : I)) Subtype.val_injective
  let : NeZero (Nat.card N : ℂ) := ⟨by exact_mod_cast (Nat.card_pos (α := N)).ne'⟩
  obtain ⟨hcyc, hcop⟩ := inertia_quotient_lowerOne_cyclic_coprime T K.Carrier
  let : IsCyclic (I ⧸ N) := hcyc
  have hcop' : Nat.Coprime N.index (Module.finrank ℂ A) := by
    change Nat.Coprime N.index A.rank
    rw [hn]
    exact hcop.pow_right i
  have hiN := isIrreducible_comp_of_cyclic_coprime R N hiR inferInstance hcop'
  have wI : w.val ∈ localInertia K := by
    rw [localInertia_eq_comap K, ← absoluteUpperCanonicalInertia K]
    exact absoluteUpperRamificationGroup_antitone K ha.le w.property
  let τ := π ⟨w.val, wI⟩
  have hτ : (τ : Gal(P.extension/K.Carrier)) ∈ Padic.upperRamificationGroup T K.Carrier a := by
    change (weilInertiaRestriction K P.extension ⟨w.val, wI⟩ : Gal(P.extension/K.Carrier)) ∈ _
    rw [weilInertiaRestriction_coe]
    exact absoluteUpperRamificationGroup_le_comap K a P.extension w.property
  obtain ⟨z, hz⟩ := Weil.UnramifiedReductionAux.scalar_of_commuting_unit
    (R.comp N.subtype) hiN (R.asGroupHom τ) (by
      intro n
      let σ : I := n
      have hs : (σ : Gal(P.extension/K.Carrier)) ∈ Padic.lowerRamificationGroup T K.Carrier 1 :=
        n.property
      obtain ⟨b, hb, hg⟩ := exists_gt_commutator_mem_upperRamificationGroup_of_wild T K.Carrier
        ha hs hτ
      let g : I := (τ * σ)⁻¹ * (σ * τ)
      have hg1 : R g = 1 := presentation_trivial_at K A P hP (ha.le.trans hb.le) (ht b hb) g hg
      have hmul : σ * τ = (τ * σ) * g := by
        change σ * τ = (τ * σ) * ((τ * σ)⁻¹ * (σ * τ))
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      have hr := congrArg R hmul
      change R σ * R τ = R τ * R σ
      simpa only [map_mul, hg1, mul_one] using hr)
  exact ⟨z, (P.representation_apply hP ⟨w.val, wI⟩).symm.trans hz⟩

/-- If the rank is a power of the residue characteristic, the action on a
positive upper group with trivial action at every deeper index is scalar,
provided the actual inertia restriction is irreducible. -/
theorem hasUpperScalarAction_of_trivialAbove (hc : A.IsContinuous)
    (hi : (localInertiaRepresentation K A).IsIrreducible)
    {i : ℕ} (hn : A.rank = p ^ i) {a : ℝ} (ha : 0 < a)
    (ht : ∀ b : ℝ, a < b → IsTrivialAt K A b) : HasUpperScalarAction K A a := by
  have : Nontrivial A := Module.finrank_pos_iff.mp (hn ▸ pow_pos (Fact.out : p.Prime).pos i)
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  let R := A.representation.comp (upperGroup K a).subtype
  have H (w : upperGroup K a) : ∃ z : ℂˣ,
      R w = (z : ℂ) • (1 : Module.End ℂ A) :=
    upper_element_scalar_of_trivialAbove K A hc hi hn ha ht w
  have h (w : upperGroup K a) : w ∈ eigenlineStabilizer R v := by
    obtain ⟨z, hz⟩ := H w
    exact ⟨z, by rw [hz, LinearMap.smul_apply, Module.End.one_apply]⟩
  refine ⟨eigenlineCharacter hv h, fun w => ?_⟩
  obtain ⟨z, hz⟩ := H w
  have he := eigenlineCharacter_apply_smul hv h w
  rw [hz, LinearMap.smul_apply, Module.End.one_apply] at he
  rw [← eigenline_scalar_unique v hv he]
  exact hz

/-- Application to a torsion-one class on any actual representative of
prime-power rank with last break at most the positive index. -/
theorem hasUpperScalarAction_of_torsionOne {k i : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    (hA : classOf A = weilClassForget K σ) (hσ : weilTorsionNumber K σ = 1)
    (hr : k + 1 = p ^ i) {a : ℝ} (ha : 0 < a) (hb : lastBreak K A ≤ a) :
    HasUpperScalarAction K A a := by
  have hc := (weilRepresentative_continuous_irreducible K hA).1
  exact hasUpperScalarAction_of_trivialAbove K A hc
    ((weilTorsionNumber_eq_one_iff_inertia_irreducible K hA).mp hσ)
    ((weilRepresentative_break_rank K hA).2.trans hr) ha
    ((lastBreak_le_iff_isTrivialAbove K hc ha.le).mp hb)

end Langlands.Henniart.Numerical
