import Langlands.Representation.Exponents.InnerCuspidalQuotientSupport
import Langlands.Representation.Geometric.RefinedOppositePieceTransport
import Langlands.Representation.Exponents.GeometricExcessBranchFromUpper
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! Inner cuspidal support for the actual upper refined Jacquet quotient. -/

noncomputable section

namespace Langlands.InnerCuspidalQuotientSupport

open GeneralLinear Geometric CuspidalSupport RelativeJacquetMultiplicity
open WeylBranchPieces ProductLeviMinimalIndex RefinedOppositeReversal ProductLeviDualOpposite
open Geometric.RefinedOppositePieceTransport OppositeCuspidalJacquetFiltration

universe uF uV uW uM

section Reversal

variable {n : ℕ} (B : BlockShape n) (R S : BlockRefinement B)

/-- Minimality of an assembled permutation is tested in each coarse block,
with possibly different source and target refinements. -/
theorem isMinimalRepresentative_blockPermOf_refinements_iff
    (σ : ∀ i, Equiv.Perm (Fin (B.size i))) :
    IsMinimalRepresentative (B.flatten R) (B.flatten S) (blockPermOf B σ) ↔
      ∀ i, IsMinimalRepresentative (R i) (S i) (σ i) := by
  simp only [isMinimalRepresentative_iff]
  have h1 := forall_flatten_pairs_iff B R
    (P := fun a b => a < b → blockPermOf B σ a < blockPermOf B σ b)
  have h2 := forall_flatten_pairs_iff B S
    (P := fun a b => a < b → (blockPermOf B σ).symm a < (blockPermOf B σ).symm b)
  simp only [blockPermOf_index, blockPermOf_symm_index,
    (index_strictMono B _).lt_iff_lt] at h1 h2
  rw [h1, h2]
  constructor
  · rintro ⟨ha, hb⟩ i
    exact ⟨ha i, hb i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

/-- Reverse each inner block order twice. -/
theorem reverseRefinement_reverse :
    reverseRefinement B (reverseRefinement B R) = R := by
  funext i
  exact GeometricExcessBranch.reverse_reverse (R i)

/-- The second inner reversal is the inverse of the first one. -/
theorem innerReverse_reverse_eq_inv :
    innerReversePermutation B (reverseRefinement B R) =
      (innerReversePermutation B R)⁻¹ := by
  calc
    innerReversePermutation B (reverseRefinement B R) =
        (innerReversePermutation B R)⁻¹ * (innerReversePermutation B R *
          innerReversePermutation B (reverseRefinement B R)) := by group
    _ = (innerReversePermutation B R)⁻¹ := by
      rw [GeometricExcessBranch.innerReverse_mul_innerReverse_reverse, mul_one]

variable {F : Type uF} [Field F]

include F in
/-- Inverse inner reversal is a minimal representative between the two
flattened refinements. -/
theorem isMinimalRepresentative_innerReverse_inv :
    IsMinimalRepresentative (B.flatten R) (B.flatten (reverseRefinement B R))
      (innerReversePermutation B R)⁻¹ := by
  change IsMinimalRepresentative _ _ (blockPermOf B (fun i => (R i).reversePermutation)).symm
  rw [blockPermOf_symm]
  apply (isMinimalRepresentative_blockPermOf_refinements_iff B R
    (reverseRefinement B R) _).mpr
  intro i
  have hm : IsMinimalRepresentative (R i) (R i) 1 :=
    ⟨fun j => index_strictMono (R i) j, fun j => index_strictMono (R i) j⟩
  simpa only [mul_one, Equiv.Perm.inv_def, reverseRefinement_apply] using
    isMinimalRepresentative_reverse_inv_mul hm
    (conjugatesLevi_one (F := F) (R i))

end Reversal

section Normalized

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (R : BlockRefinement B)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual upper quotient at R, transported by inverse inner reversal,
is the actual opposite quotient at the reversed refinement. -/
def flattenedUpperToOppositeReverseEquiv
    (A : Representation ℂ (B.Levi F.Carrier) V) :
    Representation.Equiv
      (transport (B.flatten R) (B.flatten (reverseRefinement B R))
        (innerReversePermutation B R)⁻¹
        (conjugatesLevi_inv (conjugatesLevi_innerReverse B R F.Carrier))
        ((T.normalizedRefinedJacquet B R A).comp
          (flattenedLeviEquiv F.Carrier B R).toMonoidHom))
      ((T.normalizedRefinedOppositeJacquet B (reverseRefinement B R) A).comp
        (flattenedLeviEquiv F.Carrier B (reverseRefinement B R)).toMonoidHom) := by
  have e := flattenedNormalizedOppositeReverseEquiv B (reverseRefinement B R) T A
  have convertRefinement (S : BlockRefinement B) (hS : S = R)
      (w : Equiv.Perm (Fin n))
      (hw : ConjugatesLevi (F := F.Carrier) (B.flatten S)
        (B.flatten (reverseRefinement B R)) w)
      (hw' : w = (innerReversePermutation B R)⁻¹)
      (e' : Representation.Equiv
        (transport (B.flatten S) (B.flatten (reverseRefinement B R)) w hw
          ((T.normalizedRefinedJacquet B S A).comp
            (flattenedLeviEquiv F.Carrier B S).toMonoidHom))
        ((T.normalizedRefinedOppositeJacquet B (reverseRefinement B R) A).comp
          (flattenedLeviEquiv F.Carrier B (reverseRefinement B R)).toMonoidHom)) :
      Representation.Equiv
        (transport (B.flatten R) (B.flatten (reverseRefinement B R))
          (innerReversePermutation B R)⁻¹
          (conjugatesLevi_inv (conjugatesLevi_innerReverse B R F.Carrier))
          ((T.normalizedRefinedJacquet B R A).comp
            (flattenedLeviEquiv F.Carrier B R).toMonoidHom))
        ((T.normalizedRefinedOppositeJacquet B (reverseRefinement B R) A).comp
          (flattenedLeviEquiv F.Carrier B (reverseRefinement B R)).toMonoidHom) := by
    subst S
    subst w
    exact e'
  exact convertRefinement _ (reverseRefinement_reverse B R) _ _
    (innerReverse_reverse_eq_inv B R) e

/-- Reversal preserves admissible cuspidality, using the proved minimality of
the inverse reversal and actual whole-Levi transport. -/
theorem isLeviCuspidal_innerReverse_inv
    (ρ : Representation ℂ ((B.flatten R).Levi F.Carrier) V) :
    letI := T.topology
    IsLeviCuspidal (B.flatten R) ρ →
    IsLeviCuspidal (B.flatten (reverseRefinement B R))
      (transport (B.flatten R) (B.flatten (reverseRefinement B R))
        (innerReversePermutation B R)⁻¹
        (conjugatesLevi_inv (conjugatesLevi_innerReverse B R F.Carrier)) ρ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ
  exact ⟨isAdmissible_transport _ _ hρ.1,
    isLeviQuasicuspidal_transport _ _ _
      (isMinimalRepresentative_innerReverse_inv (F := F.Carrier) B R) _ ρ hρ.2⟩

/-- A cuspidal upper-Jacquet subquotient of an actual induction quotient
has the same conditional support identification as an opposite subquotient.
The final witness includes the inner reversal and stays in the coarse Weyl group. -/
theorem exists_transport_of_upper_quotient_of_constituent
    (hC : GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uM})
    (hn : 0 < n) (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (hωi : Representation.IsIrreducible ω.ρ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (ρ : Rep.{uM} ℂ ((B.flatten R).Levi F.Carrier))
    (hρi : Representation.IsIrreducible ρ.ρ) :
    letI := T.topology
    IsLeviCuspidal (B.flatten S) ω.ρ →
    IsLeviCuspidal (B.flatten R) ρ.ρ →
    (∃ q : (innerInduced T B S (Rep.of (ω.ρ.comp
      (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom))).ρ.IntertwiningMap π.ρ,
      Function.Surjective q) →
    IsSubquotient ((T.normalizedRefinedJacquet B R π.ρ).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ.ρ →
    ∃ h ∈ blockWeyl B,
      ∃ hh : ConjugatesLevi (F := F.Carrier) (B.flatten S) (B.flatten R) h,
        Nonempty (ρ.ρ.Equiv (transport (B.flatten S) (B.flatten R) h hh ω.ρ)) := by
  let := T.topology
  intro hωc hρc hq hsub
  let r := innerReversePermutation B R
  let hr := conjugatesLevi_innerReverse B R F.Carrier
  let ρ' := Rep.of (transport (B.flatten R) (B.flatten (reverseRefinement B R))
    r⁻¹ (conjugatesLevi_inv hr) ρ.ρ)
  have hρ'i : Representation.IsIrreducible ρ'.ρ :=
    (isIrreducible_transport r⁻¹ (conjugatesLevi_inv hr) ρ.ρ).mpr hρi
  have hρ'c : IsLeviCuspidal (B.flatten (reverseRefinement B R)) ρ'.ρ :=
    isLeviCuspidal_innerReverse_inv T B R ρ.ρ hρc
  have hsub' : IsSubquotient
      ((innerJacquet T B (reverseRefinement B R) π).ρ.comp
        (flattenedLeviEquiv F.Carrier B (reverseRefinement B R)).toMonoidHom) ρ'.ρ := by
    have h := hsub.comp
      (leviConjugation (B.flatten R) (B.flatten (reverseRefinement B R))
        r⁻¹ (conjugatesLevi_inv hr)).symm.toMonoidHom
    exact IsSubquotient.of_equiv_left
      (flattenedUpperToOppositeReverseEquiv T B R π.ρ).symm h
  obtain ⟨h, hmem, hh, ⟨e⟩⟩ :=
    exists_transport_of_quotient_of_constituent T B (reverseRefinement B R)
      hC hn S ω hωi π ρ' hρ'i hωc hρ'c hq hsub'
  have hrmem : r ∈ blockWeyl B := blockPermOf_mem_blockWeyl B _
  refine ⟨r * h, (blockWeyl B).mul_mem hrmem hmem,
    conjugatesLevi_mul hh hr, ?_⟩
  have ecancel : transport (B.flatten (reverseRefinement B R)) (B.flatten R)
      r hr ρ'.ρ = ρ.ρ := by
    change transport _ _ r hr
      (transport _ _ r⁻¹ (conjugatesLevi_inv hr) ρ.ρ) = ρ.ρ
    rw [transport_transport (conjugatesLevi_inv hr) hr
      (conjugatesLevi_one (B.flatten R)) (mul_inv_cancel r), transport_one]
  have er := transportEquiv r hr e
  rw [ecancel, ← transport_mul hh hr] at er
  exact ⟨er⟩

/-- The upper quotient-support adapter with the arbitrary fine real parameter
of the persistence target, specialized only at coarse parameter zero. -/
theorem exists_transport_fineTwist_of_upper_quotient_of_constituent
    (hC : GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uM})
    (hn : 0 < n) (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (hωi : Representation.IsIrreducible ω.ρ)
    (v : Fin (B.flatten S).length → ℝ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (ρ : Rep.{uM} ℂ ((B.flatten R).Levi F.Carrier))
    (hρi : Representation.IsIrreducible ρ.ρ) :
    letI := T.topology
    IsLeviCuspidal (B.flatten S) ω.ρ →
    IsLeviCuspidal (B.flatten R) ρ.ρ →
    (∃ q : (innerInduced T B S (fineTwist T B S ω v 0)).ρ.IntertwiningMap π.ρ,
      Function.Surjective q) →
    IsSubquotient ((T.normalizedRefinedJacquet B R π.ρ).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ.ρ →
    ∃ h ∈ blockWeyl B,
      ∃ hh : ConjugatesLevi (F := F.Carrier) (B.flatten S) (B.flatten R) h,
        Nonempty (ρ.ρ.Equiv (transport (B.flatten S) (B.flatten R) h hh
          (T.leviRealPowerTwist (B.flatten S) (-v) ω.ρ))) := by
  let := T.topology
  intro hωc hρc hq hρ
  let Ω := Rep.of (T.leviRealPowerTwist (B.flatten S) (-v) ω.ρ)
  have hΩi : Representation.IsIrreducible Ω.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) (-v) ω.ρ).mpr hωi
  have hΩc : IsLeviCuspidal (B.flatten S) Ω.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B.flatten S) (-v) ω.ρ).mpr hωc
  have hfine : fineTwist T B S ω v 0 =
      Rep.of (Ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom) := by
    have hv : (fun k : Fin (B.flatten S).length =>
        -v k + (0 : Fin B.length → ℝ) ((B.flattenBlockEquiv S).symm k).1) = -v := by
      funext k
      simp
    change Rep.of ((T.leviRealPowerTwist (B.flatten S) _ ω.ρ).comp _) = _
    rw [hv]
  have hq' : ∃ q : (innerInduced T B S (Rep.of (Ω.ρ.comp
      (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom))).ρ.IntertwiningMap π.ρ,
      Function.Surjective q := by
    rw [hfine] at hq
    exact hq
  exact exists_transport_of_upper_quotient_of_constituent T B R hC hn S Ω hΩi π ρ hρi
    hΩc hρc hq' hρ

end Normalized

end Langlands.InnerCuspidalQuotientSupport
