import Langlands.Representation.Whittaker.MirabolicFiniteLengthProof
import Langlands.AllField.Representation.Whittaker.IrreducibleCoinvariantFinitenessProof
import Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthDetection
import Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthStatement
import Langlands.AllField.Representation.Whittaker.MirabolicFunctionalTransfer
/-!
# Finite length of restriction to the actual mirabolic subgroup

Bernstein--Zelevinsky (1976), Corollary 5.22, implication (1) implies (2).
Finite length over `GL_(n+1)` and finiteness of twisted coinvariants of
irreducible representations give finite-dimensional coinvariants for every
simple character `θ_S`. Detection then makes the total coinvariant dimension
a strictly monotone bounded function of mirabolic subrepresentations.
-/

noncomputable section

open Multiplicative

namespace Langlands.AllField.Whittaker.MirabolicFiniteLength
open Langlands.Whittaker.MirabolicFiniteLength hiding additiveLattice_mul_mem div_mem_additiveLattice exists_dotProduct_eq exists_exact_conductor exists_generating_character exists_mem_additiveLattice exists_mul_eq exists_mul_eq_on_additiveLattice exists_relations_ne_top exists_trivial_additiveLattice finite_quotient_additiveLattice isFiniteLength_of_finiteDimensional isLimitOfCompactSubgroups_pi isLocallyConstant_selectedSum isLocallyConstant_simpleCharacter mem_additiveLattice_of_forall_mul of_irreducibleCoinvariantFiniteness
open Langlands.AllField.Whittaker.MirabolicFiniteLength
open Langlands.Whittaker hiding CompactLocalizationStatement IrreducibleCoinvariantFinitenessStatement LeviCuspidalCoinvariantFinitenessStatement MirabolicFiniteLengthStatement ParabolicInducedCoinvariantFinitenessStatement SupercuspidalCoinvariantFinitenessStatement UnipotentOrbitStatement compactLocalization irreducibleCoinvariantFiniteness leviCuspidalCoinvariantFiniteness mirabolicFiniteLength parabolicInducedCoinvariantFiniteness supercuspidalCoinvariantFiniteness unipotentOrbit
open Langlands.AllField.Whittaker

open Langlands.Jacquet.Localization

universe uG uV uF

section Modules

variable {G : Type uG} [Group G]

variable [TopologicalSpace G]

end Modules

section Criterion

open Langlands.GeneralLinear.Mirabolic hiding upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear.Mirabolic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The upper-unipotent character `u ↦ ψ(∑_{S i} u_(i,i+1))` of `GL_(n+1)` is
locally constant. -/
theorem isLocallyConstant_selectedSum (ψ : Multiplicative F →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F => (ψ (ofAdd x) : ℂ)))
    {n : ℕ} (S : Fin n → Bool) :
    letI := T.topology
    IsLocallyConstant (fun u : GeneralLinear.upperUnipotent (n + 1) F =>
      ((ψ.comp (selectedSum S)) u : ℂ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hc : Continuous (fun u : GeneralLinear.upperUnipotent (n + 1) F =>
      ∑ i : Fin n, if S i then
        (u : Langlands.GeneralLinear (n + 1) F).val i.castSucc i.succ else 0) :=
    continuous_finsetSum _ fun i _ => continuous_if_const _
      (fun _ => (GeneralLinear.entry i.castSucc i.succ).continuous.comp continuous_subtype_val)
      (fun _ => continuous_const)
  exact hψ.comp_continuous hc

/-- The simple characters `θ_S` of the mirabolic upper-unipotent group are
locally constant. -/
theorem isLocallyConstant_simpleCharacter (ψ : Multiplicative F →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F => (ψ (ofAdd x) : ℂ)))
    {n : ℕ} (S : Fin n → Bool) :
    letI := T.topology
    IsLocallyConstant (fun u : GeneralLinear.Mirabolic.upperUnipotent n F =>
      (simpleCharacter ψ S u : ℂ)) := by
  let := T.topology
  exact (isLocallyConstant_selectedSum T ψ hψ S).comp_continuous
    (upperUnipotentContinuousEquiv (n := n) (F := F)).continuous

/-- A smooth representation of `P_(n+1)` has finite length when all its
simple-character coinvariants are finite-dimensional. -/
theorem isFiniteLength_of_finiteDimensional (ψ : Multiplicative F →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F => (ψ (ofAdd x) : ℂ)))
    (hgen : ∀ χ : Multiplicative F →* ℂˣ,
      (letI := T.topology; IsLocallyConstant (fun x : F => (χ (ofAdd x) : ℂ))) →
      ∃ a : F, ∀ x : F, χ (ofAdd x) = ψ (ofAdd (a * x)))
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear.mirabolic n F) V)
    (hσ : letI := T.topology; IsSmooth σ)
    (hfin : ∀ S : Fin n → Bool, FiniteDimensional ℂ
      (Coinvariants σ (GeneralLinear.Mirabolic.upperUnipotent n F)
        (simpleCharacter ψ S))) :
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F)) σ.asModule := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let U := GeneralLinear.Mirabolic.upperUnipotent n F
  have hU : IsLimitOfCompactSubgroups U := upperUnipotent_isLimitOfCompactSubgroups F T n
  have hθ := isLocallyConstant_simpleCharacter T ψ hψ (n := n)
  have hfin' := hfin
  -- a subrepresentation with the same simple-character images is everything
  have hsep : ∀ W W' : Subrepresentation σ, W ≤ W' →
      (∀ S, W.toSubmodule.map (mk σ U (simpleCharacter ψ S)) =
        W'.toSubmodule.map (mk σ U (simpleCharacter ψ S))) → W' ≤ W := by
    intro W W' hle heq
    by_contra hnot
    let K : Submodule ℂ W'.toSubmodule := W.toSubmodule.comap W'.toSubmodule.subtype
    have hK : ∀ g, K ≤ K.comap (W'.toRepresentation g) := by
      intro g x hx
      exact W.apply_mem_toSubmodule g hx
    let Q := Representation.quotient W'.toRepresentation K hK
    let incl : W'.toRepresentation.IntertwiningMap σ := ⟨W'.toSubmodule.subtype, fun _ => rfl⟩
    let π : W'.toRepresentation.IntertwiningMap Q := ⟨K.mkQ, fun _ => rfl⟩
    have hπ : Function.Surjective π := K.mkQ_surjective
    have hQ : IsSmooth Q :=
      isSmooth_of_surjective π hπ (isSmooth_of_injective incl Subtype.val_injective hσ)
    obtain ⟨x, hxW', hxW⟩ := SetLike.not_le_iff_exists.mp hnot
    have hne : π ⟨x, hxW'⟩ ≠ 0 := by
      intro h
      exact hxW ((Submodule.Quotient.mk_eq_zero K).mp h)
    obtain ⟨S, hS⟩ := exists_relations_ne_top T ψ hgen n Q hQ hne
    apply hS
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := hπ q
    have hy : mk σ U (simpleCharacter ψ S) y.val ∈
        W.toSubmodule.map (mk σ U (simpleCharacter ψ S)) := by
      rw [heq S]
      exact ⟨y.val, y.property, rfl⟩
    obtain ⟨z, hzW, hz⟩ := hy
    let z' : W'.toSubmodule := ⟨z, hle hzW⟩
    have hrel : incl (y - z') ∈ relations σ U (simpleCharacter ψ S) := by
      change y.val - z ∈ _
      rw [← mk_eq_zero, map_sub, hz, sub_self]
    have hrel' := mem_relations_of_injective U hU _ (hθ S) incl Subtype.val_injective hσ hrel
    have hmap : π (y - z') ∈ relations Q U (simpleCharacter ψ S) := by
      rw [← relations_map_of_surjective U _ π hπ]
      exact ⟨_, hrel', rfl⟩
    have hz0 : π z' = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hzW
    rwa [map_sub, hz0, sub_zero] at hmap
  -- the total dimension of the simple-character images
  let f : Subrepresentation σ → ℕ := fun W => ∑ S : Fin n → Bool,
    Module.finrank ℂ (W.toSubmodule.map (mk σ U (simpleCharacter ψ S)))
  have hmono : StrictMono f := by
    intro W W' hlt
    apply Finset.sum_lt_sum
    · intro S _
      exact Submodule.finrank_mono (Submodule.map_mono hlt.le)
    · by_contra h
      push Not at h
      apply hlt.not_ge
      apply hsep W W' hlt.le
      intro S
      exact Submodule.eq_of_le_of_finrank_le (Submodule.map_mono hlt.le)
        (h S (Finset.mem_univ S))
  let B := ∑ S : Fin n → Bool, Module.finrank ℂ (Coinvariants σ U (simpleCharacter ψ S))
  have hB : ∀ W, f W < B + 1 := fun W =>
    Nat.lt_succ_of_le (Finset.sum_le_sum fun S _ => Submodule.finrank_le _)
  let g : Submodule (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F)) σ.asModule →
      Fin (B + 1) := fun N =>
    ⟨f ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)).symm N), hB _⟩
  have hg : StrictMono g := fun N N' h =>
    Fin.mk_lt_mk.mpr (hmono ((Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := σ)).symm.strictMono h))
  have : IsArtinian (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F)) σ.asModule :=
    hg.wellFoundedLT
  have : IsNoetherian (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F)) σ.asModule :=
    isNoetherian_iff.mpr hg.wellFoundedGT
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end Criterion

/-- BZ76 Corollary 5.22, (1) implies (2), from the finiteness of twisted
upper-unipotent coinvariants of irreducible smooth representations (the
finiteness part of BZ76 Theorem 5.21). -/
theorem of_irreducibleCoinvariantFiniteness
    (h : IrreducibleCoinvariantFinitenessStatement.{uF, uV}) :
    MirabolicFiniteLengthStatement.{uF, uV} := by
  intro F _ T n V _ _ ρ hρ hfl
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨ψ, hψ, hgen⟩ := exists_generating_character T
  refine isFiniteLength_of_finiteDimensional T ψ hψ hgen
    (ρ.comp (GeneralLinear.mirabolic n F).subtype)
    (isSmooth_comp _ continuous_subtype_val hρ) fun S => ?_
  have hrel : relations (ρ.comp (GeneralLinear.mirabolic n F).subtype)
      (GeneralLinear.Mirabolic.upperUnipotent n F) (simpleCharacter ψ S) =
      relations ρ (GeneralLinear.upperUnipotent (n + 1) F) (ψ.comp (selectedSum S)) :=
    relations_eq_of_surjective ρ _ _ _ _ _ GeneralLinear.Mirabolic.upperUnipotentEquiv
      GeneralLinear.Mirabolic.upperUnipotentEquiv.surjective (fun _ => rfl) (fun _ => rfl)
  have := finiteDimensional_coinvariants_of_isFiniteLength
    (GeneralLinear.upperUnipotent (n + 1) F) (ψ.comp (selectedSum S))
    (fun W _ _ π hπ hirr => h F T (n + 1) W π hπ hirr _
      (isLocallyConstant_selectedSum T ψ hψ S)) ρ hρ hfl
  exact (Submodule.quotEquivOfEq _ _ hrel.symm).finiteDimensional

end Langlands.AllField.Whittaker.MirabolicFiniteLength

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding CompactLocalizationStatement IrreducibleCoinvariantFinitenessStatement LeviCuspidalCoinvariantFinitenessStatement MirabolicFiniteLengthStatement ParabolicInducedCoinvariantFinitenessStatement SupercuspidalCoinvariantFinitenessStatement UnipotentOrbitStatement compactLocalization irreducibleCoinvariantFiniteness leviCuspidalCoinvariantFiniteness mirabolicFiniteLength parabolicInducedCoinvariantFiniteness supercuspidalCoinvariantFiniteness unipotentOrbit
open Langlands.AllField.Whittaker

universe uF uV

/-- Bernstein--Zelevinsky (1976), Corollary 5.22, implication (1) implies (2):
a smooth finite-length representation of `GL_(n+1)(F)` restricts to a
finite-length representation of the actual mirabolic subgroup. -/
theorem mirabolicFiniteLength : MirabolicFiniteLengthStatement.{uF, uV} :=
  Langlands.AllField.Whittaker.MirabolicFiniteLength.of_irreducibleCoinvariantFiniteness
    irreducibleCoinvariantFiniteness.{uF, uV}

end Langlands.AllField.Whittaker
