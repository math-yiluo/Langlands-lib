import Langlands.Representation.Whittaker.IrreducibleCoinvariantFinitenessProof
import Langlands.Representation.Whittaker.IrreducibleCoinvariantFinitenessStatement
import Langlands.Representation.Whittaker.MirabolicFiniteLengthDetection
import Langlands.Representation.Whittaker.MirabolicFiniteLengthStatement
import Langlands.Representation.Whittaker.MirabolicFunctionalTransfer
import Langlands.Representation.Filtration.RepresentationLength
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.FiniteLength

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

namespace Langlands.Whittaker.MirabolicFiniteLength

open Jacquet.Localization

universe uG uV uF

section Modules

variable {G : Type uG} [Group G]

/-- A nonzero representation whose only subrepresentations are `⊥` and `⊤` is
irreducible. -/
theorem isIrreducible_of_forall {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [Nontrivial V]
    (h : ∀ A : Subrepresentation ρ, A = ⊥ ∨ A = ⊤) : ρ.IsIrreducible := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hbot
    have hvtop : v ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top (R := ℂ) (x := v)
    rw [← hbot] at hvtop
    exact hv ((Submodule.mem_bot ℂ).mp hvtop)
  exact { toNontrivial := ⟨⟨⊥, ⊤, hne⟩⟩, eq_bot_or_eq_top := h }

variable [TopologicalSpace G]

/-- Twisted coinvariants of a smooth representation of length `n` are
finite-dimensional when those of irreducible smooth representations are. -/
theorem finiteDimensional_coinvariants_of_repLength_eq (U : Subgroup G) (θ : U →* ℂˣ)
    (hirr : ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W),
      IsSmooth π → π.IsIrreducible → FiniteDimensional ℂ (Coinvariants π U θ))
    (n : ℕ) : ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      IsSmooth ρ → repLength ρ = n → FiniteDimensional ℂ (Coinvariants ρ U θ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ ρ hρ hn
    by_cases hV : Subsingleton V
    · have : Subsingleton (Coinvariants ρ U θ) := (mk_surjective ρ U θ).subsingleton
      infer_instance
    rw [not_subsingleton_iff_nontrivial] at hV
    by_cases hsub : ∃ A : Subrepresentation ρ, A ≠ ⊥ ∧ A ≠ ⊤
    swap
    · push Not at hsub
      exact hirr V ρ hρ (isIrreducible_of_forall ρ fun A => (em (A = ⊥)).imp id (hsub A))
    obtain ⟨A, hAbot, hAtop⟩ := hsub
    let Q := ρ.quotient A.toSubmodule (fun g _ hv => A.apply_mem_toSubmodule g hv)
    let ι : A.toRepresentation.IntertwiningMap ρ := ⟨A.toSubmodule.subtype, fun _ => rfl⟩
    let π : ρ.IntertwiningMap Q := ⟨A.toSubmodule.mkQ, fun _ => rfl⟩
    have hι : Function.Injective ι := Subtype.val_injective
    have hπ : Function.Surjective π := A.toSubmodule.mkQ_surjective
    have hsum : (n : ℕ∞) = repLength A.toRepresentation + repLength Q := by
      rw [← hn]
      exact repLength_eq_subrepresentation_add_quotient ρ A
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (fun h : repLength A.toRepresentation = ⊤ => by
      simp [h] at hsum)
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (fun h : repLength Q = ⊤ => by
      simp [h] at hsum)
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := repLength_eq_zero_iff.mp ha.symm
      exact hAbot (Subrepresentation.toSubmodule_injective Submodule.eq_bot_of_subsingleton)
    have hb0 : b ≠ 0 := by
      rintro rfl
      have := repLength_eq_zero_iff.mp hb.symm
      exact hAtop (Subrepresentation.toSubmodule_injective
        (Submodule.Quotient.subsingleton_iff.mp this))
    rw [← ha, ← hb] at hsum
    norm_cast at hsum
    have hfA := ih a (by omega) A.toRepresentation (isSmooth_of_injective ι hι hρ) ha.symm
    have hfQ := ih b (by omega) Q (isSmooth_of_surjective π hπ hρ) hb.symm
    have hex : LinearMap.range ι.toLinearMap = LinearMap.ker π.toLinearMap := by
      change LinearMap.range A.toSubmodule.subtype = LinearMap.ker A.toSubmodule.mkQ
      rw [Submodule.range_subtype, Submodule.ker_mkQ]
    have hrange := map_range_eq_ker U θ ⊥ bot_le (isInvariant_bot U θ) ι π hπ hex
    exact Module.Finite.of_exact (LinearMap.exact_iff.mpr hrange.symm)
      (map_surjective U θ ⊥ bot_le (isInvariant_bot U θ) π hπ)

/-- Twisted coinvariants of a smooth finite-length representation are
finite-dimensional when those of irreducible smooth representations are. -/
theorem finiteDimensional_coinvariants_of_isFiniteLength (U : Subgroup G) (θ : U →* ℂˣ)
    (hirr : ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W),
      IsSmooth π → π.IsIrreducible → FiniteDimensional ℂ (Coinvariants π U θ))
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hfl : IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule) :
    FiniteDimensional ℂ (Coinvariants ρ U θ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top_iff.mpr hfl)
  exact finiteDimensional_coinvariants_of_repLength_eq U θ hirr n ρ hρ hn.symm

end Modules

section Criterion

open GeneralLinear.Mirabolic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The upper-unipotent character `u ↦ ψ(∑_{S i} u_(i,i+1))` of `GL_(n+1)` is
locally constant. -/
theorem isLocallyConstant_selectedSum (ψ : Multiplicative F.Carrier →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F.Carrier => (ψ (ofAdd x) : ℂ)))
    {n : ℕ} (S : Fin n → Bool) :
    letI := T.topology
    IsLocallyConstant (fun u : GeneralLinear.upperUnipotent (n + 1) F.Carrier =>
      ((ψ.comp (selectedSum S)) u : ℂ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hc : Continuous (fun u : GeneralLinear.upperUnipotent (n + 1) F.Carrier =>
      ∑ i : Fin n, if S i then
        (u : Langlands.GeneralLinear (n + 1) F.Carrier).val i.castSucc i.succ else 0) :=
    continuous_finsetSum _ fun i _ => continuous_if_const _
      (fun _ => (GeneralLinear.entry i.castSucc i.succ).continuous.comp continuous_subtype_val)
      (fun _ => continuous_const)
  exact hψ.comp_continuous hc

/-- The simple characters `θ_S` of the mirabolic upper-unipotent group are
locally constant. -/
theorem isLocallyConstant_simpleCharacter (ψ : Multiplicative F.Carrier →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F.Carrier => (ψ (ofAdd x) : ℂ)))
    {n : ℕ} (S : Fin n → Bool) :
    letI := T.topology
    IsLocallyConstant (fun u : GeneralLinear.Mirabolic.upperUnipotent n F.Carrier =>
      (simpleCharacter ψ S u : ℂ)) := by
  let := T.topology
  exact (isLocallyConstant_selectedSum T ψ hψ S).comp_continuous
    (upperUnipotentContinuousEquiv (n := n) (F := F.Carrier)).continuous

/-- A smooth representation of `P_(n+1)` has finite length when all its
simple-character coinvariants are finite-dimensional. -/
theorem isFiniteLength_of_finiteDimensional (ψ : Multiplicative F.Carrier →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F.Carrier => (ψ (ofAdd x) : ℂ)))
    (hgen : ∀ χ : Multiplicative F.Carrier →* ℂˣ,
      (letI := T.topology; IsLocallyConstant (fun x : F.Carrier => (χ (ofAdd x) : ℂ))) →
      ∃ a : F.Carrier, ∀ x : F.Carrier, χ (ofAdd x) = ψ (ofAdd (a * x)))
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear.mirabolic n F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ)
    (hfin : ∀ S : Fin n → Bool, FiniteDimensional ℂ
      (Coinvariants σ (GeneralLinear.Mirabolic.upperUnipotent n F.Carrier)
        (simpleCharacter ψ S))) :
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F.Carrier)) σ.asModule := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let U := GeneralLinear.Mirabolic.upperUnipotent n F.Carrier
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
  let g : Submodule (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F.Carrier)) σ.asModule →
      Fin (B + 1) := fun N =>
    ⟨f ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)).symm N), hB _⟩
  have hg : StrictMono g := fun N N' h =>
    Fin.mk_lt_mk.mpr (hmono ((Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := σ)).symm.strictMono h))
  have : IsArtinian (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F.Carrier)) σ.asModule :=
    hg.wellFoundedLT
  have : IsNoetherian (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F.Carrier)) σ.asModule :=
    isNoetherian_iff.mpr hg.wellFoundedGT
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end Criterion

/-- BZ76 Corollary 5.22, (1) implies (2), from the finiteness of twisted
upper-unipotent coinvariants of irreducible smooth representations (the
finiteness part of BZ76 Theorem 5.21). -/
theorem of_irreducibleCoinvariantFiniteness
    (h : IrreducibleCoinvariantFinitenessStatement.{uF, uV}) :
    MirabolicFiniteLengthStatement.{uF, uV} := by
  intro p _ F T n V _ _ ρ hρ hfl
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨ψ, hψ, hgen⟩ := exists_generating_character T
  refine isFiniteLength_of_finiteDimensional T ψ hψ hgen
    (ρ.comp (GeneralLinear.mirabolic n F.Carrier).subtype)
    (isSmooth_comp _ continuous_subtype_val hρ) fun S => ?_
  have hrel : relations (ρ.comp (GeneralLinear.mirabolic n F.Carrier).subtype)
      (GeneralLinear.Mirabolic.upperUnipotent n F.Carrier) (simpleCharacter ψ S) =
      relations ρ (GeneralLinear.upperUnipotent (n + 1) F.Carrier) (ψ.comp (selectedSum S)) :=
    relations_eq_of_surjective ρ _ _ _ _ _ GeneralLinear.Mirabolic.upperUnipotentEquiv
      GeneralLinear.Mirabolic.upperUnipotentEquiv.surjective (fun _ => rfl) (fun _ => rfl)
  have := finiteDimensional_coinvariants_of_isFiniteLength
    (GeneralLinear.upperUnipotent (n + 1) F.Carrier) (ψ.comp (selectedSum S))
    (fun W _ _ π hπ hirr => h p F T (n + 1) W π hπ hirr _
      (isLocallyConstant_selectedSum T ψ hψ S)) ρ hρ hfl
  exact (Submodule.quotEquivOfEq _ _ hrel.symm).finiteDimensional

end Langlands.Whittaker.MirabolicFiniteLength

namespace Langlands.Whittaker

universe uF uV

/-- Bernstein--Zelevinsky (1976), Corollary 5.22, implication (1) implies (2):
a smooth finite-length representation of `GL_(n+1)(F)` restricts to a
finite-length representation of the actual mirabolic subgroup. -/
theorem mirabolicFiniteLength : MirabolicFiniteLengthStatement.{uF, uV} :=
  MirabolicFiniteLength.of_irreducibleCoinvariantFiniteness
    irreducibleCoinvariantFiniteness.{uF, uV}

end Langlands.Whittaker
