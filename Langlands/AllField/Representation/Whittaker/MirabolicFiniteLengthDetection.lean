import Langlands.Representation.Whittaker.MirabolicFiniteLengthDetection
import Langlands.AllField.Representation.Derivative.MirabolicCharacter
import Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthCharacters
/-!
# Detection of nonzero mirabolic representations by twisted coinvariants

A smooth representation of the actual mirabolic group is zero as soon as its
coinvariants vanish for all the characters `θ_S` of the upper-unipotent group,
`θ_S(u) = ψ(∑_{i ∈ S} u_{i,i+1})`, `S` a set of simple roots. The radical step
uses a nonzero vector, a maximal ideal of the group algebra of the radical and
the classification of its locally constant characters.
-/

noncomputable section

open Multiplicative

namespace Langlands.AllField.Whittaker.MirabolicFiniteLength
open Langlands.Whittaker.MirabolicFiniteLength hiding additiveLattice_mul_mem div_mem_additiveLattice exists_dotProduct_eq exists_exact_conductor exists_generating_character exists_mem_additiveLattice exists_mul_eq exists_mul_eq_on_additiveLattice exists_relations_ne_top exists_trivial_additiveLattice finite_quotient_additiveLattice isLimitOfCompactSubgroups_pi mem_additiveLattice_of_forall_mul
open Langlands.AllField.Whittaker.MirabolicFiniteLength
open Langlands.Whittaker
open Langlands.AllField.Whittaker

open Langlands.Jacquet.Localization

universe uA uE uG uF

section Relations

variable {G : Type uG} [Group G]
variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Relations

section Abelian

variable {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

end Abelian

section Characters

open Langlands.GeneralLinear.Mirabolic

variable {F : Type uF} [CommRing F] {n : ℕ}

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

end Characters

section Padic

open Matrix
open Langlands.GeneralLinear.Mirabolic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The vector group `F^m` is exhausted by the compact open lattices `L_k^m`. -/
theorem isLimitOfCompactSubgroups_pi (m : ℕ) :
    letI := T.topology
    IsLimitOfCompactSubgroups (⊤ : Subgroup (Multiplicative (Fin m → F))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply isLimitOfCompactSubgroups_top
  intro C hC
  let Λ : ℤ → Subgroup (Multiplicative (Fin m → F)) := fun k =>
    { carrier := {v | ∀ i, toAdd v i ∈ T.additiveLattice k}
      mul_mem' := fun ha hb i => (T.additiveLattice k).add_mem (ha i) (hb i)
      one_mem' := fun _ => (T.additiveLattice k).zero_mem
      inv_mem' := fun ha i => (T.additiveLattice k).neg_mem (ha i) }
  have hmem : ∀ k v, v ∈ Λ k ↔ ∀ i, toAdd v i ∈ T.additiveLattice k := fun _ _ => Iff.rfl
  have hcompact : ∀ k, IsCompact (Λ k : Set (Multiplicative (Fin m → F))) := by
    intro k
    have hc := (isCompact_univ_pi fun _ : Fin m => T.isCompact_additiveLattice k).image
      (continuous_ofAdd (X := Fin m → F))
    convert hc using 1
    ext v
    constructor
    · intro hv
      exact ⟨toAdd v, fun i _ => hv i, rfl⟩
    · rintro ⟨w, hw, rfl⟩ i
      exact hw i (Set.mem_univ i)
  have hopen : ∀ k, IsOpen (Λ k : Set (Multiplicative (Fin m → F))) := by
    intro k
    have ho := (isOpen_set_pi Set.finite_univ fun (i : Fin m) _ =>
      T.isOpen_additiveLattice k).preimage (continuous_toAdd (X := Fin m → F))
    convert ho using 1
    ext v
    simp only [SetLike.mem_coe, hmem, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  have hcover : C ⊆ ⋃ k, (Λ k : Set (Multiplicative (Fin m → F))) := by
    intro v _
    have hk : ∀ i, ∃ k : ℤ, toAdd v i ∈ T.additiveLattice k :=
      fun i => exists_mem_additiveLattice T (toAdd v i)
    choose k hk using hk
    obtain ⟨M, hM⟩ := Finite.exists_le k
    exact Set.mem_iUnion.mpr ⟨M, fun i => T.additiveLattice_mono (hM i) (hk i)⟩
  have hmono : Monotone fun k => (Λ k : Set (Multiplicative (Fin m → F))) :=
    fun j k hjk v hv i => T.additiveLattice_mono hjk (hv i)
  obtain ⟨k, hk⟩ := hC.elim_directed_cover _ hopen hcover hmono.directed_le
  exact ⟨Λ k, hcompact k, hk⟩

/-- A nonzero smooth representation of the actual mirabolic group `P_(n+1)` has
nonzero coinvariants for some simple character `θ_S` of its upper-unipotent
subgroup. Here `ψ` generates the locally constant characters of `F`. -/
theorem exists_relations_ne_top (ψ : Multiplicative F →* ℂˣ)
    (hgen : ∀ χ : Multiplicative F →* ℂˣ,
      (letI := T.topology; IsLocallyConstant (fun x : F => (χ (ofAdd x) : ℂ))) →
      ∃ a : F, ∀ x : F, χ (ofAdd x) = ψ (ofAdd (a * x)))
    (n : ℕ) :
    ∀ {E : Type uE} [AddCommGroup E] [Module ℂ E]
      (σ : Representation ℂ (GeneralLinear.mirabolic n F) E),
      (letI := T.topology; IsSmooth σ) → ∀ {e : E}, e ≠ 0 →
      ∃ S : Fin n → Bool,
        relations σ (GeneralLinear.Mirabolic.upperUnipotent n F)
          (simpleCharacter ψ S) ≠ ⊤ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  induction n with
  | zero =>
    intro E _ _ σ _ e he
    refine ⟨fun i => i.elim0, fun h => he ?_⟩
    have hmem : e ∈ relations σ (GeneralLinear.Mirabolic.upperUnipotent 0 F)
        (simpleCharacter ψ fun i => i.elim0) := h ▸ Submodule.mem_top
    rw [relations_eq_bot_of_subsingleton] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  | succ n ih =>
    intro E _ _ σ hσ e he
    let R := radical (n + 1) F
    -- the radical as the vector group `F^(n+1)`
    let φ : Multiplicative (Fin (n + 1) → F) →* GeneralLinear.mirabolic (n + 1) F :=
      R.subtype.comp radicalEquiv.symm.toMonoidHom
    have hφ : Continuous φ :=
      continuous_subtype_val.comp (radicalContinuousEquiv (n := n + 1) (F := F)).symm.continuous
    have hσR : IsSmooth (σ.comp φ) := isSmooth_comp φ hφ hσ
    obtain ⟨χ, hχloc, hχe⟩ := exists_character_not_mem_relations
      (isLimitOfCompactSubgroups_pi T (n + 1)) (σ.comp φ) hσR he
    obtain ⟨a, ha⟩ := exists_dotProduct_eq T ψ hgen χ (hχloc.comp_continuous continuous_ofAdd)
    -- move `χ` to a radical character by the Levi action
    obtain ⟨g, b, hgb⟩ : ∃ (g : Langlands.GeneralLinear (n + 1) F) (b : Bool),
        ∀ v : Fin (n + 1) → F,
          χ (ofAdd (g.val *ᵥ v)) = ψ (ofAdd (if b then v (Fin.last n) else 0)) := by
      by_cases ha0 : a = 0
      · refine ⟨1, false, fun v => ?_⟩
        rw [ha, ha0, zero_dotProduct]
        rfl
      · obtain ⟨g, hg⟩ := exists_dotProduct_mulVec_eq_last a ha0
        exact ⟨g, true, fun v => by rw [ha, hg]; rfl⟩
    let θR : R →* ℂˣ := χ.comp radicalEquiv.toMonoidHom
    have hθR : ∀ w : Fin (n + 1) → F, θR (radicalElement w) = χ (ofAdd w) := by
      intro w
      change χ (radicalEquiv (radicalEquiv.symm (ofAdd w))) = χ (ofAdd w)
      rw [MulEquiv.apply_symm_apply]
    have hrelR : relations (σ.comp φ) ⊤ (χ.comp (⊤ : Subgroup _).subtype) =
        relations σ R θR := by
      refine relations_eq_of_surjective σ R θR (σ.comp φ) ⊤ _
        (fun u => radicalEquiv.symm u.val) ?_ (fun _ => rfl) ?_
      · intro u
        exact ⟨⟨radicalEquiv u, Subgroup.mem_top _⟩, radicalEquiv.symm_apply_apply u⟩
      · intro u
        change χ u.val = χ (radicalEquiv (radicalEquiv.symm u.val))
        rw [MulEquiv.apply_symm_apply]
    rw [hrelR] at hχe
    have hU : ∀ u : R, levi g * u * (levi g)⁻¹ ∈ R := fun u =>
      (Subgroup.mem_normalizer_iff.mp (leviSubgroup_le_normalizer ⟨g, rfl⟩) u).mp u.property
    have hθ : ∀ u : R, θR ⟨levi g * u * (levi g)⁻¹, hU u⟩ = radicalCharacter ψ n b u := by
      intro u
      obtain ⟨v, rfl⟩ := radicalEquiv.symm.surjective u
      have hconj : (⟨levi g * (radicalEquiv.symm v).val * (levi g)⁻¹, hU _⟩ : R) =
          radicalElement (g.val *ᵥ v.toAdd) :=
        Subtype.ext (levi_conjugate_radicalElement g v.toAdd)
      rw [hconj, hθR, hgb, radicalCharacter_apply, radicalEquiv_symm_apply,
        radicalCoordinates_element]
    let θb := radicalCharacter ψ n b
    have he' : σ (levi g)⁻¹ e ∉ relations σ R θb := by
      intro hrel
      apply hχe
      have h := apply_mem_relations σ R θb θR (levi g) hU hθ hrel
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] at h
    -- pass to the radical quotient, a smooth representation of `P_(n+1)`
    have hτ : IsSmooth (radicalQuotient σ ψ b) :=
      isSmooth_comp successorEquiv.toMonoidHom
        (successorContinuousEquiv (n := n) (F := F)).continuous
        (isSmooth_action σ R θb (successorSubgroup n F) successorSubgroup_le_normalizer
          (radicalCharacter_isInvariant ψ n b) hσ)
    have hne : mk σ R θb (σ (levi g)⁻¹ e) ≠ 0 := by
      rw [Ne, mk_eq_zero]
      exact he'
    obtain ⟨S', hS'⟩ := ih (radicalQuotient σ ψ b) hτ hne
    refine ⟨Fin.snoc S' b, fun htop => hS' ?_⟩
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := mk_surjective σ R θb q
    exact mk_mem_relations σ ψ S' b (htop ▸ Submodule.mem_top)

end Padic

end Langlands.AllField.Whittaker.MirabolicFiniteLength
