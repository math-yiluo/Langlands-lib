import Langlands.Global.Arithmetic.GeneralPositionStatement
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Irreducibility from separated normal-subgroup characters

This internal algebraic step in Harris's exact-stabilizer criterion uses the
Library's actual finite-index induction, represented by equivariant functions.
-/

noncomputable section

universe uG uX uI

namespace Langlands.Global.GeneralPosition

private theorem single_mem_of_diagonal_separation
    {ι : Type uI} [Fintype ι] [DecidableEq ι] {X : Type uX}
    (W : Submodule ℂ (ι → ℂ)) (a : X → ι → ℂ)
    (stable : ∀ x v, v ∈ W → (fun i => a x i * v i) ∈ W)
    (separate : ∀ i j, i ≠ j → ∃ x, a x i ≠ a x j)
    (v : ι → ℂ) (hv : v ∈ W) (i : ι) :
    Pi.single i (v i) ∈ W := by
  classical
  have eliminate : ∀ s : Finset ι, i ∉ s →
      ∃ w ∈ W, w i = v i ∧ ∀ j ∈ s, w j = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨v, hv, rfl, by simp⟩
    | @insert j s hjs ih =>
      intro his
      obtain ⟨w, hw, hwi, hws⟩ := ih (fun h => his (Finset.mem_insert_of_mem h))
      obtain ⟨x, hx⟩ := separate i j (by
        intro h
        exact his (by simp [h]))
      let w' : ι → ℂ := (a x i - a x j)⁻¹ •
        ((fun k => a x k * w k) - a x j • w)
      refine ⟨w', W.smul_mem _ (W.sub_mem (stable x w hw) (W.smul_mem _ hw)), ?_, ?_⟩
      · dsimp [w']
        rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hx), one_mul, hwi]
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp [w']
        · simp [w', hws k hk]
  obtain ⟨w, hw, hwi, hws⟩ := eliminate (Finset.univ.erase i) (by simp)
  have heq : w = Pi.single i (v i) := by
    funext j
    by_cases h : j = i
    · subst j
      simpa using hwi
    · simp [h, hws j (by simp [h])]
  exact heq ▸ hw

private theorem irreducible_of_diagonal_coordinates
    {G : Type uG} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type uI} [Fintype ι] [Nonempty ι] {X : Type uX}
    (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] (ι → ℂ))
    (b : X → G) (a : X → ι → ℂ)
    (diagonal : ∀ x v i, e (ρ (b x) v) i = a x i * e v i)
    (separate : ∀ i j, i ≠ j → ∃ x, a x i ≠ a x j)
    (move : ∀ i j, ∃ g : G, ∀ v, e (ρ g v) j = e v i) :
    Representation.IsIrreducible ρ := by
  classical
  have hbot : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    let v := e.symm (fun _ => 1)
    have hv : v ∈ (⊥ : Subrepresentation ρ) := h ▸ Set.mem_univ v
    have hv0 : v = 0 := hv
    have := congrArg (fun w => e w (Classical.choice ‹Nonempty ι›)) hv0
    simp [v] at this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbot⟩, eq_bot_or_eq_top := ?_ }
  intro U
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  have hU' : U.toSubmodule ≠ ⊥ := fun h => hU
    (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := U.toSubmodule.ne_bot_iff.mp hU'
  have hev : e v ≠ 0 := by simpa using hv0
  obtain ⟨i, hi⟩ : ∃ i, e v i ≠ 0 := by
    by_contra! h
    exact hev (funext h)
  let W := U.toSubmodule.map e.toLinearMap
  have stable : ∀ x w, w ∈ W → (fun j => a x j * w j) ∈ W := by
    intro x w hw
    obtain ⟨z, hz, rfl⟩ := hw
    refine ⟨ρ (b x) z, U.apply_mem_toSubmodule _ hz, ?_⟩
    funext j
    exact diagonal x z j
  have project := single_mem_of_diagonal_separation W a stable separate
  have hsingle : Pi.single i (e v i) ∈ W :=
    project (e v) ⟨v, hv, rfl⟩ i
  have hequiv : ∀ w : ι → ℂ, w ∈ W ↔ e.symm w ∈ U :=
    fun _ => Submodule.mem_map_equiv U.toSubmodule
  have hall : ∀ (j : ι) (c : ℂ), Pi.single j c ∈ W := by
    intro j c
    obtain ⟨g, hg⟩ := move i j
    let z := e.symm (Pi.single i (e v i))
    have hz : z ∈ U := (hequiv _).mp hsingle
    have hgz : e (ρ g z) ∈ W :=
      ⟨ρ g z, U.apply_mem_toSubmodule g hz, rfl⟩
    have hp := project _ hgz j
    have hval : e (ρ g z) j = e v i := by simpa [z] using hg z
    rw [hval] at hp
    have hc := W.smul_mem (c / e v i) hp
    convert hc using 1
    ext k
    by_cases h : k = j
    · subst k
      simp [div_mul_cancel₀ c hi]
    · simp [h]
  apply le_antisymm le_top
  intro z _
  have hez : e z ∈ W := by
    rw [← Finset.univ_sum_single (e z)]
    exact W.sum_mem (fun j _ => hall j (e z j))
  simpa using (hequiv _).mp hez

open FiniteRepresentation

private def scalarCoordinates {G : Type uG} [Group G]
    (H : Subgroup G) (χ : H →* ℂˣ) :
    Representation.coindV H.subtype (characterLine.{uG, 0} χ).representation ≃ₗ[ℂ]
      (Induction.Cosets H → ℂ) :=
  (Induction.coordinates H (characterLine χ)).trans
    (LinearEquiv.piCongrRight fun _ => ULift.moduleEquiv)

private theorem scalarCoordinates_apply {G : Type uG} [Group G]
    (H : Subgroup G) (χ : H →* ℂˣ)
    (f : Representation.coindV H.subtype (characterLine.{uG, 0} χ).representation)
    (q : Induction.Cosets H) :
    scalarCoordinates H χ f q = (f.1 q.out).down := rfl

theorem induce_irreducible_of_separation
    {G : Type uG} [Group G] (H N : Subgroup G) [H.FiniteIndex] [N.Normal]
    (hNH : N ≤ H) (χ : H →* ℂˣ)
    (separate : ∀ x y : G, Induction.coset H x ≠ Induction.coset H y →
      ∃ n : N,
        (χ.comp (Subgroup.inclusion hNH)) (MulAut.conjNormal x n) ≠
        (χ.comp (Subgroup.inclusion hNH)) (MulAut.conjNormal y n)) :
    (induce H (characterLine.{uG, 0} χ)).IsIrreducible := by
  classical
  let := Subgroup.fintypeQuotientOfFiniteIndex (H := H)
  let : Nonempty (Induction.Cosets H) := ⟨Induction.coset H 1⟩
  let a (n : N) (q : Induction.Cosets H) : ℂ :=
    (χ.comp (Subgroup.inclusion hNH)) (MulAut.conjNormal q.out n)
  apply irreducible_of_diagonal_coordinates
    (Representation.coind H.subtype (characterLine χ).representation)
    (scalarCoordinates H χ) (fun n : N => n.1) a
  · intro n f q
    rw [scalarCoordinates_apply]
    change (f.1 (q.out * n)).down = _
    have hf := f.2
      (Subgroup.inclusion hNH (MulAut.conjNormal q.out n)) q.out
    have hmul : (q.out * (n : G) * q.out⁻¹) * q.out = q.out * n := by
      group
    have hf' := congrArg ULift.down hf
    change (f.1 ((q.out * (n : G) * q.out⁻¹) * q.out)).down =
      (χ (Subgroup.inclusion hNH (MulAut.conjNormal q.out n)) : ℂ) *
        (f.1 q.out).down at hf'
    rw [hmul] at hf'
    exact hf'
  · intro q r hqr
    obtain ⟨n, hn⟩ := separate q.out r.out (by
      simpa only [Induction.coset_out] using hqr)
    exact ⟨n, Units.val_injective.ne hn⟩
  · intro q r
    refine ⟨r.out⁻¹ * q.out, ?_⟩
    intro f
    change (f.1 (r.out * (r.out⁻¹ * q.out))).down = (f.1 q.out).down
    simp

end Langlands.Global.GeneralPosition
