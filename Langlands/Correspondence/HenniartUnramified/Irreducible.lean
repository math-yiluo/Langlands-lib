import Langlands.Correspondence.HenniartUnramified.CoindProps

/-! # Irreducibility and the twist stabilizer of the explicit coinduction -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation LinearMap

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {D : SplitDegree G} {E : SplitDegree H} {m : ℕ}

theorem finRotate_iterate_val (d : ℕ) (k : Fin (m + 1)) :
    ((finRotate (m + 1))^[d] k : ℕ) = ((k : ℕ) + d) % (m + 1) := by
  induction d with
  | zero => simp [Nat.mod_eq_of_lt k.isLt]
  | succ d ih =>
    rw [Function.iterate_succ_apply', finRotate_apply, Fin.val_add, ih, Fin.val_one',
      Nat.add_mod_mod, Nat.mod_add_mod, add_assoc]

theorem exists_finRotate_iterate (k j : Fin (m + 1)) :
    ∃ d, (finRotate (m + 1))^[d] k = j := by
  refine ⟨(j : ℕ) + (m + 1 - k), Fin.ext ?_⟩
  rw [finRotate_iterate_val]
  have hk := k.isLt
  rw [show (k : ℕ) + ((j : ℕ) + (m + 1 - k)) = (j : ℕ) + (m + 1) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt j.isLt]

theorem finRotate_iterate_self (k : Fin (m + 1)) : (finRotate (m + 1))^[m + 1] k = k := by
  apply Fin.ext
  rw [finRotate_iterate_val, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]

section Cyc

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)

/-- The twist applied at the last coordinate. -/
def tw (k : Fin (m + 1)) (a : V) : V := if k = Fin.last m then τ E.lift a else a

theorem tw_ne_zero {k : Fin (m + 1)} {a : V} (ha : a ≠ 0) : tw (E := E) τ k a ≠ 0 := by
  unfold tw
  split_ifs
  · intro h
    apply ha
    have := congrArg (τ E.lift⁻¹) h
    rwa [Representation.inv_self_apply, map_zero] at this
  · exact ha

theorem tw_smul (k : Fin (m + 1)) (c : ℂ) (a : V) :
    tw (E := E) τ k (c • a) = c • tw (E := E) τ k a := by
  unfold tw
  split_ifs <;> simp

theorem cycUnit_single (k : Fin (m + 1)) (a : V) :
    (cycUnit E m τ : Module.End ℂ _) (Pi.single (finRotate (m + 1) k) a) =
      (Pi.single k (tw (E := E) τ k a) : Fin (m + 1) → V) := by
  funext i
  by_cases hi : i = Fin.last m
  · subst hi
    rw [cycUnit_apply_last]
    by_cases hk : k = Fin.last m
    · subst hk
      simp [tw]
    · have h0 : (0 : Fin (m + 1)) ≠ finRotate (m + 1) k := by
        rw [← finRotate_last]
        exact (finRotate (m + 1)).injective.ne (Ne.symm hk)
      have h1 : Fin.last m ≠ k := Ne.symm hk
      rw [Pi.single_eq_of_ne h0, map_zero, Pi.single_eq_of_ne h1]
  · rw [cycUnit_apply_of_ne _ _ _ _ hi]
    by_cases hik : i = k
    · subst hik
      simp [tw, hi]
    · have h0 : finRotate (m + 1) i ≠ finRotate (m + 1) k :=
        (finRotate (m + 1)).injective.ne hik
      rw [Pi.single_eq_of_ne h0, Pi.single_eq_of_ne hik]

end Cyc

namespace Stage

variable (S : Stage D E (m + 1))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)

theorem single_mem_of_cycUnit {M : Submodule ℂ (Fin (m + 1) → V)}
    (hM : ∀ g : G, ∀ v ∈ M, S.coind τ g v ∈ M) {k : Fin (m + 1)}
    (hk : ∀ a, Pi.single k a ∈ M) (a : V) : Pi.single (finRotate (m + 1) k) a ∈ M := by
  have h := hk (tw (E := E) τ k a)
  rw [← cycUnit_single, ← S.coind_lift τ] at h
  have h' := hM D.lift⁻¹ _ h
  rwa [Representation.inv_self_apply] at h'

variable [FiniteDimensional ℂ V]

/-- The coinduction of a stage representation with irreducible, pairwise unrelated inertia
blocks is irreducible. -/
theorem coind_isIrreducible [Nontrivial V]
    (hirr : ∀ k : Fin (m + 1), (S.block τ k).IsIrreducible)
    (hdist : ∀ j k : Fin (m + 1), j ≠ k →
      ∀ T : (S.block τ j).IntertwiningMap (S.block τ k), T = 0) :
    (S.coind τ).IsIrreducible := by
  classical
  let π := S.inertiaRep τ
  have hbot : (⊥ : Subrepresentation (S.coind τ)) ≠ ⊤ :=
    fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  refine { exists_pair_ne := ⟨⊥, ⊤, hbot⟩, eq_bot_or_eq_top := ?_ }
  intro W
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  let M := W.toSubmodule
  have hMstab : ∀ g : G, ∀ v ∈ M, S.coind τ g v ∈ M := fun g v hv => W.apply_mem_toSubmodule g hv
  have hM0 : M ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  -- Step A: a minimal nonzero inertia-stable subspace is a full coordinate block.
  let P : Submodule ℂ (Fin (m + 1) → V) → Prop := fun U =>
    U ≠ ⊥ ∧ U ≤ M ∧ ∀ n : D.inertia, ∀ v ∈ U, π n v ∈ U
  have hPM : P M := ⟨hM0, le_rfl, fun n v hv => by
    have := hMstab n v hv
    rwa [coind_inertia] at this⟩
  have hex : ∃ d, ∃ U, P U ∧ Module.finrank ℂ U = d := ⟨_, M, hPM, rfl⟩
  obtain ⟨U₀, hU₀, hd⟩ := Nat.find_spec hex
  have hmin : ∀ U, P U → Module.finrank ℂ U₀ ≤ Module.finrank ℂ U := fun U hU =>
    hd ▸ Nat.find_min' hex ⟨U, hU, rfl⟩
  have hdich : ∀ k : Fin (m + 1), (∀ u ∈ U₀, u k = 0) ∨ (∀ u ∈ U₀, u k = 0 → u = 0) := by
    intro k
    let K := U₀ ⊓ LinearMap.ker (LinearMap.proj k : (Fin (m + 1) → V) →ₗ[ℂ] V)
    by_cases hK : K = ⊥
    · right
      intro u hu huk
      have : u ∈ K := ⟨hu, huk⟩
      rw [hK] at this
      exact this
    · left
      have hPK : P K := ⟨hK, inf_le_left.trans hU₀.2.1, fun n v hv =>
        ⟨hU₀.2.2 n v hv.1, by
          change π n v k = 0
          rw [inertiaRep_apply]
          have : v k = 0 := hv.2
          rw [this, map_zero]⟩⟩
      have hKU : K = U₀ := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin K hPK)
      intro u hu
      have : u ∈ K := hKU ▸ hu
      exact this.2
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU₀.1
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hu₀0
  have hinj : ∀ u ∈ U₀, u k = 0 → u = 0 :=
    (hdich k).resolve_left fun h => hk (h u₀ hu₀)
  have hsurj : ∀ a : V, ∃ u ∈ U₀, u k = a := by
    let Ik : Subrepresentation (S.block τ k) :=
      ⟨U₀.map (LinearMap.proj k), fun n a ha => by
        obtain ⟨u, hu, rfl⟩ := ha
        exact ⟨π n u, hU₀.2.2 n u hu, rfl⟩⟩
    rcases (hirr k).eq_bot_or_eq_top Ik with h | h
    · exfalso
      have hmem : u₀ k ∈ Ik.toSubmodule := ⟨u₀, hu₀, rfl⟩
      rw [h] at hmem
      exact hk hmem
    · intro a
      have hmem : a ∈ Ik.toSubmodule := by rw [h]; trivial
      obtain ⟨u, hu, hua⟩ := hmem
      exact ⟨u, hu, hua⟩
  have hother : ∀ j, j ≠ k → ∀ u ∈ U₀, u j = 0 := by
    intro j hjk
    let pk : U₀ →ₗ[ℂ] V := (LinearMap.proj k) ∘ₗ U₀.subtype
    have hb : Function.Bijective pk := ⟨fun x y hxy => by
        have h := hinj (x.val - y.val) (U₀.sub_mem x.2 y.2)
          (by simpa [pk, sub_eq_zero] using hxy)
        exact Subtype.ext (sub_eq_zero.mp h),
      fun a => by
        obtain ⟨u, hu, hua⟩ := hsurj a
        exact ⟨⟨u, hu⟩, hua⟩⟩
    let e : U₀ ≃ₗ[ℂ] V := LinearEquiv.ofBijective pk hb
    let T : (S.block τ k).IntertwiningMap (S.block τ j) :=
      ⟨((LinearMap.proj j) ∘ₗ U₀.subtype) ∘ₗ e.symm.toLinearMap, fun n => by
        apply LinearMap.ext
        intro a
        let w : U₀ := e.symm a
        have hw : (w : Fin (m + 1) → V) k = a := e.apply_symm_apply a
        let w' : U₀ := ⟨π n w, hU₀.2.2 n w w.2⟩
        have hw' : e.symm (S.block τ k n a) = w' := by
          apply e.injective
          rw [e.apply_symm_apply]
          change S.block τ k n a = π n w k
          rw [inertiaRep_apply, hw]
          rfl
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hw', Submodule.coe_subtype,
          LinearMap.coe_proj, Function.eval]
        change π n w j = S.block τ j n ((w : Fin (m + 1) → V) j)
        rw [inertiaRep_apply]
        rfl⟩
    have hT := hdist k j (Ne.symm hjk) T
    intro u hu
    have h := congrArg (fun F : (S.block τ k).IntertwiningMap (S.block τ j) => F (e ⟨u, hu⟩)) hT
    simpa [T] using h
  have hsingle : ∀ a, Pi.single k a ∈ M := by
    intro a
    obtain ⟨u, hu, hua⟩ := hsurj a
    have : u = Pi.single k a := by
      funext i
      by_cases hik : i = k
      · subst hik
        simpa using hua
      · rw [Pi.single_eq_of_ne hik]
        exact hother i hik u hu
    exact hU₀.2.1 (this ▸ hu)
  -- Step B: rotate the block.
  have hrot : ∀ d a, Pi.single ((finRotate (m + 1))^[d] k) a ∈ M := by
    intro d
    induction d with
    | zero => exact hsingle
    | succ d ih =>
      intro a
      rw [Function.iterate_succ_apply']
      exact S.single_mem_of_cycUnit τ hMstab ih a
  have hall : ∀ j a, Pi.single j a ∈ M := by
    intro j a
    obtain ⟨d, hd⟩ := exists_finRotate_iterate k j
    have h := hrot d a
    rwa [hd] at h
  apply Subrepresentation.toSubmodule_injective
  apply eq_top_iff.mpr
  intro v _
  rw [← Finset.univ_sum_single v]
  exact Submodule.sum_mem _ fun j _ => hall j (v j)

/-- An unramified self-twist of the coinduction has order dividing `m + 1`. -/
theorem pow_eq_one_of_twist_equiv [Nontrivial V]
    (hirr : ∀ k : Fin (m + 1), (S.block τ k).IsIrreducible)
    (hdist : ∀ j k : Fin (m + 1), j ≠ k →
      ∀ T : (S.block τ j).IntertwiningMap (S.block τ k), T = 0)
    (u : ℂˣ) (e : (Langlands.twist (Weil.Local.unramifiedCharacter D.degree u).toMonoidHom
      (S.coind τ)).Equiv (S.coind τ)) : u ^ (m + 1) = 1 := by
  classical
  let χ := (Weil.Local.unramifiedCharacter D.degree u).toMonoidHom
  have hχN (n : D.inertia) : χ n = 1 :=
    Weil.Local.unramifiedCharacter_on_kernel _ _ n.property
  have hχT : χ D.lift = u := Weil.Local.unramifiedCharacter_degree_one _ _ D.lift_degree
  let T : (Fin (m + 1) → V) →ₗ[ℂ] (Fin (m + 1) → V) := e.toLinearMap
  have hTn : ∀ n : D.inertia,
      T ∘ₗ blockRep (fun k : Fin (m + 1) => S.block τ k) n =
        blockRep (fun k : Fin (m + 1) => S.block τ k) n ∘ₗ T := by
    intro n
    have h := e.isIntertwining' (n : G)
    change T ∘ₗ ((χ n : ℂ) • S.coind τ n) = S.coind τ n ∘ₗ T at h
    rwa [hχN, Units.val_one, one_smul, coind_inertia] at h
  obtain ⟨c, hc⟩ := blockRep_endo_diag _ hirr hdist T hTn
  have hTsingle : ∀ k a, T (Pi.single k a) = Pi.single k (c k • a) := by
    intro k a
    funext i
    rw [hc]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [Pi.single_eq_of_ne hik]
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  have hc0 : c 0 ≠ 0 := by
    intro h0
    apply ha
    have h := hTsingle 0 a
    rw [h0, zero_smul, Pi.single_zero] at h
    have := e.toLinearEquiv.injective (h.trans (map_zero T).symm)
    have := congrFun this 0
    simpa using this
  have hrel : ∀ k, c (finRotate (m + 1) k) = u * c k := by
    intro k
    have h := LinearMap.congr_fun (e.isIntertwining' D.lift) (Pi.single (finRotate (m + 1) k) a)
    change T ((χ D.lift : ℂ) • S.coind τ D.lift (Pi.single (finRotate (m + 1) k) a)) =
      S.coind τ D.lift (T (Pi.single (finRotate (m + 1) k) a)) at h
    rw [hχT, coind_lift, hTsingle, cycUnit_single, map_smul, hTsingle, cycUnit_single,
      tw_smul] at h
    have hk := congrFun h k
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_smul] at hk
    exact (smul_left_injective ℂ (tw_ne_zero (E := E) τ (k := k) ha) hk).symm
  have hiter : ∀ d, c ((finRotate (m + 1))^[d] 0) = (u : ℂ) ^ d * c 0 := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => rw [Function.iterate_succ_apply', hrel, ih, pow_succ]; ring
  have h := hiter (m + 1)
  rw [finRotate_iterate_self] at h
  have h1 : (u : ℂ) ^ (m + 1) = 1 := by
    have := mul_right_cancel₀ hc0 (h.symm.trans (one_mul (c 0)).symm)
    exact this
  exact Units.ext (by simpa using h1)

end Stage

end Langlands.FiniteRepresentation.SplitDegree
