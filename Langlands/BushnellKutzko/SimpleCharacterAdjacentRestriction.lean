import Langlands.BushnellKutzko.SimpleCharacterHighExistence
import Langlands.BushnellKutzko.SimpleCharacterTwistRestriction

/-! # Adjacent restriction and nonemptiness -/

open ValuativeRel

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- At and above the cutoff, adjacent surjectivity passes from the approximating element
to the original element. The trace twists are compatible across the critical depth. -/
theorem simpleCharacters_adjacent_cons_of_twist (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (n : ℤ) (β γ : A) (tail : List A)
    (m : ℕ) :
    let r := finiteCriticalDepth L n β
    let H := fun j : ℕ => simpleHGroup L n β (γ :: tail) (j + 1)
    let H' := fun j : ℕ => simpleHGroup L n γ tail (j + 1)
    let C := simpleCharacters ψF L n β (γ :: tail)
    let C' := simpleCharacters ψF L n γ tail
    (hdiff : β - γ ∈ L.endFiltration (-r)) → (hm : r / 2 ≤ (m : ℤ)) →
    (he : ∀ j, m ≤ j → H' j = H j) →
    (∀ j (hmj : m ≤ j), (j : ℤ) < r → ∀ θ ∈ C' j,
      characterTwistTransport (he j hmj) (elementCharacterHom L ψF hψ hdiff
        (by
          have _h : (m : ℤ) ≤ j := by exact_mod_cast hmj
          omega)
        (simpleHGroup_le_unitFiltration L n γ tail (j + 1))) θ ∈ C j) →
    (fun χ : H' m →* ℂˣ => χ.comp (Subgroup.inclusion (simpleHGroup_antitone L n γ tail
      (Nat.succ_le_succ (Nat.le_succ m))))) '' C' m = C' (m + 1) →
    (fun χ : H m →* ℂˣ => χ.comp (Subgroup.inclusion (simpleHGroup_antitone L n β (γ :: tail)
      (Nat.succ_le_succ (Nat.le_succ m))))) '' C m = C (m + 1) := by
  intro r H H' C C' hdiff hm he hback hImage
  let τ := elementCharacterHom L ψF hψ hdiff (by omega :
    1 ≤ -r + (((m + 1 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ)))
    (simpleHGroup_le_unitFiltration L n γ tail (m + 1))
  have hm' : r / 2 ≤ ((m + 1 : ℕ) : ℤ) := by omega
  have hmem := simpleCharacters_twist_cons_iff_of_reverse L ψF hψ n β γ tail m
    hdiff hm (he m le_rfl) (fun h => hback m le_rfl h)
  have hmem' := simpleCharacters_twist_cons_iff_of_reverse L ψF hψ n β γ tail (m + 1)
    hdiff hm' (he (m + 1) (Nat.le_succ m)) (fun h => hback (m + 1) (Nat.le_succ m) h)
  exact restriction_image_eq_of_twistTransport (he m le_rfl) (he (m + 1) (Nat.le_succ m))
    (simpleHGroup_antitone L n γ tail (Nat.succ_le_succ (Nat.le_succ m)))
    (simpleHGroup_antitone L n β (γ :: tail) (Nat.succ_le_succ (Nat.le_succ m))) τ
    (C' m) (C m) (C' (m + 1)) (C (m + 1)) hmem hmem' hImage

/-- Both characters at adjacent high indices are given by the same trace formula. -/
theorem simpleCharacterRestriction_adjacent_high (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) {m : ℕ} (hm : S.n / 2 ≤ (m : ℤ)) :
    (simpleCharacterRestriction S q (Nat.le_succ m)) ''
        simpleCharacters ψF S.chain S.n S.b q.tail m =
      simpleCharacters ψF S.chain S.n S.b q.tail (m + 1) := by
  obtain ⟨_, θ, hθ, hv⟩ := simpleCharacters_high_singleton_of_detCriterion hDet ψF hψ q hm
  obtain ⟨_, θ', hθ', hv'⟩ := simpleCharacters_high_singleton_of_detCriterion hDet ψF hψ q
    (m := m + 1) (by omega)
  rw [hθ, hθ', Set.image_singleton, Set.singleton_eq_singleton_iff]
  apply MonoidHom.ext
  intro g
  apply Units.ext
  exact (hv _).trans (hv' g).symm

/-- A high-index singleton and adjacent surjectivity yield nonemptiness at every index below
the level. -/
theorem simpleCharacterRestriction_nonempty_of_adjacent (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {S : Stratum 𝒪[F] F V}
    (h0 : S.r = 0) (q : S.DefiningSequenceChoice) :
    let C := simpleCharacters ψF S.chain S.n S.b q.tail
    (∀ m : ℕ, (m : ℤ) + 1 < S.n →
      (simpleCharacterRestriction S q (Nat.le_succ m)) '' C m = C (m + 1)) →
    ∀ m : ℕ, (m : ℤ) < S.n → (C m).Nonempty := by
  intro C hAdj m hm
  let t := (S.n - 1).toNat
  have hn : 0 < S.n := h0 ▸ S.r_lt_n
  have ht : (t : ℤ) = S.n - 1 := Int.toNat_of_nonneg (by omega)
  obtain ⟨_, θ, hθ, _⟩ := simpleCharacters_high_singleton_of_detCriterion hDet ψF hψ q
    (m := t) (by omega)
  have htop : (C t).Nonempty := by
    rw [show C t = {θ} from hθ]
    exact Set.singleton_nonempty θ
  have hdesc (k : ℕ) (hk : k ≤ t) : (C (t - k)).Nonempty := by
    induction k with
    | zero => simpa using htop
    | succ k ih =>
      have hne := ih (by omega)
      have heq : t - (k + 1) + 1 = t - k := by omega
      have hres := hAdj (t - (k + 1)) (by omega)
      rw [← heq, ← hres] at hne
      exact hne.of_image
  have h := hdesc (t - m) (Nat.sub_le _ _)
  have heq : t - (t - m) = m := by omega
  exact (congrArg (fun i => (C i).Nonempty) heq).mp h

end

end Langlands.BushnellKutzko
