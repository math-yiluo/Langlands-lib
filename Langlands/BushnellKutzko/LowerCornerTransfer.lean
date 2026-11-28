import Langlands.BushnellKutzko.LowerCornerCovariance
import Langlands.BushnellKutzko.CentralizerDoubleCoset
import Langlands.BushnellKutzko.FiniteCharacterComparison
import Langlands.BushnellKutzko.PairingTransfer

/-! # Isotypic transfer from the shifted lower-corner kernel -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV uW

local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

/-- Let `K` be the subgroup of `H^m` with lower corner in `P^(m+1)`. The
twisted simple character on `K` transfers from the kernel of the shifted
lower-corner map once the upper block units preserve `H^m` and fix the
character on the kernel. The reference trace pairing supplies separation. -/
def LowerCornerTransferStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (_h0 : S.r = 0) (_hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (i : ℕ), let m := i + 1
    (m : ℤ) < S.n →
    ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
    ∀ (θ : H[S,q] m →* ℂˣ), θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i →
    ∀ (e₁ e₂ ζ' c : Module.End F V) (hadd : e₁ + e₂ = 1) (_h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
      (he₁ : e₁ ∈ centralizerLattice S.chain S.b 0) (he₂ : e₂ ∈ centralizerLattice S.chain S.b 0)
      (_hζ' : ζ' ∈ centralizerLattice S.chain S.b (-1)), Commute c e₁ → Commute c e₂ →
    c ∈ S.chain.endFiltration (-(m : ℤ)) →
    ∀ (I X : Submodule 𝒪[F] (Module.End F V)), I ≤ S.chain.endFiltration 1 →
    Hₗ[S,q] m ≤ X → X ≤ S.chain.endFiltration m →
    traceDualLattice ψF X = I.map (adjointMap 𝒪[F] S.b) ⊔ S.chain.endFiltration (1 - (m : ℤ)) →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Module.End F V)ˣ W) (M : Subgroup (Module.End F V)ˣ),
    M ≤ blockUnipotent e₁ e₂ h₂₁ ⊤ →
    let K := lowerBlockSimpleHGroup S q hadd he₁ he₂ m (Nat.succ_pos i)
    let u := fun y : I => blockUnit e₁ e₂ h₂₁ (ζ' * (y : Module.End F V))
    ∀ (ϑ : K →* ℂˣ),
    (∀ k : K, (ϑ k : ℂ) = (θ ⟨k, k.2.1⟩ : ℂ) * elementCharacter (traceCharacter ψF) c k) →
    (∀ (y : I) k, k ∈ H[S,q] m → u y * k * (u y)⁻¹ ∈ H[S,q] m) →
    (∀ (y : I) (k : K) (hk : u y * (k : (Module.End F V)ˣ) * (u y)⁻¹ ∈ K),
      e₂ * ((k : (Module.End F V)ˣ) - 1 : Module.End F V) * e₁ * ζ' ∈ X →
      ϑ ⟨_, hk⟩ = ϑ k) →
    ∀ v : W,
    (∀ k : K, e₂ * ((k : (Module.End F V)ˣ) - 1 : Module.End F V) * e₁ * ζ' ∈ X →
      ρ k v = (ϑ k : ℂ) • v) →
    v ∉ Jacquet.relations ρ M →
    ∃ w : W, (∀ k : K, ρ k w = (ϑ k : ℂ) • w) ∧ w ∉ Jacquet.relations ρ M

set_option maxHeartbeats 1500000 in
theorem exists_isotypic_of_lowerCornerKernel : LowerCornerTransferStatement.{uF, uV, uW} := by
  intro F _ _ _ _ V _ _ S h0 hs q ψF hψ i m hn hcrit θ hθ e₁ e₂ ζ' c hadd h₁₂ h₂₁ he₁ he₂ hζ'
    hc₁ hc₂ hc I X hI hHX hXP hdual W _ _ ρ M hM K u ϑ hϑ hHnorm hfix v hv hvM
  have hm : 1 ≤ m := Nat.succ_pos i
  let A := Module.End F V
  let G := (Module.End F V)ˣ
  let T := Hₗ[S,q] (m + 1)
  let Y := lowerCornerQuotient T X e₁ e₂ ζ'
  let p : K →* Multiplicative Y := lowerCornerQuotientHom S q hadd he₁ he₂ m hm h0 hs X hHX hζ'
  obtain ⟨hfin, hp, hker⟩ := lowerCornerQuotientProperties F V S h0 hs q e₁ e₂ ζ'
    hadd h₁₂ he₁ he₂ hζ' m hm X hHX
  let : Finite Y := hfin
  let g : Multiplicative I →* G :=
    { toFun := fun y => u y.toAdd
      map_one' := by
        apply Units.ext
        change 1 + e₁ * (ζ' * (0 : A)) * e₂ = 1
        simp
      map_mul' := fun y y' => by
        change blockUnit e₁ e₂ h₂₁ (ζ' * ((y.toAdd : A) + (y'.toAdd : A))) = _
        rw [mul_add, blockUnit_add] }
  have hg (y : I) (k : G) (hk : k ∈ K) : g (.ofAdd y) * k * (g (.ofAdd y))⁻¹ ∈ K := by
    have hcorner := blockUnit_conj_lowerCorner h₂₁ (ζ' * (y : A)) k
    exact ⟨hHnorm y k hk.1, hcorner ▸ hk.2⟩
  have hpconj (y : I) (k : K) : p (conjEndo K (g (.ofAdd y)) (hg y) k) = p k := by
    apply congrArg (fun x : T => Multiplicative.ofAdd (Submodule.Quotient.mk x : Y))
    apply Subtype.ext
    exact blockUnit_conj_lowerCorner h₂₁ (ζ' * (y : A)) k
  have hfix' (y : I) (k : K) (hk : p k = 1) :
      ϑ (conjEndo K (g (.ofAdd y)) (hg y) k) = ϑ k :=
    hfix y k (hg y k k.2) ((hker k).mp hk)
  let a := Jacquet.quotientConjRatios ϑ p hp g hg hpconj hfix'
  have hID : I.map (adjointMap 𝒪[F] S.b) ≤ traceDualLattice ψF X := hdual ▸ le_sup_left
  let b := lowerCornerTracePairing ψF S.b e₁ e₂ ζ' I T X hID
  have hsep := lowerCornerTracePairing_separates ψF S.b e₁ e₂ ζ' I T X hID S.chain hψ m hXP
    inf_le_right he₁.1 he₂.1 hζ'.1 hdual
  have hK : H[S,q] (m + 1) ≤ K := by
    intro k hk
    refine ⟨simpleHGroup_antitone _ _ _ _ (Nat.le_succ m) hk, ?_⟩
    have hkP := (simpleHGroup_le_unitFiltration _ _ _ _ _ hk).2.2
    exact mul_mul_mem_endFiltration S.chain he₂.1 hkP he₁.1 (by ring)
  let θ' := θ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail (Nat.le_succ m)))
  have hθ' : θ' ∈ simpleCharacters ψF S.chain S.n S.b q.tail m :=
    simpleCharacters_restrict_forward ψF S h0 hs q (Nat.le_succ i) hn hcrit hθ
  have hcomp : a.ker ≤ b.ker := by
    intro y hy
    have ha : a y = 0 := AddMonoidHom.mem_ker.mp hy
    have hϑfix (k : K) : ϑ (conjEndo K (g (.ofAdd y)) (hg y) k) = ϑ k := by
      have h := Jacquet.quotientConjRatios_apply ϑ p hp g hg hpconj hfix' y k
      change a y (p k).toAdd = _ at h
      rw [ha, AddChar.zero_apply] at h
      exact (div_eq_one.mp (Units.ext (h.symm.trans Units.val_one.symm))).symm
    have hyP : ζ' * (y : A) ∈ S.chain.endFiltration 0 := by
      simpa using S.chain.mul_mem_endFiltration hζ'.1 (hI y.2)
    have hW : e₁ * (ζ' * (y : A)) * e₂ ∈ S.chain.endFiltration 0 :=
      mul_mul_mem_endFiltration S.chain he₁.1 hyP he₂.1 (by ring)
    have h1 : (1 : A) ∈ S.chain.endFiltration 0 := S.chain.order.one_mem
    have hgP : (u y : A) ∈ S.chain.endFiltration 0 := add_mem h1 hW
    have hgP' : (↑(u y)⁻¹ : A) ∈ S.chain.endFiltration 0 := sub_mem h1 hW
    have hnext (k : G) (hk : k ∈ H[S,q] (m + 1)) : u y * k * (u y)⁻¹ ∈ H[S,q] (m + 1) := by
      rw [simpleHGroup_succ_eq_inf S h0 hs q hm] at hk ⊢
      exact ⟨hHnorm y k hk.1, conj_mem_unitFiltration S.chain (by omega) hgP hgP' hk.2⟩
    have hθfix : u y ∈ characterSelfIntertwining θ' := by
      intro k hk
      let k₀ : K := ⟨k, hK k.2⟩
      let k₁ := conjEndo K (g (.ofAdd y)) (hg y) k₀
      have h : (ϑ k₁ : ℂ) = (ϑ k₀ : ℂ) := congrArg Units.val (hϑfix k₀)
      rw [hϑ k₁, hϑ k₀] at h
      have ht := blockUnit_elementCharacter_conj_eq S.chain hψ h₂₁ hc₁ hc₂ m hc hyP
        (k : G) k₀.2.2
      change (θ' ⟨_, hk⟩ : ℂ) *
        elementCharacter (traceCharacter ψF) c (u y * (k : G) * (u y)⁻¹) =
          (θ' k : ℂ) * elementCharacter (traceCharacter ψF) c (k : G) at h
      rw [ht] at h
      exact Units.ext (mul_right_cancel₀ ((traceCharacter ψF).val_isUnit _).ne_zero h)
    have hd := conjugationDifference_mem_traceDual_of_fixed S h0 hs q hψ m hn hcrit hθ' hnext hθfix
    change (↑(blockUnit e₁ e₂ h₂₁ (ζ' * (y : A)))⁻¹ : A) * S.b *
      (blockUnit e₁ e₂ h₂₁ (ζ' * (y : A)) : A) - S.b ∈ traceDualLattice ψF T at hd
    rw [blockUnit_conjugationDifference h₂₁ S.b _ (commute_of_mem_centralizerLattice he₁)] at hd
    apply AddMonoidHom.mem_ker.mpr
    ext z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [AddChar.zero_apply, lowerCornerTracePairing_upper_mk ψF S.b e₁ e₂ ζ' I T X hID
      (commute_of_mem_centralizerLattice he₁) (commute_of_mem_centralizerLattice he₂)
      (commute_of_mem_centralizerLattice hζ')]
    exact hd (x : A) x.2
  have hsurj := surjective_of_character_separation a b hcomp hsep
  have h₁ : e₁ * e₁ = e₁ := by
    calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, h₁₂, add_zero]
      _ = e₁ := by rw [hadd, mul_one]
  have h₂ : e₂ * e₂ = e₂ := by
    calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, h₁₂, zero_add]
      _ = e₂ := by rw [hadd, one_mul]
  have hgM (y : I) (k : G) (hk : k ∈ M) : (g (.ofAdd y))⁻¹ * k * g (.ofAdd y) ∈ M := by
    have hcomm : g (.ofAdd y) * k = k * g (.ofAdd y) :=
      blockUnipotent_commute (blockUnit_mem h₂₁ h₁ h₂ _) (hM hk)
    rwa [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  exact Jacquet.exists_isotypic_not_mem_relations_of_quotientConjRatios ρ M ϑ p hp g hg hpconj hfix'
    hsurj hgM (fun k hk => hv k ((hker k).mp hk)) hvM

end Langlands.BushnellKutzko.SplitBlocks
