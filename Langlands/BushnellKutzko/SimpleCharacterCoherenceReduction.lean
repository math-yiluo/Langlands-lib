import Langlands.BushnellKutzko.SimpleCharacterCoherenceStatement
import Langlands.BushnellKutzko.SimpleCharacterHighIndex
import Langlands.BushnellKutzko.SimpleCharacterRestrictionStatement
import Langlands.BushnellKutzko.SimpleCharacterSequence
import Langlands.BushnellKutzko.SimpleCharacterTernary
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement

/-! # Descending induction for coherence of simple character sets -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uG

section Characters

variable {G : Type uG} [Group G]

/-- Transport a character set along equality of its domain subgroup. -/
def transportCharacterSet {H H' : Subgroup G} (h : H = H') (C : Set (H →* ℂˣ)) :
    Set (H' →* ℂˣ) := Eq.ndrec (motive := fun K : Subgroup G => Set (K →* ℂˣ)) C h

private theorem transportCharacterSet_restriction_image {H H' K K' : Subgroup G}
    (h : H = H') (hk : K = K') (i : K ≤ H) (i' : K' ≤ H') (C : Set (H →* ℂˣ)) :
    transportCharacterSet hk ((fun χ => χ.comp (Subgroup.inclusion i)) '' C) =
      (fun χ => χ.comp (Subgroup.inclusion i')) '' transportCharacterSet h C := by
  cases h
  cases hk
  rfl

private theorem mem_characterSelfIntertwining_div {H : Subgroup G} {χ φ : H →* ℂˣ} {a : G}
    (hχ : a ∈ characterSelfIntertwining χ) (hφ : a ∈ characterSelfIntertwining φ) :
    a ∈ characterSelfIntertwining (χ / φ) := by
  intro g hg
  rw [MonoidHom.div_apply, MonoidHom.div_apply, hχ g hg, hφ g hg]

private theorem characterSets_eq_of_restriction_image_eq {H K : Subgroup G} (i : K ≤ H)
    (C D : Set (H →* ℂˣ)) {θ : H →* ℂˣ} (hθC : θ ∈ C) (hθD : θ ∈ D)
    (hC : ∀ ⦃a b c⦄, a ∈ C → b ∈ C → c ∈ C → a / b * c ∈ C)
    (hD : ∀ ⦃a b c⦄, a ∈ D → b ∈ D → c ∈ D → a / b * c ∈ D)
    (him : (fun χ : H →* ℂˣ => χ.comp (Subgroup.inclusion i)) '' C =
      (fun χ : H →* ℂˣ => χ.comp (Subgroup.inclusion i)) '' D)
    (I : Set G) (hI : ∀ χ ∈ C ∪ D, I ⊆ characterSelfIntertwining (χ / θ))
    (hkernel : ∀ η : H →* ℂˣ, η.comp (Subgroup.inclusion i) = 1 →
      I ⊆ characterSelfIntertwining η → θ * η ∈ C ∩ D) : C = D := by
  have lift (C' D' : Set (H →* ℂˣ)) (hθD' : θ ∈ D')
      (hD' : ∀ ⦃a b c⦄, a ∈ D' → b ∈ D' → c ∈ D' → a / b * c ∈ D')
      (hC' : C' ⊆ C ∪ D) (hD'u : D' ⊆ C ∪ D)
      (hkerD' : C ∩ D ⊆ D')
      (himage : (fun χ : H →* ℂˣ => χ.comp (Subgroup.inclusion i)) '' C' ⊆
        (fun χ : H →* ℂˣ => χ.comp (Subgroup.inclusion i)) '' D') : C' ⊆ D' := by
    intro χ hχ
    obtain ⟨φ, hφ, heq⟩ := himage ⟨χ, hχ, rfl⟩
    have htriv : (χ / φ).comp (Subgroup.inclusion i) = 1 := by
      apply MonoidHom.ext
      intro g
      have h := DFunLike.congr_fun heq g
      change φ (Subgroup.inclusion i g) = χ (Subgroup.inclusion i g) at h
      simp only [MonoidHom.comp_apply, MonoidHom.div_apply, ← h, div_self', MonoidHom.one_apply]
    have hintertwining : I ⊆ characterSelfIntertwining (χ / φ) := by
      intro a ha
      rw [← div_div_div_cancel_right χ φ θ]
      exact mem_characterSelfIntertwining_div (hI χ (hC' hχ) ha) (hI φ (hD'u hφ) ha)
    have hz := hD' (hkerD' (hkernel (χ / φ) htriv hintertwining)) hθD' hφ
    rw [mul_div_cancel_left θ (χ / φ), div_mul_cancel χ φ] at hz
    exact hz
  exact le_antisymm
    (lift C D hθD hD Set.subset_union_left Set.subset_union_right Set.inter_subset_right him.le)
    (lift D C hθC hC Set.subset_union_right Set.subset_union_left Set.inter_subset_left him.ge)

end Characters

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "G" => (Module.End F V)ˣ
local notation "Hc(" S "," q "," m ")" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q) (m + 1)
local notation "Cc(" ψ "," S "," q "," m ")" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q) m

/-- The adjacent-depth intertwining test used for the kernel of restriction in (3.5.8).
A common character determines a set of intertwining elements. These intertwine all ratios
with that common character, and detect admissible twists in the kernel of restriction. -/
def SimpleCharacterCoherenceFibreStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S T : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice),
      S.r = 0 → T.r = 0 → S.IsSimple → T.IsSimple → T.chain.order = S.chain.order → T.n = S.n →
      ∀ (m : ℕ), (m : ℤ) < S.n / 2 → ∀ h : Hc(S, q, m) = Hc(T, q', m),
        Hc(S, q, (m + 1)) = Hc(T, q', (m + 1)) →
        let C := transportCharacterSet h (Cc(ψF, S, q, m))
        let D := Cc(ψF, T, q', m)
        ∀ θ ∈ C ∩ D, ∃ I : Set (Module.End F V)ˣ,
          (∀ χ ∈ C ∪ D, I ⊆ characterSelfIntertwining (χ / θ)) ∧
          ∀ η, simpleCharacterRestriction T q' (Nat.le_succ m) η = 1 →
            I ⊆ characterSelfIntertwining η → θ * η ∈ C ∩ D

/-- Exact group carriers, adjacent restriction surjectivity and the intertwining test
for the kernel of restriction imply coherence. -/
def SimpleCharacterCoherenceReductionStatement : Prop :=
  SimpleStratumGroupPropertiesStatement.{uF, uV} → SimpleCharacterRestrictionStatement.{uF, uV} →
    SimpleCharacterCoherenceFibreStatement.{uF, uV} → SimpleCharacterCoherenceStatement.{uF, uV}

private theorem simpleHGroup_inf_unitFiltration (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (hr : S.r = 0) (hS : S.IsSimple)
    {k l : ℕ} (hkl : k ≤ l) :
    simpleHGroup S.chain S.n S.b q.tail k ⊓ S.chain.unitFiltration l =
      simpleHGroup S.chain S.n S.b q.tail l := by
  have h := (hgroups F V S hr hS q).1
  ext g
  simp only [Subgroup.mem_inf]
  change (g ∈ (simpleHGroup S.chain S.n S.b q.tail k : Set G) ∧ _) ↔
    g ∈ (simpleHGroup S.chain S.n S.b q.tail l : Set G)
  rw [(h k).1, (h l).1]
  change ((_ ∧ (g : Module.End F V) ∈ simpleHLattice S.chain S.n S.b q.tail) ∧ _) ↔ _ ∧ _
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨S.chain.unitFiltration_antitone hkl h.1, h.2⟩, h.1⟩⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem div_mul_mem_transportCharacterSet (ψF : AddChar F ℂ) {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) (m : ℕ) {H : Subgroup G} (h : Hc(S, q, m) = H) :
    ∀ ⦃a b c⦄, a ∈ transportCharacterSet h (Cc(ψF, S, q, m)) →
      b ∈ transportCharacterSet h (Cc(ψF, S, q, m)) → c ∈ transportCharacterSet h (Cc(ψF, S, q, m)) →
      a / b * c ∈ transportCharacterSet h (Cc(ψF, S, q, m)) := by
  cases h
  exact fun _ _ _ => simpleCharacters_div_mul_mem ψF S.chain S.n S.b q.tail m

private theorem simpleCharacterCoherence_atDepthZero
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (hfibre : SimpleCharacterCoherenceFibreStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S T : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice)
    (hr : S.r = 0) (hr' : T.r = 0) (hS : S.IsSimple) (hT : T.IsSimple)
    (horder : T.chain.order = S.chain.order) (hn : T.n = S.n) :
    ∀ m (h : Hc(S, q, m) = Hc(T, q', m)),
      (transportCharacterSet h (Cc(ψF, S, q, m)) ∩ Cc(ψF, T, q', m)).Nonempty →
      transportCharacterSet h (Cc(ψF, S, q, m)) = Cc(ψF, T, q', m) := by
  suffices ∀ (d m : ℕ), (S.n / 2 - (m : ℤ)).toNat = d →
      ∀ (h : Hc(S, q, m) = Hc(T, q', m)),
      (transportCharacterSet h (Cc(ψF, S, q, m)) ∩ Cc(ψF, T, q', m)).Nonempty →
      transportCharacterSet h (Cc(ψF, S, q, m)) = Cc(ψF, T, q', m) by
    intro m h hcommon
    exact this _ m rfl h hcommon
  intro d
  induction d with
  | zero =>
    intro m hd h hcommon
    exact simpleCharacterCoherence_of_half_le ψF hψ q q' m hn (by omega) h hcommon
  | succ d ih =>
    intro m hd h hcommon
    have hlow : (m : ℤ) < S.n / 2 := by omega
    have hm : (m : ℤ) + 1 < S.n := by omega
    have hm' : (m : ℤ) + 1 < T.n := hn.symm ▸ hm
    let r := simpleCharacterRestriction S q (Nat.le_succ m)
    let r' := simpleCharacterRestriction T q' (Nat.le_succ m)
    have hrim : r '' (Cc(ψF, S, q, m)) = Cc(ψF, S, q, (m + 1)) :=
      (hrestriction F V ψF hψ S hr hS q).2.2.2.1 m hm
    have hrim' : r' '' (Cc(ψF, T, q', m)) = Cc(ψF, T, q', (m + 1)) :=
      (hrestriction F V ψF hψ T hr' hT q').2.2.2.1 m hm'
    have hnext : Hc(S, q, (m + 1)) = Hc(T, q', (m + 1)) := by
      rw [← simpleHGroup_inf_unitFiltration hgroups q hr hS (k := m + 1) (by omega),
        ← simpleHGroup_inf_unitFiltration hgroups q' hr' hT (k := m + 1) (by omega)]
      rw [h, LatticeChain.unitFiltration_eq_of_order_eq horder]
    have himage : transportCharacterSet hnext (Cc(ψF, S, q, (m + 1))) =
        r' '' transportCharacterSet h (Cc(ψF, S, q, m)) := by
      rw [← hrim]
      exact transportCharacterSet_restriction_image h hnext _ _ _
    obtain ⟨θ, hθ, hθ'⟩ := hcommon
    have hnext_common :
        (transportCharacterSet hnext (Cc(ψF, S, q, (m + 1))) ∩ Cc(ψF, T, q', (m + 1))).Nonempty :=
      ⟨r' θ, himage.symm ▸ ⟨θ, hθ, rfl⟩, hrim' ▸ ⟨θ, hθ', rfl⟩⟩
    have heq := ih (m + 1) (by omega) hnext hnext_common
    have heqim : r' '' transportCharacterSet h (Cc(ψF, S, q, m)) = r' '' (Cc(ψF, T, q', m)) :=
      himage.symm.trans (heq.trans hrim'.symm)
    obtain ⟨I, hI, hkernel⟩ := hfibre F V ψF hψ S T q q' hr hr' hS hT horder hn m hlow h hnext
      θ ⟨hθ, hθ'⟩
    exact characterSets_eq_of_restriction_image_eq _ _ _ hθ hθ'
      (div_mul_mem_transportCharacterSet ψF q m h)
      (fun _ _ _ => simpleCharacters_div_mul_mem ψF T.chain T.n T.b q'.tail m) heqim I hI hkernel

/-- The descending argument applies to all inputs of the published coherence statement. -/
theorem simpleCharacterCoherenceReduction : SimpleCharacterCoherenceReductionStatement.{uF, uV} := by
  intro hgroups hrestriction hfibre F _ _ _ _ V _ _ ψF hψ S T m horder hn hr hr' hS hT q q'
  have hr₀ : 0 ≤ S.r := by omega
  have hr₀' : 0 ≤ T.r := by omega
  exact simpleCharacterCoherence_atDepthZero hgroups hrestriction hfibre ψF hψ
    (q.atDepthZero hr₀) (q'.atDepthZero hr₀') rfl rfl
    (Stratum.isSimple_atDepthZero hS hr₀) (Stratum.isSimple_atDepthZero hT hr₀') horder hn m

end Langlands.BushnellKutzko
