import Langlands.BushnellKutzko.SimpleCharacterLabelBoundStatement
import Langlands.BushnellKutzko.SimpleCharacterClassCoverStatement
import Langlands.BushnellKutzko.SimpleStratumLabelStatement
import Langlands.BushnellKutzko.SimpleCharacterConjugationStatement
import Langlands.BushnellKutzko.SimpleCharacterInvariantsStatement

/-! # The label bound for simple characters from its inputs (BK94 (2.5), printed p. 120)

`SimpleCharacterLabelBoundStatement` follows from four Library statements: the cover of
the simple-character classes by simple strata (BK94 (2.3)), the labels of simple strata in a
principal order (BK94 (1.14)), transport of simple characters by conjugation, and the
equality of field invariants for a common simple character (BK93 (3.5.1)). See the paired
Markdown file.
-/

noncomputable section

open ValuativeRel
open Langlands.Group.RelativeWeyl

namespace Langlands.BushnellKutzko

universe uF uV uG

/-- **Reduction of BK94 (2.5).** The cover of the simple-character classes by simple strata,
the simple-stratum labels, transport by conjugation and the comparison of field invariants
together imply the label bound for simple characters in a principal order. -/
def SimpleCharacterLabelBoundReductionStatement : Prop :=
  SimpleCharacterClassCoverStatement.{uF, uV} →
  SimpleStratumLabelStatement.{uF, uV} →
  SimpleCharacterConjugationStatement.{uF, uV} →
  SimpleCharacterInvariantsStatement.{uF, uV} →
  SimpleCharacterLabelBoundStatement.{uF, uV}

section CharacterPairConj

variable {G : Type uG} [Group G]

/-- Two subgroup–character pairs agree when their subgroups agree and their characters
agree pointwise. -/
private theorem characterPair_ext {P Q : CharacterPair G} (h₁ : P.1 = Q.1)
    (h₂ : ∀ (a : G) (ha : a ∈ P.1), P.2 ⟨a, ha⟩ = Q.2 ⟨a, h₁ ▸ ha⟩) : P = Q := by
  obtain ⟨H, θ⟩ := P
  obtain ⟨K, χ⟩ := Q
  dsimp only at h₁
  subst h₁
  have hθ : θ = χ := MonoidHom.ext fun ⟨a, ha⟩ => h₂ a ha
  rw [hθ]

/-- The inverse of `j ↦ g j g⁻¹` is `y ↦ g⁻¹ y g`. -/
private theorem coe_conjSubgroupEquiv_symm (g : G) (J : Subgroup G)
    (y : conjugateSubgroup g J) :
    (((conjSubgroupEquiv g J).symm y : J) : G) = g⁻¹ * y * g := by
  set j := (conjSubgroupEquiv g J).symm y
  have h : (y : G) = g * j * g⁻¹ := by
    rw [← coe_conjSubgroupEquiv, MulEquiv.apply_symm_apply]
  rw [h]
  group

/-- `(θ^y)^x = θ^{yx}` in the convention `θˣ(h) = θ(x h x⁻¹)`. -/
private theorem characterPair_conj_conj (x y : G) (P : CharacterPair G) :
    (P.conj y).conj x = P.conj (y * x) := by
  refine characterPair_ext ?_ ?_
  · change conjugateSubgroup x⁻¹ (conjugateSubgroup y⁻¹ P.1) = conjugateSubgroup (y * x)⁻¹ P.1
    rw [mul_inv_rev, conjugateSubgroup_mul]
  · intro a ha
    change P.2 _ = P.2 _
    congr 1
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom]
    erw [coe_conjSubgroupEquiv_symm, coe_conjSubgroupEquiv_symm, coe_conjSubgroupEquiv_symm]
    group

/-- Conjugation by `1` is the identity on pairs. -/
private theorem characterPair_conj_one (P : CharacterPair G) : P.conj 1 = P := by
  refine characterPair_ext ?_ ?_
  · change conjugateSubgroup 1⁻¹ P.1 = P.1
    rw [inv_one, conjugateSubgroup_one]
  · intro a ha
    change P.2 _ = P.2 _
    congr 1
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom]
    erw [coe_conjSubgroupEquiv_symm]
    group

/-- `U`-conjugacy of pairs is symmetric. -/
private theorem areConjugateBy_symm {U : Subgroup G} {P Q : CharacterPair G}
    (h : CharacterPair.AreConjugateBy U P Q) : CharacterPair.AreConjugateBy U Q P := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨x⁻¹, ?_⟩
  rw [characterPair_conj_conj, Subgroup.coe_inv, mul_inv_cancel, characterPair_conj_one]

/-- `U`-conjugacy of pairs is transitive. -/
private theorem areConjugateBy_trans {U : Subgroup G} {P Q R : CharacterPair G}
    (h₁ : CharacterPair.AreConjugateBy U P Q) (h₂ : CharacterPair.AreConjugateBy U Q R) :
    CharacterPair.AreConjugateBy U P R := by
  obtain ⟨x, rfl⟩ := h₁
  obtain ⟨y, rfl⟩ := h₂
  exact ⟨x * y, by rw [characterPair_conj_conj, Subgroup.coe_mul]⟩

end CharacterPairConj

section Chain

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Lattice chains with the same lattices are equal. -/
private theorem latticeChain_ext {L L' : LatticeChain 𝒪[F] F V} (h : L.lattice = L'.lattice) :
    L = L' := by
  cases L
  cases L'
  cases h
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A unit of `𝔄(𝓛)` maps every lattice of `𝓛` onto itself, so transporting `𝓛` along it
returns `𝓛`. -/
private theorem linearEquivMap_eq_self_of_mem_unitFiltration (L : LatticeChain 𝒪[F] F V)
    {g : (Module.End F V)ˣ} (hg : g ∈ L.unitFiltration 0) :
    L.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g) = L := by
  obtain ⟨hg₁, hg₂⟩ := (L.mem_unitFiltration_zero).1 hg
  have hlat : (L.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g)).lattice =
      L.lattice := by
    funext i
    ext v
    rw [LatticeChain.mem_linearEquivMap]
    constructor
    · intro hv
      have h := (L.mem_order.1 hg₁) i _ hv
      rwa [show (g : Module.End F V)
          ((LinearMap.GeneralLinearGroup.toLinearEquiv g).symm v) = v from
        (LinearMap.GeneralLinearGroup.toLinearEquiv g).apply_symm_apply v] at h
    · intro hv
      exact (L.mem_order.1 hg₂) i v hv
  exact latticeChain_ext hlat

end Chain

/-- The reduction of BK94 (2.5) holds: the label bound for simple characters follows from
the class cover, the stratum labels, transport by conjugation and the comparison of field
invariants. -/
theorem simpleCharacterLabelBoundReduction :
    SimpleCharacterLabelBoundReductionStatement.{uF, uV} := by
  intro hCover hLabel hConj hInv F _ _ _ _ V _ _ _ ψF hψ hN L hL n m hmn
  obtain ⟨Φ, hΦmem, hΦconj, hΦcover⟩ := hCover F V ψF hψ L n m hmn
  obtain ⟨ρ, hρconj, hρinv⟩ := hLabel F V L (m : ℤ) n hN hL (Int.natCast_nonneg m) hmn
  intro S P
  -- For each pair choose a simple stratum whose assigned pair is conjugate to it.
  have hst : ∀ Q : S, ∃ T : SimpleStratumAt L n m,
      CharacterPair.AreConjugateBy (L.unitFiltration 0) (Φ T) Q.1 :=
    fun Q => hΦcover Q.1 Q.2
  choose st hst using hst
  have hP : ∀ p, p ∈ labelSet ((m : ℤ).toNat) n.toNat L.period
      (Module.finrank F V / L.period) (Nat.card 𝓀[F]) → p ∈ P := by
    intro p hp
    rwa [Int.toNat_natCast] at hp
  have hmem : ∀ T : SimpleStratumAt L n m, (ρ T).1 ∈ P := fun T => hP _ (ρ T).2
  refine ⟨fun Q => ⟨(ρ (st Q)).1, hmem (st Q)⟩, ?_, ?_⟩
  · -- Equal labels: the chosen strata are conjugate, hence so are the assigned pairs.
    intro Q₁ Q₂ h
    have h' : ρ (st Q₁) = ρ (st Q₂) := Subtype.ext (congrArg Subtype.val h)
    obtain ⟨u, hu, hcoset⟩ := hρconj _ _ h'
    have hsub : (st Q₂).1.b - (((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * (st Q₁).1.b *
        (u : Module.End F V)) ∈ L.endFiltration (-(m : ℤ)) := by
      have h₂ := neg_mem (show _ ∈ (st Q₂).1.chain.endFiltration (-(st Q₂).1.r) from hcoset)
      rw [neg_sub, (st Q₂).2.1, (st Q₂).2.2.2.1] at h₂
      exact h₂
    exact areConjugateBy_trans
      (areConjugateBy_trans (areConjugateBy_symm (hst Q₁)) (hΦconj (st Q₁) (st Q₂) ⟨u, hu⟩ hsub))
      (hst Q₂)
  · -- Invariants: transport the chosen stratum to one whose character set contains `Q`.
    intro T Q hQT
    obtain ⟨x, hx⟩ := hst Q
    set R := st Q
    obtain ⟨-, -, -, -, T', hT'chain, hT'n, hT'r, -, hT'simple, -, hT'pairs, hT'e, hT'f⟩ :=
      hConj F V ψF hψ R.1 m R.2.2.2.1 R.2.2.2.2 ((x : (Module.End F V)ˣ)⁻¹)
    have hchain : T'.chain = L := by
      rw [hT'chain, R.2.1]
      exact linearEquivMap_eq_self_of_mem_unitFiltration L (inv_mem x.2)
    let T'' : SimpleStratumAt L n m :=
      ⟨T', hchain, hT'n.trans R.2.2.1, hT'r.trans R.2.2.2.1, hT'simple⟩
    have hQT' : Q.1 ∈ simpleCharacterPairs ψF T''.1 m := by
      change Q.1 ∈ simpleCharacterPairs ψF T' m
      rw [hT'pairs]
      exact ⟨Φ R, hΦmem R, by rw [inv_inv]; exact hx⟩
    obtain ⟨-, hIe, hIf⟩ := hInv F V ψF hψ L n m T'' T ⟨Q.1, hQT', hQT⟩
    refine ⟨?_, ?_⟩
    · change (ρ R).1.d = _
      rw [(hρinv R).1, ← hT'f]
      exact hIf
    · change _ * (ρ R).1.e = _
      rw [← hIe]
      change elementRamificationIndex F T'.b * _ = _
      rw [hT'e]
      exact (hρinv R).2

end Langlands.BushnellKutzko
