import Langlands.BushnellKutzko.SimpleCharacterConjugationStatement
import Langlands.BushnellKutzko.SimpleCharacterTransport
import Langlands.BushnellKutzko.ElementFieldInvariantTransport
import Langlands.BushnellKutzko.SimpleCharacterSequence
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof
import Langlands.BushnellKutzko.FundamentalStratumPowerCondition

/-! # Transport of simple characters by conjugation -/

noncomputable section

open ValuativeRel
open Langlands.Group.RelativeWeyl

namespace Langlands.BushnellKutzko

universe uF uV

section Pairs

variable {G : Type*} [Group G]

/-- Two subgroup–character pairs with equal subgroups and equal values are equal. -/
theorem characterPair_eq_of_eq {K K' : Subgroup G} (h : K = K') (θ : K →* ℂˣ) (θ' : K' →* ℂˣ)
    (hv : ∀ (x : G) (hx : x ∈ K) (hx' : x ∈ K'), θ ⟨x, hx⟩ = θ' ⟨x, hx'⟩) :
    (⟨K, θ⟩ : CharacterPair G) = ⟨K', θ'⟩ := by
  subst h
  congr
  ext x
  exact congrArg Units.val (hv x x.2 x.2)

/-- A pair corresponding to `(H, θ)` under conjugation by `g` is `CharacterPair.conj g⁻¹`
of it. -/
theorem characterPair_eq_conj (φ : G ≃* G) (g : G) (hφ : ∀ x, φ x = g * x * g⁻¹)
    {H H' : Subgroup G} (hH : H' = H.map φ.toMonoidHom) {θ : H →* ℂˣ} {θ' : H' →* ℂˣ}
    (hθ : CharacterCorresponds φ θ θ') :
    (⟨H', θ'⟩ : CharacterPair G) = CharacterPair.conj g⁻¹ ⟨H, θ⟩ := by
  have hH' : H' = conjugateSubgroup g⁻¹⁻¹ H := by
    rw [hH, inv_inv]
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, hφ]
    rfl
  refine characterPair_eq_of_eq hH' θ' _ fun x hx hx' => ?_
  change θ' ⟨x, hx⟩ = θ ((conjSubgroupEquiv g⁻¹⁻¹ H).symm ⟨x, hx'⟩)
  set y := (conjSubgroupEquiv g⁻¹⁻¹ H).symm ⟨x, hx'⟩ with hy
  have hxy : x = φ y := by
    have h := congrArg Subtype.val ((conjSubgroupEquiv g⁻¹⁻¹ H).apply_symm_apply ⟨x, hx'⟩)
    rw [← hy, coe_conjSubgroupEquiv] at h
    have h2 : g⁻¹⁻¹ * (y : G) * g⁻¹⁻¹⁻¹ = x := h
    simp only [inv_inv] at h2
    rw [hφ, h2]
  have hyx : φ y ∈ H' := hxy ▸ hx
  rw [← hθ y y.2 hyx]
  congr 1
  exact Subtype.ext hxy

end Pairs

section Linear

variable {O F V : Type*} [CommRing O] [Field F] [Algebra O F] [AddCommGroup V] [Module F V]
  [Module O V] [IsScalarTower O F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

theorem LatticeChain.Corresponds.simpleHGroup_eq_of_eq {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) {β β' : A} {tail tail' : List A}
    (hβ : β' = endConj f β) (htail : tail' = tail.map (endConj f)) (m : ℕ) :
    simpleHGroup L' n β' tail' m = (simpleHGroup L n β tail m).map (unitsConj f).toMonoidHom := by
  subst hβ htail
  exact hL.simpleHGroup_eq n β tail m

theorem LatticeChain.Corresponds.simpleJGroup_eq_of_eq {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) {β β' : A} {tail tail' : List A}
    (hβ : β' = endConj f β) (htail : tail' = tail.map (endConj f)) (m : ℕ) :
    simpleJGroup L' n β' tail' m = (simpleJGroup L n β tail m).map (unitsConj f).toMonoidHom := by
  subst hβ htail
  exact hL.simpleJGroup_eq n β tail m

theorem LatticeChain.Corresponds.mem_simpleCharacters_of_eq (ψF : AddChar F ℂ)
    {f : V ≃ₗ[F] V} {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) {β β' : A}
    {tail tail' : List A} (hβ : β' = endConj f β) (htail : tail' = tail.map (endConj f)) (m : ℕ)
    (θ : simpleHGroup L n β tail (m + 1) →* ℂˣ) (θ' : simpleHGroup L' n β' tail' (m + 1) →* ℂˣ)
    (hθ : CharacterCorresponds (unitsConj f) θ θ') :
    θ' ∈ simpleCharacters ψF L' n β' tail' m ↔ θ ∈ simpleCharacters ψF L n β tail m := by
  subst hβ htail
  exact hL.mem_simpleCharacters ψF n tail β m θ θ' hθ

theorem unitsConj_toLinearEquiv (g u : G) :
    unitsConj (LinearMap.GeneralLinearGroup.toLinearEquiv g) u = g * u * g⁻¹ :=
  Units.ext (LinearMap.ext fun _ => rfl)

theorem map_unitsConj_toLinearEquiv (g : G) (H : Subgroup G) :
    H.map (unitsConj (LinearMap.GeneralLinearGroup.toLinearEquiv g)).toMonoidHom =
      conjugateSubgroup g H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, unitsConj_toLinearEquiv]
  rfl

end Linear

section LocalField

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- The lattices `ℌ` and `𝔍` of a simple stratum at a nonnegative index do not depend on
the defining sequence (BK93, remarks following (3.1.9), pp. 91–92, for `ℌ`, and following
(3.1.10), p. 94, for `𝔍`). -/
theorem simpleLattices_eq_of_definingSequence {S : Stratum 𝒪[F] F V} (hS : S.IsSimple)
    (hr : 0 ≤ S.r) (q q' : S.DefiningSequenceChoice) :
    simpleHLattice S.chain S.n S.b q.tail = simpleHLattice S.chain S.n S.b q'.tail ∧
      simpleJLattice S.chain S.n S.b q.tail = simpleJLattice S.chain S.n S.b q'.tail := by
  have hS0 := Stratum.isSimple_atDepthZero hS hr
  have h := (simpleStratumLatticeProperties F V (S.atDepthZero (hr.trans_lt S.r_lt_n)) rfl hS0
    (q.atDepthZero hr)).1 (q'.atDepthZero hr)
  exact h

theorem simpleHGroup_eq_of_definingSequence {S : Stratum 𝒪[F] F V} (hS : S.IsSimple)
    (hr : 0 ≤ S.r) (q q' : S.DefiningSequenceChoice) (k : ℕ) :
    simpleHGroup S.chain S.n S.b q.tail k = simpleHGroup S.chain S.n S.b q'.tail k := by
  unfold simpleHGroup simpleHCarrier
  rw [(simpleLattices_eq_of_definingSequence hS hr q q').1]

theorem simpleJGroup_eq_of_definingSequence {S : Stratum 𝒪[F] F V} (hS : S.IsSimple)
    (hr : 0 ≤ S.r) (q q' : S.DefiningSequenceChoice) (k : ℕ) :
    simpleJGroup S.chain S.n S.b q.tail k = simpleJGroup S.chain S.n S.b q'.tail k := by
  unfold simpleJGroup simpleJCarrier
  rw [(simpleLattices_eq_of_definingSequence hS hr q q').2]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem LatticeChain.corresponds_linearEquivMap (L : LatticeChain 𝒪[F] F V) (f : V ≃ₗ[F] V) :
    L.Corresponds f (L.linearEquivMap f) := by
  intro i v
  rw [LatticeChain.mem_linearEquivMap, LinearEquiv.symm_apply_apply]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem LatticeChain.isPrincipal_linearEquivMap (L : LatticeChain 𝒪[F] F V) (f : V ≃ₗ[F] V)
    (h : L.IsPrincipal) : (L.linearEquivMap f).IsPrincipal := by
  have hrel : ∀ i j : ℤ,
      ((L.linearEquivMap f).lattice j).toAddSubgroup.relIndex
        ((L.linearEquivMap f).lattice i).toAddSubgroup =
      (L.lattice j).toAddSubgroup.relIndex (L.lattice i).toAddSubgroup := by
    intro i j
    change ((L.lattice j).map (f.toLinearMap.restrictScalars 𝒪[F])).toAddSubgroup.relIndex
      ((L.lattice i).map (f.toLinearMap.restrictScalars 𝒪[F])).toAddSubgroup = _
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ f.injective
  intro i j
  rw [hrel, hrel]
  exact h i j

/-- **Transport of simple characters by conjugation** (BK93 §§1.1, 3.1–3.2, p. 104;
BK94 §2, p. 118). -/
theorem simpleCharacterConjugation : SimpleCharacterConjugationStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ ψF _ S m hSr hS g f L L'
  have hLL' : L.Corresponds f L' := L.corresponds_linearEquivMap f
  let T : Stratum 𝒪[F] F V := S.transport f L' hLL'
  have hST : S.Corresponds f T := S.corresponds_transport f L' hLL'
  have hT : T.IsSimple := hST.isSimple_iff.2 hS
  have hr : 0 ≤ S.r := hSr ▸ Int.natCast_nonneg m
  have hrT : 0 ≤ T.r := hr
  have hφ : ∀ u : (Module.End F V)ˣ, unitsConj f u = g * u * g⁻¹ :=
    unitsConj_toLinearEquiv g
  refine ⟨⟨L', rfl⟩, ?_, L.period_linearEquivMap f, L.isPrincipal_linearEquivMap f, T, rfl, rfl,
    rfl, rfl, hT, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      refine ⟨endConj f.symm y, ?_, endConj_endConj_symm f y⟩
      rw [SetLike.mem_coe, ← hLL'.mem_order, endConj_endConj_symm]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      exact (hLL'.mem_order x).2 hx
  · intro q q' k
    let qT := q.transport f hST
    have htail : qT.tail = q.tail.map (endConj f) := Stratum.DefiningSequenceChoice.tail_transport f hST q
    constructor
    · calc simpleHGroup L' T.n T.b q'.tail k = simpleHGroup L' T.n T.b qT.tail k :=
            simpleHGroup_eq_of_definingSequence hT hrT q' qT k
        _ = (simpleHGroup L S.n S.b q.tail k).map (unitsConj f).toMonoidHom :=
            hLL'.simpleHGroup_eq_of_eq S.n rfl htail k
        _ = conjugateSubgroup g (simpleHGroup L S.n S.b q.tail k) :=
            map_unitsConj_toLinearEquiv g _
    · calc simpleJGroup L' T.n T.b q'.tail k = simpleJGroup L' T.n T.b qT.tail k :=
            simpleJGroup_eq_of_definingSequence hT hrT q' qT k
        _ = (simpleJGroup L S.n S.b q.tail k).map (unitsConj f).toMonoidHom :=
            hLL'.simpleJGroup_eq_of_eq S.n rfl htail k
        _ = conjugateSubgroup g (simpleJGroup L S.n S.b q.tail k) :=
            map_unitsConj_toLinearEquiv g _
  · ext P
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨q', θ', hθ', rfl⟩
      let q'' := q'.transport f.symm hST.symm
      have htail : q'.tail = q''.tail.map (endConj f) := by
        rw [Stratum.DefiningSequenceChoice.tail_transport, List.map_map]
        conv_lhs => rw [← List.map_id q'.tail]
        congr 1
        funext y
        exact (endConj_endConj_symm f y).symm
      have hH := hLL'.simpleHGroup_eq_of_eq S.n (β := S.b) (β' := T.b) rfl htail (m + 1)
      obtain ⟨θ'', h''⟩ := exists_characterCorresponds_symm (unitsConj f) hH θ'
      refine ⟨⟨simpleHGroup L S.n S.b q''.tail (m + 1), θ''⟩, ⟨q'', θ'', ?_, rfl⟩, ?_⟩
      · exact (hLL'.mem_simpleCharacters_of_eq ψF S.n rfl htail m θ'' θ' h'').1 hθ'
      · exact (characterPair_eq_conj (unitsConj f) g hφ hH h'').symm
    · rintro ⟨_, ⟨q, θ, hθ, rfl⟩, rfl⟩
      let qT := q.transport f hST
      have htail : qT.tail = q.tail.map (endConj f) :=
        Stratum.DefiningSequenceChoice.tail_transport f hST q
      have hH := hLL'.simpleHGroup_eq_of_eq S.n (β := S.b) (β' := T.b) rfl htail (m + 1)
      obtain ⟨θ', h'⟩ := exists_characterCorresponds (unitsConj f) hH θ
      refine ⟨qT, θ', ?_, ?_⟩
      · exact (hLL'.mem_simpleCharacters_of_eq ψF S.n rfl htail m θ θ' h').2 hθ
      · exact characterPair_eq_conj (unitsConj f) g hφ hH h'
  · exact elementRamificationIndex_endConj f S.b
  · exact elementResidueDegree_endConj f S.b

end LocalField

end Langlands.BushnellKutzko
