import Langlands.BushnellKutzko.IntertwiningTransport
import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.SimpleCharacterConjugationProof

/-! # Transport of representations of subgroups by conjugation

For a group `G`, an element `g` and subgroups `K`, `K'` with `K' = gKg⁻¹`,
`conjEquivOfEq g h : K ≃* K'` is `k ↦ gkg⁻¹`. A representation `ρ` of `K` gives the
representation `ρ ∘ (conjEquivOfEq g h)⁻¹` of `K'`, which is `ρ^{g⁻¹}` on the subgroup
`K'`. For `G = Aut_F(V)` this transports smoothness, Heisenberg representations
(BK93 (5.1.1)), `β`-extensions (BK93 (5.2.1)) and isomorphism of pairs.
-/

noncomputable section

open ValuativeRel
open Langlands.Group.RelativeWeyl

namespace Langlands.BushnellKutzko

universe uG uW uW' uF uV

section Group

variable {G : Type uG} [Group G]

/-- For `K' = gKg⁻¹`, the isomorphism `K ≃* K'`, `k ↦ gkg⁻¹`. -/
def conjEquivOfEq (g : G) {K K' : Subgroup G} (h : K' = conjugateSubgroup g K) : K ≃* K' :=
  (conjSubgroupEquiv g K).trans (MulEquiv.subgroupCongr h.symm)

@[simp] theorem coe_conjEquivOfEq (g : G) {K K' : Subgroup G} (h : K' = conjugateSubgroup g K)
    (k : K) : (conjEquivOfEq g h k : G) = g * k * g⁻¹ :=
  rfl

theorem coe_conjEquivOfEq_symm (g : G) {K K' : Subgroup G} (h : K' = conjugateSubgroup g K)
    (k : K') : ((conjEquivOfEq g h).symm k : G) = g⁻¹ * k * g := by
  have hk := congrArg Subtype.val ((conjEquivOfEq g h).apply_symm_apply k)
  rw [coe_conjEquivOfEq] at hk
  rw [← hk]
  group

theorem mem_conjugateSubgroup_iff (g : G) (K : Subgroup G) (x : G) :
    x ∈ conjugateSubgroup g K ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    change g⁻¹ * (g * k * g⁻¹) * g ∈ K
    simpa [mul_assoc] using hk
  · intro hx
    exact ⟨_, hx, by change g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩

theorem conjSubgroupEquiv_symm_val (g : G) (K : Subgroup G) (k : conjugateSubgroup g K) :
    ((conjSubgroupEquiv g K).symm k : G) = g⁻¹ * k * g :=
  coe_conjEquivOfEq_symm g (rfl : conjugateSubgroup g K = conjugateSubgroup g K) k

theorem conjugateSubgroup_inf (g : G) (K₁ K₂ : Subgroup G) :
    conjugateSubgroup g (K₁ ⊓ K₂) = conjugateSubgroup g K₁ ⊓ conjugateSubgroup g K₂ := by
  ext x
  simp only [Subgroup.mem_inf, mem_conjugateSubgroup_iff]

/-- Conjugation is compatible with inclusions of subgroups. -/
theorem conjEquivOfEq_symm_inclusion (g : G) {K₁ K₂ K₁' K₂' : Subgroup G}
    (h₁ : K₁' = conjugateSubgroup g K₁) (h₂ : K₂' = conjugateSubgroup g K₂) (hle : K₁ ≤ K₂)
    (hle' : K₁' ≤ K₂') (k : K₁') :
    (conjEquivOfEq g h₂).symm (Subgroup.inclusion hle' k) =
      Subgroup.inclusion hle ((conjEquivOfEq g h₁).symm k) :=
  Subtype.ext (by simp only [coe_conjEquivOfEq_symm, Subgroup.coe_inclusion])

variable {W : Type uW} [AddCommGroup W] [Module ℂ W] {W' : Type uW'} [AddCommGroup W']
  [Module ℂ W']

/-- Pulling back along an isomorphism of groups preserves irreducibility. -/
theorem isIrreducible_comp_mulEquiv {H H' : Type*} [Group H] [Group H'] (ρ : Representation ℂ H W)
    (e : H' ≃* H) (hρ : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  let o : Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun x v hv => by
        obtain ⟨y, rfl⟩ := e.surjective x
        exact S.apply_mem_toSubmodule y hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun y v hv => S.apply_mem_toSubmodule (e y) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact o.isSimpleOrder_iff.2 hρ

/-- An equivalence of representations pulls back along any homomorphism. -/
def equivComp {H H' : Type*} [Monoid H] [Monoid H'] {ρ : Representation ℂ H W}
    {σ : Representation ℂ H W'} (e : ρ.Equiv σ) (φ : H' →* H) :
    Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv fun x => LinearMap.ext fun v => by
    have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (φ x) v
    simpa using this

/-- An equivalence of representations gives an equivalence of representations which are
pointwise its pullbacks along a homomorphism. -/
def equivOfPullback {H H' : Type*} [Monoid H] [Monoid H'] {ρ : Representation ℂ H W}
    {σ : Representation ℂ H W'} (e : ρ.Equiv σ) (ε : H' →* H) {ρ' : Representation ℂ H' W}
    {σ' : Representation ℂ H' W'} (hρ : ∀ x, ρ' x = ρ (ε x)) (hσ : ∀ x, σ' x = σ (ε x)) :
    ρ'.Equiv σ' :=
  Representation.Equiv.mk e.toLinearEquiv fun x => LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hρ, hσ]
    have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (ε x) v
    simpa using this

/-- An intertwining map pulls back along any homomorphism. -/
def intertwiningMapComp {H H' : Type*} [Monoid H] [Monoid H'] {ρ : Representation ℂ H W}
    {σ : Representation ℂ H W'} (f : Representation.IntertwiningMap ρ σ) (φ : H' →* H) :
    Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ) :=
  ⟨f.toLinearMap, fun x => LinearMap.ext fun v => by
    have := Representation.IntertwiningMap.isIntertwining _ _ f (φ x) v
    simpa using this⟩

/-- Conjugation of pairs: if `(J₁, ρ₁) ≅ (J₂, ρ₂)`, then
`(gJ₁g⁻¹, ρ₁^{g⁻¹}) ≅ (J₂', ρ₂ ∘ (k ↦ g⁻¹kg))` for `J₂' = gJ₂g⁻¹`. -/
theorem IsPairIsomorphic.conj (g : G) {J₁ J₂ J₂' : Subgroup G}
    (h' : J₂' = conjugateSubgroup g J₂) {ρ₁ : Representation ℂ J₁ W}
    {ρ₂ : Representation ℂ J₂ W'} (h : IsPairIsomorphic ρ₁ ρ₂) :
    IsPairIsomorphic (conjRepresentation g ρ₁) (ρ₂.comp (conjEquivOfEq g h').symm.toMonoidHom) := by
  obtain ⟨hJ, ⟨e⟩⟩ := h
  subst hJ
  subst h'
  refine ⟨rfl, ⟨?_⟩⟩
  have hρ : (conjRepresentation g ρ₁).comp
      (MulEquiv.subgroupCongr (rfl : conjugateSubgroup g J₁ = conjugateSubgroup g J₁)).symm.toMonoidHom =
      (ρ₁.comp (MulEquiv.subgroupCongr (rfl : J₁ = J₁)).symm.toMonoidHom).comp
        (conjEquivOfEq g rfl).symm.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [hρ]
  exact equivComp e _

end Group

section Local

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {W' : Type uW'} [AddCommGroup W']
  [Module ℂ W']

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- Conjugation transports smooth representations. -/
theorem IsSmoothRepresentation.conj (g : G) {K K' : Subgroup G}
    (h : K' = conjugateSubgroup g K) {ρ : Representation ℂ K W} (hρ : IsSmoothRepresentation ρ) :
    IsSmoothRepresentation (ρ.comp (conjEquivOfEq g h).symm.toMonoidHom) := by
  obtain ⟨L, m, hL⟩ := hρ
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv g
  have hc : L.Corresponds f (L.linearEquivMap f) := L.corresponds_linearEquivMap f
  refine ⟨L.linearEquivMap f, m, fun k hk => ?_⟩
  apply hL
  rw [← hc.mem_unitFiltration, unitsConj_toLinearEquiv, MulEquiv.coe_toMonoidHom,
    coe_conjEquivOfEq_symm]
  convert hk using 1
  group

/-- `U^m(g𝔄g⁻¹) = g U^m(𝔄) g⁻¹`. -/
theorem unitFiltration_linearEquivMap (g : G) (L : LatticeChain 𝒪[F] F V) (m : ℕ) :
    (L.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g)).unitFiltration m =
      conjugateSubgroup g (L.unitFiltration m) := by
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv g
  have hc : L.Corresponds f (L.linearEquivMap f) := L.corresponds_linearEquivMap f
  ext y
  rw [mem_conjugateSubgroup_iff, ← hc.mem_unitFiltration, unitsConj_toLinearEquiv,
    show g * (g⁻¹ * y * g) * g⁻¹ = y by group]

omit [ValuativeRel F] in
/-- `B_{gβg⁻¹}^× = g B_β^× g⁻¹`. -/
theorem centralizerUnitGroup_endConj (g : G) (β : A) :
    centralizerUnitGroup (endConj (LinearMap.GeneralLinearGroup.toLinearEquiv g) β) =
      conjugateSubgroup g (centralizerUnitGroup β) := by
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv g
  ext y
  rw [mem_conjugateSubgroup_iff]
  have hy : (y : A) = endConj f ((g⁻¹ * y * g : G) : A) := by
    rw [← coe_unitsConj, unitsConj_toLinearEquiv]
    congr 1
    group
  change endConj f β * (y : A) = (y : A) * endConj f β ↔ β * ((g⁻¹ * y * g : G) : A) =
    ((g⁻¹ * y * g : G) : A) * β
  rw [hy, ← map_mul, ← map_mul]
  exact (endConj f).injective.eq_iff

/-- `U^m(𝔅_{gβg⁻¹})` computed in `g𝔄g⁻¹` is `g U^m(𝔅_β) g⁻¹`. -/
theorem relativeUnitFiltration_linearEquivMap (g : G) (L : LatticeChain 𝒪[F] F V) (β : A)
    (m : ℕ) :
    relativeUnitFiltration (L.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g))
        (endConj (LinearMap.GeneralLinearGroup.toLinearEquiv g) β) m =
      conjugateSubgroup g (relativeUnitFiltration L β m) := by
  rw [relativeUnitFiltration, relativeUnitFiltration, conjugateSubgroup_inf,
    centralizerUnitGroup_endConj, unitFiltration_linearEquivMap]

/-- Conjugation transports Heisenberg representations (BK93 (5.1.1)). -/
theorem IsHeisenbergRepresentation.conj (g : G) {L L' : LatticeChain 𝒪[F] F V} {n n' : ℤ}
    {β β' : A} {tail tail' : List A}
    (hH : simpleHGroup L' n' β' tail' 1 = conjugateSubgroup g (simpleHGroup L n β tail 1))
    (hJ : simpleJGroup L' n' β' tail' 1 = conjugateSubgroup g (simpleJGroup L n β tail 1))
    {θ : simpleHGroup L n β tail 1 →* ℂˣ} {η : Representation ℂ (simpleJGroup L n β tail 1) W}
    (hη : IsHeisenbergRepresentation L n β tail θ η) :
    IsHeisenbergRepresentation L' n' β' tail' (θ.comp (conjEquivOfEq g hH).symm.toMonoidHom)
      (η.comp (conjEquivOfEq g hJ).symm.toMonoidHom) := by
  obtain ⟨hfin, hsm, hirr, f, hf⟩ := hη
  refine ⟨hfin, hsm.conj g hJ, isIrreducible_comp_mulEquiv η _ hirr, ?_⟩
  have h1 : characterRepresentation (θ.comp (conjEquivOfEq g hH).symm.toMonoidHom) =
      (characterRepresentation θ).comp (conjEquivOfEq g hH).symm.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  have h2 : (η.comp (conjEquivOfEq g hJ).symm.toMonoidHom).comp
      (Subgroup.inclusion (simpleHGroup_le_simpleJGroup L' n' β' tail' 1)) =
      (η.comp (Subgroup.inclusion (simpleHGroup_le_simpleJGroup L n β tail 1))).comp
        (conjEquivOfEq g hH).symm.toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [conjEquivOfEq_symm_inclusion g hH hJ]
  rw [h1, h2]
  refine ⟨intertwiningMapComp f _, fun h0 => hf ?_⟩
  apply Representation.IntertwiningMap.ext
  have h3 := congrArg Representation.IntertwiningMap.toLinearMap h0
  exact h3

/-- Conjugation transports `β`-extensions (BK93 (5.2.1)). -/
theorem IsBetaExtension.conj (g : G) {L L' : LatticeChain 𝒪[F] F V} {n n' : ℤ}
    {β : A} {tail tail' : List A}
    (hJ1 : simpleJGroup L' n' (endConj (LinearMap.GeneralLinearGroup.toLinearEquiv g) β) tail' 1 =
      conjugateSubgroup g (simpleJGroup L n β tail 1))
    (hJ0 : simpleJ L' n' (endConj (LinearMap.GeneralLinearGroup.toLinearEquiv g) β) tail' =
      conjugateSubgroup g (simpleJ L n β tail))
    {η : Representation ℂ (simpleJGroup L n β tail 1) W}
    {κ : Representation ℂ (simpleJ L n β tail) W'} (hκ : IsBetaExtension L n β tail η κ) :
    IsBetaExtension L' n' (endConj (LinearMap.GeneralLinearGroup.toLinearEquiv g) β) tail'
      (η.comp (conjEquivOfEq g hJ1).symm.toMonoidHom)
      (κ.comp (conjEquivOfEq g hJ0).symm.toMonoidHom) := by
  obtain ⟨hfin, hsm, ⟨e⟩, hint⟩ := hκ
  refine ⟨hfin, hsm.conj g hJ0, ⟨?_⟩, fun y hy => ?_⟩
  · have h2 : (κ.comp (conjEquivOfEq g hJ0).symm.toMonoidHom).comp
        (Subgroup.inclusion (simpleJGroup_one_le_simpleJ L' n'
          (endConj (LinearMap.GeneralLinearGroup.toLinearEquiv g) β) tail')) =
        (κ.comp (Subgroup.inclusion (simpleJGroup_one_le_simpleJ L n β tail))).comp
          (conjEquivOfEq g hJ1).symm.toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [conjEquivOfEq_symm_inclusion g hJ1 hJ0]
    rw [h2]
    exact equivComp e _
  · rw [centralizerUnitGroup_endConj, mem_conjugateSubgroup_iff] at hy
    have hy0 := hint _ hy
    let κ' := κ.comp (conjEquivOfEq g hJ0).symm.toMonoidHom
    have hκ' : κ'.comp (conjEquivOfEq g hJ0).toMonoidHom = κ := by
      refine MonoidHom.ext fun x => ?_
      simp [κ']
    have key := selfIntertwines_comp_mulEquiv_iff (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective (conjEquivOfEq g hJ0) (fun j => rfl) κ' (g⁻¹ * y * g)
    rw [hκ'] at key
    have hgy : (MulAut.conj g).toMonoidHom (g⁻¹ * y * g) = y := by
      change g * (g⁻¹ * y * g) * g⁻¹ = y
      group
    rw [hgy] at key
    exact key.1 hy0

end Local

end Langlands.BushnellKutzko
