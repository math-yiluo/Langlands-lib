import Langlands.BushnellKutzko.BetaExtensionTwist.HeisenbergTrace
import Langlands.BushnellKutzko.BetaExtensionTwist.IntersectionIndex
import Langlands.BushnellKutzko.HeisenbergRepresentationStatement

/-! # Multiplicity one for the intertwining of a Heisenberg representation -/

noncomputable section
open ValuativeRel
open scoped Pointwise MonoidAlgebra

namespace Langlands.BushnellKutzko

universe uG uF uV uW uW₁ uW₂

section ScalarExtensions

variable {G : Type uG} [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ W] {H J : Subgroup G} (hHJ : H ≤ J)
  [(H.subgroupOf J).Normal]

/-- On an intertwining double coset of a square-degree scalar extension, the
dimension times the scalar-subgroup index on the common domain is the degree squared. -/
theorem finrank_intertwiningSpace_mul_relIndex_of_scalar
    (θ : H →* ℂˣ) (η : Representation ℂ J W) [η.IsIrreducible]
    (hscalar : ∀ h : H, η (Subgroup.inclusion hHJ h) = (θ h : ℂ) • LinearMap.id)
    (hdim : Module.finrank ℂ W ^ 2 = H.relIndex J) (y : G) (hy : Intertwines η η y) :
    Module.finrank ℂ (intertwiningSpace η η y) *
      (intertwiningDomain H H y).relIndex (intertwiningDomain J J y) = Module.finrank ℂ W ^ 2 := by
  let K := intertwiningDomain J J y
  let l := intertwiningDomainConj J J y
  let r := intertwiningDomainIncl J J y
  let N := H.subgroupOf J
  let D := N.comap l ⊓ N.comap r
  have : Nontrivial W := IsSimpleModule.nontrivial ℂ[J] η.asModule
  have : N.FiniteIndex := by
    constructor
    change H.relIndex J ≠ 0
    rw [← hdim]
    exact pow_ne_zero 2 (Module.finrank_pos (R := ℂ) (M := W)).ne'
  have : N.Normal := inferInstanceAs ((H.subgroupOf J).Normal)
  let nH : N →* H := (J.subtype.comp N.subtype).codRestrict H fun x => x.property
  have htrace (g : J) (hg : (g : G) ∉ H) : η.character g = 0 :=
    character_eq_zero_of_scalar_index η N (θ.comp nH) (fun n => hscalar (nH n)) hdim g hg
  let ρ := η.comp l
  let σ := η.comp r
  obtain ⟨f, hf⟩ := hy
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra! hz
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext hz))
  have htriv (g : K) (hg : g ∈ D) : Representation.linHom ρ σ g = 1 := by
    let a : H := ⟨y * (g : G) * y⁻¹, hg.1⟩
    let b : H := ⟨(g : G), hg.2⟩
    have hl : l g = Subgroup.inclusion hHJ a := rfl
    have hr : r g = Subgroup.inclusion hHJ b := rfl
    have h := Representation.IntertwiningMap.isIntertwining ρ σ f g v
    change f (η (l g) v) = η (r g) (f v) at h
    rw [hl, hr, hscalar, hscalar, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.id_apply, map_smul] at h
    have hθ : θ a = θ b := Units.ext (smul_left_injective ℂ hv h)
    ext A w
    change η (r g) (A (η (l g⁻¹) w)) = A w
    rw [map_inv l, hl, hr, ← map_inv (Subgroup.inclusion hHJ), hscalar, hscalar,
      LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_apply,
      map_smul, map_inv θ, hθ, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hzero (g : K) (hg : g ∉ D) : (Representation.linHom ρ σ).character g = 0 := by
    rw [Representation.char_linHom]
    change η.character (l g⁻¹) * η.character (r g) = 0
    by_cases hrg : (r g : G) ∈ H
    · have hlg : (l g : G) ∉ H := fun h => hg ⟨h, hrg⟩
      rw [htrace _ (by simpa only [map_inv, Subgroup.coe_inv, Subgroup.inv_mem_iff] using hlg), zero_mul]
    · rw [htrace _ hrg, mul_zero]
  have h := finrank_intertwiningMap_mul_index_of_trace_support ρ σ D htriv hzero
  rw [Module.finrank_linearMap, ← pow_two] at h
  exact h

omit [FiniteDimensional ℂ W] [(H.subgroupOf J).Normal] in
private theorem relIndex_intertwiningDomain_mul_left_right
    (hnorm : J ≤ Subgroup.normalizer H) (y : G) (a b : J) :
    (intertwiningDomain H H ((a : G) * y * b)).relIndex
      (intertwiningDomain J J ((a : G) * y * b)) =
    (intertwiningDomain H H y).relIndex (intertwiningDomain J J y) := by
  let e := MulAut.conj (b : G)
  have he (T : Subgroup G) (hT : J ≤ Subgroup.normalizer T) :
      intertwiningDomain T T ((a : G) * y * b) = (intertwiningDomain T T y).comap e.toMonoidHom := by
    ext g
    change (((a : G) * y * b) * g * ((a : G) * y * b)⁻¹ ∈ T ∧ g ∈ T) ↔
      (y * ((b : G) * g * (b : G)⁻¹) * y⁻¹ ∈ T ∧ (b : G) * g * (b : G)⁻¹ ∈ T)
    have hconj : ((a : G) * y * b) * g * ((a : G) * y * b)⁻¹ =
        (a : G) * (y * ((b : G) * g * (b : G)⁻¹) * y⁻¹) * (a : G)⁻¹ := by group
    rw [hconj, ← Subgroup.mem_normalizer_iff.mp (hT a.property),
      ← Subgroup.mem_normalizer_iff.mp (hT b.property) g]
  rw [he H hnorm, he J J.le_normalizer, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective e.surjective]

end ScalarExtensions

section SimpleStrata

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- On every intertwining double coset of the Heisenberg representation the
intertwining space has dimension one, as in BK93 (5.1.8). -/
theorem heisenberg_intertwining_finrank_eq_one
    (hV₁ : HeisenbergRepresentationStatement.{uF, uV, uW, uW₁, uW₂})
    (hlattices : SimpleStratumLatticePropertiesStatement.{uF, uV})
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ)
    (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (θ : simpleHGroup S.chain S.n S.b q.tail 1 →* ℂˣ)
    (hθ : θ ∈ simpleCharacters ψ S.chain S.n S.b q.tail 0)
    (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) W)
    (hη : IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η)
    (x : (Module.End F V)ˣ) (hx : x ∈ representationSelfIntertwining η) :
    Module.finrank ℂ (intertwiningSpace η η x) = 1 := by
  let H := simpleHGroup S.chain S.n S.b q.tail 1
  let J := simpleJGroup S.chain S.n S.b q.tail 1
  let B := centralizerUnitGroup S.b
  let hHJ : H ≤ J := simpleHGroup_le_simpleJGroup S.chain S.n S.b q.tail 1
  have hnorm : J ≤ Subgroup.normalizer H := (simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail).trans
    (((hgroups F V S hr hs q).2.2.2.1 0).2.2)
  have : (H.subgroupOf J).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  obtain ⟨hscalar, hdim, hsupport⟩ := (hV₁ F V ψ hψ S hr hs q θ hθ).2.2 W η hη
  have := hη.1
  have := hη.2.2.1
  have : Nontrivial W := IsSimpleModule.nontrivial ℂ[J] η.asModule
  have hd : H.relIndex J ≠ 0 := hdim ▸ pow_ne_zero 2 (Module.finrank_pos (R := ℂ) (M := W)).ne'
  have hxprod : x ∈ ((J : Set (Module.End F V)ˣ) * (B : Set (Module.End F V)ˣ)) * J := hsupport ▸ hx
  obtain ⟨ay, hay, b, hb, rfl⟩ := Set.mem_mul.mp hxprod
  obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.mp hay
  have hle := simpleStratum_relIndex_le_intertwiningDomain hψ hlattices hgroups S hr hs q y hy hd
  have hprod := finrank_intertwiningSpace_mul_relIndex_of_scalar hHJ θ η hscalar hdim _ hx
  rw [relIndex_intertwiningDomain_mul_left_right hnorm y ⟨a, ha⟩ ⟨b, hb⟩, hdim] at hprod
  have hpos := (Nat.pos_of_ne_zero hd).trans_le hle
  apply le_antisymm
  · apply Nat.le_of_not_gt
    intro hgt
    have hlt := Nat.mul_lt_mul_of_pos_right hgt hpos
    rw [one_mul, hprod] at hlt
    exact (not_lt_of_ge hle) hlt
  · obtain ⟨f, hf⟩ := hx
    have : Nontrivial (intertwiningSpace η η (a * y * b)) := ⟨⟨f, 0, hf⟩⟩
    exact Module.finrank_pos

end SimpleStrata

end Langlands.BushnellKutzko
