import Langlands.BushnellKutzko.BetaExtensionTwist.QuotientPairing
import Langlands.BushnellKutzko.BetaExtensionTwist.SimpleLayerDual
import Langlands.BushnellKutzko.BetaExtensionTwist.UnitIndex

/-! # The level-one intersection index for a centralizer translate -/

noncomputable section
open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "tr" => LinearMap.trace F V

private theorem char_eq_one_of_mem_maximalIdealInField {ψ : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψ) {x : F} (hx : x ∈ maximalIdealInField 𝒪[F] F) :
    ψ x = 1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact hψ.1 z hz

private theorem mem_maximalIdealInField_of_char_mul_eq_one {ψ : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψ) {x : F} (hx : ∀ z : 𝒪[F], ψ ((z : F) * x) = 1) :
    x ∈ maximalIdealInField 𝒪[F] F := by
  by_cases hv : valuation F x < 1
  · exact ⟨⟨x, hv.le⟩, (valuation F).mem_maximalIdeal_iff.mpr hv, rfl⟩
  have hvx := le_of_not_gt hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨s, hs⟩ := hψ.2
  have hdiv : valuation F ((s : F) / x) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (zero_lt_one.trans_le hvx)]
    exact s.property.trans hvx
  exact (hs (by simpa only [div_mul_cancel₀ _ hx0] using hx ⟨(s : F) / x, hdiv⟩)).elim

private def unitConjLinearEquiv (y : G) : A ≃ₗ[𝒪[F]] A where
  __ := unitConjAddEquiv y
  map_smul' c x := by
    change (y : A) * (c • x) * ((y⁻¹ : G) : A) = c • ((y : A) * x * ((y⁻¹ : G) : A))
    rw [mul_smul_comm, smul_mul_assoc]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The level-one additive index cannot decrease on intersecting both lattices
with their translates by an element of the centralizer. -/
theorem simpleLayer_relIndex_le_intersection {ψ : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψ)
    (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (y : G) (hy : y ∈ centralizerUnitGroup S.b) :
    let H := simpleHLayer S.chain S.n S.b q.tail 1
    let J := simpleJLayer S.chain S.n S.b q.tail 1
    let c := (unitConjAddEquiv y).toAddMonoidHom
    H ≤ J → H.toAddSubgroup.relIndex J.toAddSubgroup ≠ 0 →
    H.toAddSubgroup.relIndex J.toAddSubgroup ≤
      (H.toAddSubgroup.comap c ⊓ H.toAddSubgroup).relIndex
        (J.toAddSubgroup.comap c ⊓ J.toAddSubgroup) := by
  intro H J c hHJ hfinite
  let L := S.chain
  let β := S.b
  let a := adjointMap 𝒪[F] β
  let e := unitConjLinearEquiv y
  let H' := H.comap e.toLinearMap
  let J' := J.comap e.toLinearMap
  let : FiniteDimensional F V := L.finiteDimensional
  let eTrace := endTracePairing.toDual (endTracePairing_nondegenerate (F := F) (V := V))
  have hHJ' : H' ≤ J' := Submodule.comap_mono hHJ
  have heMul (x z : A) : e (x * z) = e x * e z := unitConjAddEquiv_mul y x z
  have heβ : e β = β := by
    change (y : A) * β * ((y⁻¹ : G) : A) = β
    have h := (show Commute β (y : A) from hy).eq
    rw [← h, mul_assoc, Units.mul_inv, mul_one]
  have heAdj (x : A) : e (a x) = a (e x) := by
    change e (β * x - x * β) = β * e x - e x * β
    rw [map_sub, heMul, heMul, heβ]
  have heTrace (x z : A) : tr (e x * e z) = tr (x * z) := by
    rw [← heMul]
    exact LinearMap.trace_conj F _ y
  have hd : ∀ x, a x ∈ traceLatticeDual H ↔ a x ∈ J.map a :=
    (simpleLayer_traceDual_adjoint S hr q).1
  have hd' (x : A) : a x ∈ traceLatticeDual H' ↔ a x ∈ J'.map a := by
    have htrace : a x ∈ traceLatticeDual H' ↔ a (e x) ∈ traceLatticeDual H := by
      simp only [mem_traceLatticeDual, ← heAdj]
      constructor
      · intro ht z hz
        have hpre : e.symm z ∈ H' := by
          change e (e.symm z) ∈ H
          rwa [e.apply_symm_apply]
        have h := ht (e.symm z) hpre
        rwa [← heTrace (a x) (e.symm z), e.apply_symm_apply] at h
      · intro ht z hz
        simpa only [heTrace] using ht (e z) (show e z ∈ H from hz)
    rw [htrace, hd]
    constructor
    · rintro ⟨z, hz, heq⟩
      refine ⟨e.symm z, ?_, e.injective ?_⟩
      · change e (e.symm z) ∈ J
        rwa [e.apply_symm_apply]
      · rw [heAdj, e.apply_symm_apply, heq, heAdj]
    · rintro ⟨z, hz, heq⟩
      refine ⟨e z, hz, ?_⟩
      rw [← heAdj z, heq, heAdj]
  obtain ⟨hf, hnorm⟩ := hs.1.1
  obtain ⟨p, hp, hfix, hp₁, hp₁'⟩ := exists_common_centralizer_projection L β hf hnorm y hy
  have hQ : centralizerLattice L β 1 ≤ H := (centralizer_le_simpleLayers L S.n β q.tail).1
  have hpH {z : A} (hz : z ∈ L.endFiltration 1) : p z ∈ H := hQ ⟨hp₁ z hz, hp z⟩
  have hpH' {z : A} (hz : e z ∈ L.endFiltration 1) : p z ∈ H' := by
    change e (p z) ∈ H
    refine hQ ⟨hp₁' z hz, ?_⟩
    change a (e (p z)) = 0
    rw [← heAdj, show a (p z) = 0 from hp z, map_zero]
  have hcommon (x : A) (hx : a x ∈ traceLatticeDual (H ⊔ H')) :
      ∃ w ∈ J ⊓ J', a w = a x := by
    rw [traceLatticeDual_sup] at hx
    obtain ⟨t, ht, ht_eq⟩ := (hd x).mp hx.1
    obtain ⟨s, hs, hs_eq⟩ := (hd' x).mp hx.2
    have hts : adjointMap F β (t - s) = 0 := by
      change a (t - s) = 0
      rw [map_sub, ht_eq, hs_eq, sub_self]
    have hdiff : t - p t = s - p s := by
      have h := hfix (t - s) hts
      rw [map_sub] at h
      calc
        t - p t = s - p s + ((t - s) - (p t - p s)) := by abel
        _ = s - p s := by rw [h, sub_self, add_zero]
    refine ⟨t - p t, ⟨J.sub_mem ht (hHJ (hpH ht.2)), ?_⟩, ?_⟩
    · rw [hdiff]
      exact J'.sub_mem hs (hHJ' (hpH' hs.2))
    · rw [map_sub, ht_eq, show a (p t) = 0 from hp t, sub_zero]
  have hann {w : A} (hw : w ∈ J ⊓ J') : a w ∈ traceLatticeDual (H ⊔ H') := by
    rw [traceLatticeDual_sup]
    exact ⟨(hd w).mpr ⟨w, hw.1, rfl⟩, (hd' w).mpr ⟨w, hw.2, rfl⟩⟩
  have hsum {x : A} (hx : x ∈ J ⊔ J') {w : A} (hw : w ∈ H ⊓ H') :
      tr (a w * x) ∈ maximalIdealInField 𝒪[F] F := by
    have hskew : tr (a w * x) = -tr (a x * w) := by
      change tr ((β * w - w * β) * x) = -tr ((β * x - x * β) * w)
      rw [LinearMap.trace_mul_comm F (β * x - x * β) w]
      rw [sub_mul, mul_sub, map_sub, map_sub, neg_sub,
        LinearMap.trace_mul_comm F (β * w) x, ← mul_assoc x β w,
        LinearMap.trace_mul_comm F (x * β) w, mul_assoc w β x]
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    have hu' := mem_traceLatticeDual.mp ((hd u).mpr ⟨u, hu, rfl⟩) w hw.1
    have hv' := mem_traceLatticeDual.mp ((hd' v).mpr ⟨v, hv, rfl⟩) w hw.2
    obtain ⟨r, hr, hr_eq⟩ := hu'
    obtain ⟨s, hs, hs_eq⟩ := hv'
    refine ⟨-(r + s), neg_mem (add_mem hr hs), ?_⟩
    rw [hskew, map_add, add_mul, map_add, ← hr_eq, ← hs_eq]
    rfl
  have hfg : H.FG := (L.fg_endFiltration 1).of_le inf_le_right
  have hfg' : H'.FG := by
    rw [show H' = H.map e.symm.toLinearMap from Submodule.comap_equiv_eq_map_symm _ _]
    exact hfg.map _
  let b : (J ⊔ J').toAddSubgroup →+ AddChar (J ⊓ J').toAddSubgroup ℂ :=
    { toFun x := ψ.compAddMonoidHom
        (((endTracePairing.flip (x : A)).restrictScalars 𝒪[F]).comp
          (a.comp (J ⊓ J').subtype)).toAddMonoidHom
      map_zero' := by
        ext w : 1
        change ψ (tr (a w * 0)) = 1
        rw [mul_zero, map_zero, AddChar.map_zero_eq_one]
      map_add' x z := by
        ext w : 1
        change ψ (tr (a w * ((x : A) + z))) = ψ (tr (a w * x)) * ψ (tr (a w * z))
        rw [mul_add, map_add, AddChar.map_add_eq_mul] }
  let U := (H ⊔ H').toAddSubgroup.addSubgroupOf (J ⊔ J').toAddSubgroup
  let T := (H ⊓ H').toAddSubgroup.addSubgroupOf (J ⊓ J').toAddSubgroup
  have hbU : ∀ x ∈ U, b x = 0 := by
    intro x hx
    ext w : 1
    change ψ (tr (a (w : A) * (x : A))) = 1
    exact char_eq_one_of_mem_maximalIdealInField hψ (mem_traceLatticeDual.mp (hann w.property) _ hx)
  have hbT : ∀ x w, w ∈ T → b x w = 1 :=
    fun x w hw => char_eq_one_of_mem_maximalIdealInField hψ (hsum x.property hw)
  have hker (x : (J ⊔ J').toAddSubgroup) (hx : ∀ w, b x w = 1) : x ∈ U := by
    change (x : A) ∈ H ⊔ H'
    rw [← traceLatticeDual_dual_of_fg (hfg.sup hfg')]
    refine mem_traceLatticeDual.mpr fun u hu => ?_
    let v := eTrace.symm ((endTracePairing u).comp p)
    have hv (z : A) : tr (v * z) = tr (u * p z) := by
      change eTrace (eTrace.symm ((endTracePairing u).comp p)) z = _
      rw [eTrace.apply_symm_apply]
      rfl
    have hvJ : v ∈ traceLatticeDual (J ⊔ J') := by
      rw [traceLatticeDual_sup]
      refine ⟨mem_traceLatticeDual.mpr (fun z hz => ?_), mem_traceLatticeDual.mpr (fun z hz => ?_)⟩
      · rw [hv]
        exact mem_traceLatticeDual.mp hu _ (Submodule.mem_sup_left (hpH hz.2))
      · rw [hv]
        exact mem_traceLatticeDual.mp hu _ (Submodule.mem_sup_right (hpH' hz.2))
    have huv : u - v ∈ traceLatticeDual (H ⊔ H') :=
      Submodule.sub_mem _ hu (traceLatticeDual_antitone (sup_le_sup hHJ hHJ') hvJ)
    have huv' : u - v ∈ (adjointMap F β).range := by
      rw [range_adjoint_eq_traceAnnilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
      intro z hz
      change tr ((u - v) * z) = 0
      rw [sub_mul, map_sub, hv, hfix z hz, sub_self]
    obtain ⟨z, hz⟩ := huv'
    obtain ⟨w, hw, heq⟩ := hcommon z (show a z ∈ _ from hz.symm ▸ huv)
    have hchar : tr (a w * (x : A)) ∈ maximalIdealInField 𝒪[F] F := by
      apply mem_maximalIdealInField_of_char_mul_eq_one hψ
      intro t
      have ht := hx ⟨t • w, Submodule.smul_mem _ t hw⟩
      change ψ (tr (a (t • w) * (x : A))) = 1 at ht
      rw [map_smul] at ht
      change ψ (tr (((t : F) • a w) * (x : A))) = 1 at ht
      simpa only [smul_mul_assoc, map_smul, smul_eq_mul] using ht
    have hwv : a w + v = u := by
      rw [heq, show a z = u - v from hz, sub_add_cancel]
    rw [LinearMap.trace_mul_comm F, ← hwv, add_mul, map_add]
    obtain ⟨r, hr, hr_eq⟩ := hchar
    obtain ⟨s, hs, hs_eq⟩ := mem_traceLatticeDual.mp hvJ x x.property
    exact ⟨r + s, Ideal.add_mem _ hr hs, by rw [← hr_eq, ← hs_eq]; rfl⟩
  have hprimed : H'.toAddSubgroup.relIndex J'.toAddSubgroup = H.toAddSubgroup.relIndex J.toAddSubgroup := by
    change (H.toAddSubgroup.comap c).relIndex (J.toAddSubgroup.comap c) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective ((unitConjAddEquiv y).surjective)]
  have hproduct : T.index * U.index = H.toAddSubgroup.relIndex J.toAddSubgroup ^ 2 := by
    have h := relIndex_inf_mul_sup H.toAddSubgroup H'.toAddSubgroup J.toAddSubgroup J'.toAddSubgroup hHJ hHJ'
    rw [← Submodule.sup_toAddSubgroup, ← Submodule.sup_toAddSubgroup, hprimed, ← pow_two] at h
    exact h
  have : T.FiniteIndex := ⟨fun h => (pow_ne_zero 2 hfinite) (by simpa only [h, zero_mul] using hproduct.symm)⟩
  have hle := index_le_of_quotientCharacterPairing U T b hbU hbT hker
  have hbound : H.toAddSubgroup.relIndex J.toAddSubgroup ≤ T.index := by
    apply Nat.le_of_not_gt
    intro ht
    have hlt := Nat.mul_lt_mul_of_pos_right ht (Nat.zero_lt_of_ne_zero hfinite)
    have hle' := Nat.mul_le_mul_left T.index (hle.trans ht.le)
    rw [pow_two] at hproduct
    exact (hle'.trans_lt hlt).ne hproduct
  change H.toAddSubgroup.relIndex J.toAddSubgroup ≤ (H'.toAddSubgroup ⊓ H.toAddSubgroup).relIndex
    (J'.toAddSubgroup ⊓ J.toAddSubgroup)
  change _ ≤ (H.toAddSubgroup ⊓ H'.toAddSubgroup).relIndex
    (J.toAddSubgroup ⊓ J'.toAddSubgroup) at hbound
  rwa [inf_comm H'.toAddSubgroup, inf_comm J'.toAddSubgroup]

/-- The original relative index is a lower bound for the index on the level-one
common domain at a centralizing unit. -/
theorem simpleStratum_relIndex_le_intertwiningDomain {ψ : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψ)
    (hlattices : SimpleStratumLatticePropertiesStatement.{uF, uV})
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (y : G) (hy : y ∈ centralizerUnitGroup S.b) :
    let H := simpleHGroup S.chain S.n S.b q.tail 1
    let J := simpleJGroup S.chain S.n S.b q.tail 1
    H.relIndex J ≠ 0 → H.relIndex J ≤ (intertwiningDomain H H y).relIndex (intertwiningDomain J J y) := by
  intro H J hfinite
  have hidentity (K : Subgroup G) : intertwiningDomain K K 1 = K := by
    ext g
    simp [mem_intertwiningDomain]
  have hindex := simpleStratum_relIndex_intertwiningDomain hlattices hgroups S hr hs q 1
  have hone (K : AddSubgroup A) : K.comap (unitConjAddEquiv (1 : G)).toAddMonoidHom = K := by
    ext x
    change ((1 : G) : A) * x * (((1 : G)⁻¹ : G) : A) ∈ K ↔ x ∈ K
    simp
  dsimp only at hindex
  rw [hidentity, hidentity, hone, hone, inf_idem, inf_idem] at hindex
  rw [simpleStratum_relIndex_intertwiningDomain hlattices hgroups S hr hs q y, hindex]
  have hHJ := ((hlattices F V S hr hs q).2.1.2.2.2.2.2.2.2 1).2.2
  exact simpleLayer_relIndex_le_intersection hψ S hr hs q y hy hHJ (hindex ▸ hfinite)

end Langlands.BushnellKutzko
