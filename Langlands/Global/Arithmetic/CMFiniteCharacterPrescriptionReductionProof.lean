import Langlands.Global.Arithmetic.CMFiniteCharacterPrescriptionReductionStatement

noncomputable section

universe u

namespace Langlands.Global

open NumberField AdelicFunctoriality

private theorem ideleEquiv_infiniteFactor
    {K : Type u} [Field K] [NumberField K] (e : K ≃+* K)
    (a : (InfiniteAdeles K)ˣ) :
    ideleEquiv e (infiniteIdelesInclusion K a) =
      infiniteIdelesInclusion K (Units.mapEquiv (infiniteAdeleEquiv e).toMulEquiv a) := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · exact map_one (finiteAdeleEquiv e)

private theorem comp_trivialInfinity
    {K : Type u} [Field K] [NumberField K] (e : K ≃+* K)
    (ψ : HeckeCharacter K) (hψ : ψ.HasPrescribedInfinityComponent 1) :
    HeckeCharacter.HasPrescribedInfinityComponent
      (ψ.comp (ideleClassEquiv e : IdeleClasses K →ₜ* IdeleClasses K)) 1 := by
  apply ContinuousMonoidHom.ext
  intro a
  change ψ (QuotientGroup.mk (ideleEquiv e (infiniteIdelesInclusion K a))) = 1
  rw [ideleEquiv_infiniteFactor]
  exact DFunLike.congr_fun hψ _

private theorem comp_trivialFinite
    {K : Type u} [Field K] [NumberField K] (e : K ≃+* K)
    (ψ : HeckeCharacter K) (p : FinitePlace K) (hψ : ψ.finiteComponent p = 1) :
    HeckeCharacter.finiteComponent
      (ψ.comp (ideleClassEquiv e : IdeleClasses K →ₜ* IdeleClasses K))
      (finitePlaceEquiv e p) = 1 := by
  apply ContinuousMonoidHom.ext
  intro a
  change ψ (ideleClassEquiv e
    (IdeleClassGroup.ofAdicCompletion (RingOfIntegers K) K (finitePlaceEquiv e p) a)) = 1
  rw [ideleClassEquiv_ofAdicCompletion]
  exact DFunLike.congr_fun hψ _

private theorem finitePlaceComplexConj_involutive
    {K : Type u} [Field K] [NumberField K] [IsCMField K] :
    Function.Involutive (finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv) := by
  have h : (IsCMField.complexConj K).toRingEquiv.trans
      (IsCMField.complexConj K).toRingEquiv = RingEquiv.refl K := by
    ext x
    exact IsCMField.complexConj_apply_apply K x
  intro p
  have hh := finitePlaceEquiv_trans (IsCMField.complexConj K).toRingEquiv
    (IsCMField.complexConj K).toRingEquiv
  rw [h, finitePlaceEquiv_refl] at hh
  exact (Equiv.congr_fun hh p).symm

/-- The finite-order prescription premise implies its CM conjugate-self-dual form. -/
theorem cmFiniteCharacterPrescriptionOfFiniteOrder :
    CMFiniteCharacterPrescriptionOfFiniteOrderStatement.{u} := by
  intro hPrescription K _ _ _ S hS η hη
  classical
  choose n hn hηn using hη
  let N : ℕ := ∏ w : {w // w ∈ S}, n w
  have hN : 0 < N := Finset.prod_pos fun w _ => hn w
  have hηN (w : {w // w ∈ S}) : η w ^ N = 1 := by
    have hd : n w ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ w)
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, hηn w]
    ext x
    simp
  let c := finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv
  let T := S ∪ S.map c.toEmbedding
  let θ : (w : {w // w ∈ T}) → (FiniteCompletion K w.1)ˣ →ₜ* ℂˣ :=
    fun w => if hw : w.1 ∈ S then η ⟨w.1, hw⟩ else 1
  have hθN (w : {w // w ∈ T}) : θ w ^ N = 1 := by
    dsimp [θ]
    split_ifs with hw
    · exact hηN ⟨w.1, hw⟩
    · ext x
      simp
  obtain ⟨ψ, hψorder, hψfin, hψinf⟩ :=
    hPrescription K T N hN θ 1 hθN (by ext x; simp)
  have hSelected (w : {w // w ∈ S}) : ψ.finiteComponent w.1 = η w := by
    have hwT : w.1 ∈ T := Finset.mem_union_left _ w.2
    simpa only [θ, dite_eq_left w.2] using hψfin ⟨w.1, hwT⟩
  have hConjugate (w : {w // w ∈ S}) : ψ.finiteComponent (c w.1) = 1 := by
    have hwc : c w.1 ∈ S.map c.toEmbedding := Finset.mem_map.mpr ⟨w.1, w.2, rfl⟩
    have hwNot : c w.1 ∉ S := fun h => Finset.disjoint_left.mp hS h hwc
    have hwT : c w.1 ∈ T := Finset.mem_union_right _ hwc
    simpa only [θ, dite_eq_right hwNot] using hψfin ⟨c w.1, hwT⟩
  let ψc : HeckeCharacter K := ψ.comp (ideleClassComplexConj (K := K) : IdeleClasses K →ₜ* IdeleClasses K)
  have hψcfin (w : {w // w ∈ S}) : ψc.finiteComponent w.1 = 1 := by
    have h := comp_trivialFinite (IsCMField.complexConj K).toRingEquiv
      ψ (c w.1) (hConjugate w)
    change ψc.finiteComponent (c (c w.1)) = 1 at h
    have hc : c (c w.1) = w.1 := finitePlaceComplexConj_involutive w.1
    rwa [hc] at h
  have hψcinf : ψc.HasPrescribedInfinityComponent 1 :=
    comp_trivialInfinity (IsCMField.complexConj K).toRingEquiv ψ hψinf
  refine ⟨ψ / ψc, ?_, ?_, ?_, ?_⟩
  · refine ⟨2 * N, by omega, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    have h₁ : ψ x ^ (2 * N) = 1 := by
      simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
        using DFunLike.congr_fun hψorder x
    have h₂ : ψ (ideleClassComplexConj x) ^ (2 * N) = 1 := by
      simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
        using DFunLike.congr_fun hψorder (ideleClassComplexConj x)
    rw [ContinuousMonoidHom.pow_apply]
    change (ψ x / ψ (ideleClassComplexConj x)) ^ (2 * N) = 1
    rw [div_pow, h₁, h₂, one_div_one]
  · intro x
    change ψ (ideleClassComplexConj x) /
      ψ (ideleClassComplexConj (ideleClassComplexConj x)) =
      (ψ x / ψ (ideleClassComplexConj x))⁻¹
    rw [ideleClassComplexConj_involutive]
    exact (inv_div _ _).symm
  · change ψ.atInfinity / ψc.atInfinity = 1
    rw [hψinf, hψcinf]
    apply ContinuousMonoidHom.ext
    intro x
    change (1 : ℂˣ) / 1 = 1
    exact one_div_one
  · intro w
    change ψ.finiteComponent w.1 / ψc.finiteComponent w.1 = η w
    rw [hSelected w, hψcfin w]
    apply ContinuousMonoidHom.ext
    intro x
    change η w x / 1 = η w x
    exact div_one _

end Langlands.Global
