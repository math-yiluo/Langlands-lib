import Langlands.FieldTheory.RealAlgebraicClosure
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Torus.EquivariantCharacterValueDescent
import Langlands.GroupScheme.Torus.FiniteMatrixRowWeightCocharacter
import Langlands.GroupScheme.Torus.RelativeCentralizerReductiveProof
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.SplitCharacterPoint
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof
import Langlands.GroupScheme.Torus.WeilCocharacterTransfer
import Langlands.LinearAlgebra.InvolutiveLatticeSign

/-! # Representatives for real torus points modulo norms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RealTorusNormRepresentatives

private theorem mul_conj_ne_neg_one {K : Type u} [Field K] (e : K ≃+* ℝ)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : σ ≠ 1)
    (z : AlgebraicClosure K) : z * σ z ≠ -1 := by
  let : Algebra K ℂ := ((algebraMap ℝ ℂ).comp e.toRingHom).toAlgebra
  let f : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure K) zero_lt_two
  have hi' : f i ^ 2 = Complex.I ^ 2 := by
    rw [Complex.I_sq, ← map_pow, hi, map_neg, map_one]
  have hI : ∃ j, f j = Complex.I := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi' with h | h
    · exact ⟨i, h⟩
    · exact ⟨-i, by rw [map_neg, h, neg_neg]⟩
  obtain ⟨j, hj⟩ := hI
  have hs : Function.Surjective f := by
    intro y
    refine ⟨algebraMap K _ (e.symm y.re) + algebraMap K _ (e.symm y.im) * j, ?_⟩
    rw [map_add, map_mul, f.commutes, f.commutes, hj]
    change ((e (e.symm y.re) : ℝ) : ℂ) + (e (e.symm y.im) : ℝ) * Complex.I = y
    rw [e.apply_symm_apply, e.apply_symm_apply, Complex.re_add_im]
  let g : AlgebraicClosure K ≃ₐ[K] ℂ := AlgEquiv.ofBijective f ⟨f.injective, hs⟩
  let τ : ℂ ≃ₐ[K] ℂ := (g.symm.trans σ).trans g
  let α : ℂ →ₐ[ℝ] ℂ :=
    { toRingHom := τ.toRingHom
      commutes' r := by
        change τ (Complex.ofReal r) = Complex.ofReal r
        have h := τ.commutes (e.symm r)
        change τ (Complex.ofReal (e (e.symm r))) = Complex.ofReal (e (e.symm r)) at h
        simpa only [e.apply_symm_apply] using h }
  have hα (y : AlgebraicClosure K) : α (g y) = g (σ y) := by
    change g (σ (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  have hc : α = Complex.conjAe.toAlgHom := by
    rcases Complex.real_algHom_eq_id_or_conj α with h | h
    · exfalso
      apply hσ
      ext y
      apply g.injective
      rw [← hα, h]
      rfl
    · exact h
  intro h
  have he := congrArg g h
  rw [map_mul, map_neg, map_one, ← hα, hc] at he
  change g z * starRingEnd ℂ (g z) = -1 at he
  rw [mul_comm, ← Complex.normSq_eq_conj_mul_self] at he
  have hre := congrArg Complex.re he
  have hneg : Complex.normSq (g z) = -1 := by simpa using hre
  linarith [Complex.normSq_nonneg (g z)]

private theorem units_eq_one_or_neg_one_of_sq_eq_one {M : Type u} [Field M]
    (x : Mˣ) (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h : (x : M) ^ 2 = (1 : M) ^ 2 := by
    simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hx
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

private theorem neg_one_unit_ne_one (M : Type u) [Field M] [CharZero M] :
    (-1 : Mˣ) ≠ 1 := by
  intro h
  have hv : (-1 : M) = 1 := congrArg Units.val h
  norm_num at hv

private def signFunctional {Λ M : Type u} [AddCommGroup Λ] [Field M] [CharZero M]
    (z : Multiplicative Λ →* Mˣ)
    (hz : ∀ a, z a ^ 2 = 1) : Λ →ₗ[ℤ] ZMod 2 := by
  classical
  let s : Λ →+ ZMod 2 :=
    { toFun a := if z (.ofAdd a) = 1 then 0 else 1
      map_zero' := by simp
      map_add' a b := by
        change (if z (.ofAdd a * .ofAdd b) = 1 then 0 else 1) =
          (if z (.ofAdd a) = 1 then 0 else 1) + (if z (.ofAdd b) = 1 then 0 else 1)
        rw [map_mul]
        rcases units_eq_one_or_neg_one_of_sq_eq_one _ (hz (.ofAdd a)) with ha | ha <;>
          rcases units_eq_one_or_neg_one_of_sq_eq_one _ (hz (.ofAdd b)) with hb | hb <;>
          simp [ha, hb, neg_one_unit_ne_one M, show (1 : ZMod 2) + 1 = 0 by decide] }
  exact s.toIntLinearMap

private theorem eq_neg_one_zpow_of_signFunctional {Λ M : Type u} [AddCommGroup Λ]
    [Field M] [CharZero M] (z : Multiplicative Λ →* Mˣ) (hz : ∀ a, z a ^ 2 = 1)
    (a : Λ) (n : ℤ) (hn : (n : ZMod 2) = signFunctional z hz a) :
    z (.ofAdd a) = (-1 : Mˣ) ^ n := by
  classical
  change (n : ZMod 2) = (if z (.ofAdd a) = 1 then 0 else 1) at hn
  rcases units_eq_one_or_neg_one_of_sq_eq_one _ (hz (.ofAdd a)) with h | h
  · rw [h, ite_eq_left rfl] at hn
    rw [h, (ZMod.intCast_eq_zero_iff_even.mp hn).neg_one_zpow]
  · rw [h, ite_eq_right (neg_one_unit_ne_one M)] at hn
    have he : ¬ Even n := fun he => zero_ne_one (he.intCast_zmod_two.symm.trans hn)
    rw [h, (Int.not_even_iff_odd.mp he).neg_one_zpow]

private theorem exists_sq_eq_of_isSplitTorus {M : Type u} [Field M] [IsAlgClosed M]
    {T : CommGroupScheme (Spec (CommRingCat.of M))} (hT : IsSplitTorus T.toGrp)
    (p : Lie.AffinePoints T.toGrp M) : ∃ a : Lie.AffinePoints T.toGrp M, a ^ 2 = p := by
  classical
  obtain ⟨I, _, ⟨e⟩⟩ := hT
  let d := (isoPointsEquiv e _).trans (splitTorus.algebraPointsEquiv I M)
  have hr (i : I) : ∃ u : Mˣ, u ^ 2 = d p i := by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (d p i : M) zero_lt_two
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      exact (d p i).ne_zero (by simpa using hx.symm)
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  choose a ha using hr
  refine ⟨d.symm a, d.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  funext i
  exact ha i

end RealTorusNormRepresentatives

open RealTorusNormRepresentatives

/-- Over a field isomorphic to the reals, a torus point on extension to its
algebraic closure is the value at `-1` of a fixed cocharacter times a norm. -/
def RealTorusNormRepresentativesStatement : Prop :=
  ∀ (K : Type u) [Field K], (K ≃+* ℝ) →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of K))), IsTorus T.toGrp →
    ∀ p : Lie.AffinePoints T.toGrp K,
      ∃ (ν : cocharacterLattice ((CommGroupScheme.baseChange
          (algebraBaseMap K (AlgebraicClosure K))).obj T))
        (r : Lie.AffinePoints T.toGrp (AlgebraicClosure K)),
        (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          cocharacterLattice.galoisRepresentation K (AlgebraicClosure K) T σ ν = ν) ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ≠ 1 →
          GaloisPoint.extend K (AlgebraicClosure K) T.toGrp p =
            WeilGm.cocharacterValue K (AlgebraicClosure K) T (CommGroupScheme.groupHom ν)
              (AlgebraicClosure K) (-1) *
            (r * GaloisPoint.conjugate K (AlgebraicClosure K) T.toGrp σ r)

set_option maxHeartbeats 900000 in
/-- Torus point classes modulo the quadratic norm are represented by fixed
cocharacters evaluated at the unit `-1`. -/
theorem realTorusNormRepresentatives : RealTorusNormRepresentativesStatement.{u} := by
  intro K _ e T hT p
  classical
  let M := AlgebraicClosure K
  let TM := (CommGroupScheme.baseChange (algebraBaseMap K M)).obj T
  let X := characterLattice TM
  let ρ := characterLattice.galoisRepresentation K M T
  let β : Lie.AffinePoints TM.toGrp M ≃* Lie.AffinePoints T.toGrp M :=
    Lie.affineBaseChangeEquiv K M T.toGrp M
  let q := β.symm (GaloisPoint.extend K M T.toGrp p)
  let : CharZero K := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  let : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  have hdim : Module.finrank K M = 2 := Langlands.FieldTheory.finrank_algebraicClosure_of_equiv_real e
  let : FiniteDimensional K M := FiniteDimensional.of_finrank_pos (by rw [hdim]; decide)
  have hcard : Nat.card (M ≃ₐ[K] M) = 2 := (IsGalois.card_aut_eq_finrank K M).trans hdim
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : M ≃ₐ[K] M)).mp hcard
  have hσ₂ : σ * σ = 1 := by simpa only [hcard, pow_two] using (pow_card_eq_one' (x := σ))
  have hσi : σ⁻¹ = σ := (eq_inv_of_mul_eq_one_left hσ₂).symm
  have hs₀ : Function.Involutive (ρ σ) := by
    intro χ
    change (ρ σ * ρ σ) χ = χ
    rw [← map_mul, hσ₂, map_one]
    rfl
  let s : X ≃ₗ[ℤ] X := LinearEquiv.ofInvolutive (ρ σ) hs₀
  have hTM : IsSplitTorus TM.toGrp :=
    ((hT.baseChange (K := M)).isRelativeTorus).isSplitTorus_of_isAlgClosed
  have hfree := TorusSurjectionIsogenySection.characterLattice_free_finite hTM
  let : Module.Free ℤ X := hfree.1
  let : Module.Finite ℤ X := hfree.2
  obtain ⟨a, ha⟩ := exists_sq_eq_of_isSplitTorus hTM q
  let g := β.symm.toMonoidHom.comp ((GaloisPoint.conjugate K M T.toGrp σ).comp β.toMonoidHom)
  have hg (x : Lie.AffinePoints TM.toGrp M) :
      g x = EquivariantCharacterValueDescent.inverseConjugate K M T σ x := by
    apply β.injective
    have h := EquivariantCharacterValueDescent.affineBaseChangeEquiv_inverseConjugate K M T σ x
    change β (EquivariantCharacterValueDescent.inverseConjugate K M T σ x) =
      GaloisPoint.conjugate K M T.toGrp σ.symm (β x) at h
    rw [h]
    change β (β.symm (GaloisPoint.conjugate K M T.toGrp σ (β x))) =
      GaloisPoint.conjugate K M T.toGrp σ.symm (β x)
    rw [MulEquiv.apply_symm_apply, show σ.symm = σ from hσi]
  have hgq : g q = q := by
    change β.symm (GaloisPoint.conjugate K M T.toGrp σ (β (β.symm _))) = β.symm _
    rw [MulEquiv.apply_symm_apply, GaloisPoint.conjugate_extend]
  let z := a / g a
  have hz₂ : z ^ 2 = 1 := by
    change (a / g a) ^ 2 = 1
    rw [div_pow, ← map_pow g, ha, hgq, div_self']
  let ev (χ : X) :=
    (Gm.affineUnitsEquiv (CommRingCat.of M) (CommAlgCat.of M M)).toMonoidHom.comp
      (GroupScheme.affinePointsTarget TM.toGrp (CommGroupScheme.groupHom χ) (CommAlgCat.of M M))
  let zval := SplitCharacterPoint.valueHom z
  have hzval (χ : Multiplicative X) : zval χ ^ 2 = 1 := by
    change ev χ.toAdd z ^ 2 = 1
    rw [← map_pow, hz₂, map_one]
  let c := signFunctional zval hzval
  have hc (χ : X) (hχ : s χ = -χ) : c χ = 0 := by
    change (if ev χ z = 1 then (0 : ZMod 2) else 1) = 0
    apply ite_eq_left
    rcases units_eq_one_or_neg_one_of_sq_eq_one (ev χ z) (hzval (.ofAdd χ)) with h | h
    · exact h
    · have hv := EquivariantCharacterValueDescent.characterValue_inverseConjugate K M T σ χ a
      rw [← hg] at hv
      change (ev χ (g a) : M) = σ.symm (Lie.characterValue (ρ σ χ) a : M) at hv
      have hinv : Lie.characterValue (-χ) a = (ev χ a)⁻¹ := by
        let f := SplitCharacterPoint.valueHom a
        change f ((Multiplicative.ofAdd χ)⁻¹) = (f (Multiplicative.ofAdd χ))⁻¹
        exact map_inv f (Multiplicative.ofAdd χ)
      rw [show ρ σ χ = -χ from hχ, hinv, show σ.symm = σ from hσi] at hv
      have hprod : (ev χ z : M) = (ev χ a : M) * σ (ev χ a : M) := by
        change ((ev χ (a / g a) : Mˣ) : M) = _
        rw [map_div]
        simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
        rw [hv, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
      apply False.elim
      apply mul_conj_ne_neg_one e σ hσ (ev χ a : M)
      rw [← hprod, h]
      rfl
  obtain ⟨m, hm, hs⟩ := Langlands.LinearAlgebra.involutiveLatticeSign X s hs₀ c hc
  obtain ⟨ν, hν⟩ := hTM.isPerfPair_latticePairing.bijective_right.surjective m
  have hp (χ : X) : latticePairing TM χ ν = m χ := LinearMap.congr_fun hν χ
  have hfix : ∀ τ : M ≃ₐ[K] M, cocharacterLattice.galoisRepresentation K M T τ ν = ν := by
    intro τ
    by_cases hτ : τ = 1
    · rw [hτ, map_one]; rfl
    · rw [huniq τ hτ]
      apply hTM.isPerfPair_latticePairing.bijective_right.injective
      ext χ
      change latticePairing TM χ (cocharacterLattice.galoisRepresentation K M T σ ν) =
        latticePairing TM χ ν
      rw [latticePairing_galoisRepresentation_right, hσi, hp, hp]
      exact hm χ
  let t := (Gm.affineUnitsEquiv (CommRingCat.of M) (CommAlgCat.of M M)).symm (-1)
  have hza : z = t ≫ (CommGroupScheme.groupHom ν).hom.hom := by
    apply EquivariantCharacterValueDescent.eq_of_characterValue_eq hTM
    intro χ
    rw [Lie.characterValue_cocharacter, MulEquiv.apply_symm_apply, hp]
    exact eq_neg_one_zpow_of_signFunctional zval hzval χ (m χ) (hs χ)
  refine ⟨ν, β a, hfix, fun τ hτ => ?_⟩
  rw [huniq τ hτ]
  have hβg : β (g a) = GaloisPoint.conjugate K M T.toGrp σ (β a) :=
    β.apply_symm_apply _
  have hval : β z = WeilGm.cocharacterValue K M T (CommGroupScheme.groupHom ν) M (-1) :=
    congrArg β hza
  rw [← hval, ← hβg, ← map_mul, ← map_mul]
  have hq : β (a ^ 2) = GaloisPoint.extend K M T.toGrp p := by rw [ha]; exact β.apply_symm_apply _
  rw [← hq]
  congr 1
  change a ^ 2 = a / g a * (a * g a)
  rw [← mul_left_comm, div_mul_cancel, pow_two]

end Langlands.GroupScheme
