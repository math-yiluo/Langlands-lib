import Langlands.Global.AdelicWeylCentralPairing
import Langlands.Global.AdelicSquareIntegrableHeightExpansion
import Langlands.Global.AdelicWeakConstantTermEigenReduction

/-! # Central translation of an unshifted weak pairing expansion -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Param[" J "]" => ComplexCharacterParameter F (fam.P J)
local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "Z" => fam.positiveSplitComponent fam.top

attribute [local instance] isClosedImmersion_p

private def centralTranslateLinear (z : Z) : Fun →ₗ[ℂ] Fun where
  toFun := fam.centralTranslate z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem centralTranslate_orthogonal {K : Subgroup (AdelicGroupPoints F G)}
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (Q : Idx) (z : Z) {ψ : Fun}
    (hψ : fam.IsSquareIntegrableOrthogonal K hKc rho hsmooth hcalc Q ψ) :
    fam.IsSquareIntegrableOrthogonal K hKc rho hsmooth hcalc Q (fam.centralTranslate z ψ) := by
  let a := fam.splitLift (show Q ≤ fam.top from Q.property) z
  have he : fam.centralTranslate z ψ = fam.splitComponentRepresentation Q a ψ := by
    funext g
    change ψ (g * fam.centralPoint z) = ψ (map F (fam.P Q) G (fam.p Q) a.val * g)
    have h := fam.map_splitLift (show Q ≤ fam.top from Q.property) z
    change map F (fam.P Q) G (fam.p Q) a.val = fam.centralPoint z at h
    rw [h, (fam.centralPoint_commute z g).eq]
  rw [he]
  exact hψ.splitComponentTranslate fam Q hKc rho hsmooth hcalc a

private theorem hasExponent_parameterTwist {Q : Idx} {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p Q) K) (a : Param[Q]) {v : Fun}
    (hv : IsSplitComponentEquivariant (fam.p Q) (fam.l Q) v) :
    fam.HasExponent Q a (hK.parameterTwist v a) := by
  have h : fam.HasUnnormalizedExponent Q (halfModulusParameter F (fam.P Q)) v := by
    refine ⟨0, fun g => ⟨fun _ => v g, ?_, ?_⟩⟩
    · have hOne : (1 : RealCharacterDual F (fam.P Q) → ℂ) ∈ polynomialFunctions _ 0 := by
        apply Submodule.subset_span
        exact ⟨0, le_rfl, Fin.elim0, by funext y; simp⟩
      simpa only [Pi.smul_def, Pi.one_def, smul_eq_mul, mul_one] using
        Submodule.smul_mem (polynomialFunctions _ 0) (v g) hOne
    · intro x hx
      change v (map F (fam.P Q) G (fam.p Q) x * g) *
        parameterPower F (fam.P Q) (-halfModulusParameter F (fam.P Q)) x = v g
      rw [fam.splitComponentEquivariant_apply Q hv hx g, halfModulus, mul_right_comm,
        ← parameterPower_add, add_neg_cancel, InducedInnerProductIntegrable.parameterPower_zero, one_mul]
  apply (fam.hasExponent_iff Q a _).mpr
  exact add_comm (halfModulusParameter F (fam.P Q)) a ▸ fam.hasUnnormalizedExponent_parameterTwist Q hK a h

set_option maxHeartbeats 2000000 in
/-- In a square-integrable twist decomposition of a central eigenfunction, every summand
retains the same central eigenvalue. -/
theorem centralTranslate_of_squareIntegrableTwistDecomposition {K : Subgroup (AdelicGroupPoints F G)}
    {Q : Idx} (hK : IsIwasawaCompact (fam.p Q) K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) {E : Fun} {s : Finset (Param[Q])}
    {v : Param[Q] → Fun} (h : fam.IsSquareIntegrableTwistDecomposition rho hsmooth hcalc hK E s v)
    (z : Z) (a : ℂ) (he : fam.centralTranslate z E = a • E) :
    ∀ eta ∈ s, fam.centralTranslate z (hK.parameterTwist (v eta) eta) = a • hK.parameterTwist (v eta) eta := by
  classical
  let L := fam.centralTranslateLinear z
  let u (eta : Param[Q]) := hK.parameterTwist (v eta) eta
  let R := E - ∑ eta ∈ s, u eta
  let b (eta : Param[Q]) := a - fam.truncationCentralFactor Q z eta
  let w (eta : Param[Q]) := b eta • v eta
  let diff (eta : Param[Q]) := hK.parameterTwist (w eta) eta
  have hLu (eta : Param[Q]) (heta : eta ∈ s) : L (u eta) = fam.truncationCentralFactor Q z eta • u eta :=
    fam.centralTranslate_parameterTwist Q hK (h.1 eta heta).2.1 eta z
  have hw (eta : Param[Q]) (heta : eta ∈ s) :
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p Q) (fam.iU Q) (fam.l Q) (w eta) :=
    (squareIntegrableInducedForms (fam.p Q) (fam.l Q) hK.isCompact rho hsmooth hcalc (fam.iU Q)).smul_mem _
      (h.1 eta heta)
  have hd (eta : Param[Q]) (heta : eta ∈ s) : a • u eta - L (u eta) = diff eta := by
    rw [hLu eta heta, ← sub_smul]
    funext g
    change b eta * (v eta g * hK.heightPower eta g) = (b eta * v eta g) * hK.heightPower eta g
    rw [mul_assoc]
  have hD : L R - a • R = ∑ eta ∈ s, diff eta := by
    calc
      _ = (∑ eta ∈ s, a • u eta) - (∑ eta ∈ s, L (u eta)) := by
        simp only [R, map_sub, map_sum, show L E = a • E from he, smul_sub, Finset.smul_sum]
        abel
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl hd
  let A := fam.squareIntegrableOrthogonalSubmodule Q hK.isCompact rho hsmooth hcalc
  have hR : R ∈ A := h.2
  have hL : L R ∈ A := fam.centralTranslate_orthogonal hK.isCompact rho hsmooth hcalc Q z h.2
  have hDO : fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc Q (∑ eta ∈ s, diff eta) :=
    hD ▸ A.sub_mem hL (A.smul_mem a hR)
  let ix := (Fintype.equivFin s).symm
  have hH : fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc Q hK (∑ eta ∈ s, diff eta) := by
    refine ⟨Fintype.card s, fun i => w (ix i).val,
      fun i H => Complex.exp (complexParameterPairing F (fam.P Q) (ix i).val H),
      fun i => hw (ix i).val (ix i).property, fun g => ?_⟩
    rw [Finset.sum_apply, ← Finset.sum_coe_sort s]
    apply (Fintype.sum_equiv ix _ _ (fun i => ?_)).symm
    change _ * w (ix i).val g = w (ix i).val g * hK.heightPower (ix i).val g
    exact mul_comm _ _
  have hz := fam.eq_zero_of_squareIntegrableHeightExpansion_of_orthogonal rho hsmooth hcalc Q hK hH hDO
  intro eta heta
  exact sub_eq_zero.mp ((hd eta heta).trans (fam.eq_zero_of_sum_eq_zero_of_hasExponent Q s diff
    (fun t ht => fam.hasExponent_parameterTwist hK t (hw t ht).2.1) hz eta heta)) |>.symm

/-- From an unshifted actual weak pairing expansion and central eigencharacters on both
forms, the translated expansion is obtained by scaling all polynomials by the
sesquilinear product of the two characters. -/
def WeakPairingCentralTransferStatement : Prop :=
  ∀ {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (E Φ : Fun)
    (e : ∀ Q : Idx, fam.UnitaryPairingExpansion Q),
    fam.IsWeakConstantTermPairingExpansion hsmooth hcalc rho hK 1 E Φ e →
    ∀ (z : Z) (a b : ℂ), fam.centralTranslate z E = a • E → fam.centralTranslate z Φ = b • Φ →
      fam.IsWeakConstantTermPairingExpansion hsmooth hcalc rho hK z E Φ
        (fun Q => (e Q).scale (a * starRingEnd ℂ b))

set_option maxHeartbeats 2000000 in
theorem weakPairingCentralTransfer : fam.WeakPairingCentralTransferStatement := by
  intro K hK N d rho hsmooth hcalc E Φ e h z a b hE hΦ Q
  obtain ⟨EQ, ΦQ, s, u, hEQ, hΦQ, hu, hpair⟩ := h Q
  let hKQ := fam.isIwasawaCompact_index hK Q
  refine ⟨EQ, ΦQ, s, u, hEQ, hΦQ, hu, ?_⟩
  have hone (f : Fun) : fam.centralTranslate (1 : Z) f = f := by
    funext g
    change f (g * map F (fam.P fam.top) G (fam.p fam.top) 1) = f g
    rw [map_one, mul_one]
  simp_rw [hone] at hpair
  exact fam.isNormalizedPairingExpansion_centralTranslate Q K hK.isCompact s
    (fun t => hKQ.parameterTwist (u t) t) ΦQ (e Q) hpair a b z
    (fam.centralTranslate_of_squareIntegrableTwistDecomposition hKQ rho hsmooth hcalc hu z a
      (fam.centralTranslate_weakConstantTerm Q z hE hEQ))
    (fam.centralTranslate_weakConstantTerm Q z hΦ hΦQ)

end Langlands.Global.StandardParabolicFamily
