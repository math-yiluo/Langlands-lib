import Langlands.Global.AdelicParabolicConstantTermGrowth
import Langlands.Global.AdelicInducingConstantTermCovariance
import Langlands.Global.AdelicLeviCuspTestBounds
import Langlands.Global.AdelicNestedCuspidalQuotient

/-! # Transported convolution on nested cuspidal pairings -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G fam.i fam.ν

/-- The kernel of transported convolution at an external point is the original
kernel multiplied by the ratio of the height powers at the translated and original point. -/
def parameterConvolutionKernel {outer : StandardIndex F G fam.i fam.ν}
    [IsClosedImmersion (fam.p outer).hom.hom.left]
    {K : Subgroup A} (hK : IsIwasawaCompact (fam.p outer) K)
    (lam : ComplexCharacterParameter F (fam.P outer)) (h : A → ℂ) (g : A) : A → ℂ :=
  fun t => h t * (hK.heightPower lam (g * t) / hK.heightPower lam g)

/-- On norm-one Levi fibres the height ratio depends only on the external point
and the integration variable. Pairing the transported convolution therefore
uses the original cusp test and a compactly supported scalar kernel. -/
theorem leviPairing_twistedConvolutionEnd {outer Q : StandardIndex F G fam.i fam.ν}
    [IsClosedImmersion (fam.p outer).hom.hom.left]
    {K : Subgroup A} (hK : IsIwasawaCompact (fam.p outer) K) (hQP : Q ≤ outer)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hρ : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hKinf : Langlands.CompactIwasawa.IsMaximalCompact (fam.leviInfiniteCompact Kinf Q))
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F (fam.P outer))
    {f : C(A, ℂ)} (hf : fam.IsModerateContinuousOnParabolic rho Q f)
    {ψ : AdelicGroupPoints F (fam.M Q) → ℂ} (hψ : fam.IsLeviCuspForm Kinf rho Q ψ) (g : A) :
    Integrable (fam.leviPairingIntegrand Q (hK.twistedConvolutionEnd hsmooth hh lam f) g ψ)
        (normOneRationalQuotientHaarMeasure F (fam.M Q)) ∧
      fam.leviPairing Q (hK.twistedConvolutionEnd hsmooth hh lam f) g ψ =
        rightConvolution F G (fam.parameterConvolutionKernel hK lam h g)
          (fun x => fam.leviPairing Q f x ψ) g := by
  let w := fam.parameterConvolutionKernel hK lam h g
  have hw : Continuous w := hh.1.1.mul
    (((hK.continuous_heightPower lam).comp (continuous_const.mul continuous_id)).div_const _)
  have hws : HasCompactSupport w := HasCompactSupport.of_support_subset_isCompact hh.2.1.isCompact (by
    intro t ht
    by_contra hnot
    apply ht
    change h t * _ = 0
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul])
  have hfinv : IsLeftInvariantUnder F G (rationalImage F (fam.l Q ≫ fam.p Q)) f :=
    fun _ hx x => hf.1 _ (Subgroup.mem_sup_right hx) x
  have hEq : fam.leviPairingIntegrand Q (hK.twistedConvolutionEnd hsmooth hh lam f) g ψ =
      fam.leviPairingIntegrand Q (rightConvolution F G w f) g ψ := by
    funext q
    let m := (Quotient.out q : normOneSubgroup F (fam.M Q))
    let a := map F (fam.M Q) G (fam.l Q ≫ fam.p Q) m.val
    change hK.twistedConvolutionEnd hsmooth hh lam f (a * g) * starRingEnd ℂ (ψ m.val) =
      rightConvolution F G w f (a * g) * starRingEnd ℂ (ψ m.val)
    congr 1
    rw [IsIwasawaCompact.twistedConvolutionEnd_apply]
    change (∫ t, h t * hK.parameterTwist f lam (a * g * t) ∂Measure.haar) /
        hK.heightPower lam (a * g) =
      ∫ t, w t * f (a * g * t) ∂Measure.haar
    rw [← integral_div]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      change h t * (f (a * g * t) * hK.heightPower lam (a * g * t)) /
          hK.heightPower lam (a * g) = w t * f (a * g * t)
      rw [mul_assoc a g t,
        fam.heightPower_normOneLevi_mul outer Q hK hQP lam m g,
        fam.heightPower_normOneLevi_mul outer Q hK hQP lam m (g * t)]
      simp only [w, parameterConvolutionKernel, div_eq_mul_inv]
      ring
  have hresult := fam.leviPairing_rightConvolution_of_cuspForm Q rho hKinf hN hρ hw hws
    f.continuous hf.2.2 hfinv hψ g
  refine ⟨hEq ▸ hresult.1, ?_⟩
  unfold leviPairing at *
  rw [hEq]
  exact hresult.2

/-- After a transported convolution, each nested cuspidal class is still zero
if its original norm-one test pairings all vanish. -/
theorem InCuspidalAnnihilator.twistedConvolutionEnd {outer Q : StandardIndex F G fam.i fam.ν}
    [IsClosedImmersion (fam.p outer).hom.hom.left]
    {K : Subgroup A} (hK : IsIwasawaCompact (fam.p outer) K)
    (hQP : Q ≤ outer) {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hρ : IsClosedSubgroup rho) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hKinf : Langlands.CompactIwasawa.IsMaximalCompact (fam.leviInfiniteCompact Kinf Q))
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F (fam.P outer))
    {f : C(A, ℂ)} (hf : fam.IsModerateContinuousOnParabolic rho Q f)
    (hkill : fam.InCuspidalAnnihilator Kinf rho Q f) :
    fam.InCuspidalAnnihilator Kinf rho Q (hK.twistedConvolutionEnd hsmooth hh lam f) := by
  intro ψ hψ g
  obtain ⟨hI, hpair⟩ := fam.leviPairing_twistedConvolutionEnd hK hQP rho hN hρ hsmooth hKinf
    hh lam hf hψ g
  refine ⟨hI, hpair.trans ?_⟩
  unfold rightConvolution
  simp only [fun x => (hkill ψ hψ x).2, mul_zero, integral_zero]

/-- Transported convolution gives the same cuspidal class on any two moderate
continuous representatives of one class. -/
theorem cuspidalQuotient_twistedConvolutionEnd_eq_of_eq
    {outer Q : StandardIndex F G fam.i fam.ν}
    [IsClosedImmersion (fam.p outer).hom.hom.left]
    {K : Subgroup A} (hK : IsIwasawaCompact (fam.p outer) K)
    (hQP : Q ≤ outer) {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hρ : IsClosedSubgroup rho) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hKinf : Langlands.CompactIwasawa.IsMaximalCompact (fam.leviInfiniteCompact Kinf Q))
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F (fam.P outer))
    {f g : C(A, ℂ)} (hf : fam.IsModerateContinuousOnParabolic rho Q f)
    (hg : fam.IsModerateContinuousOnParabolic rho Q g)
    (heq : (fam.cuspidalAnnihilator Kinf rho Q).mkQ f =
      (fam.cuspidalAnnihilator Kinf rho Q).mkQ g) :
    (fam.cuspidalAnnihilator Kinf rho Q).mkQ (hK.twistedConvolutionEnd hsmooth hh lam f) =
      (fam.cuspidalAnnihilator Kinf rho Q).mkQ (hK.twistedConvolutionEnd hsmooth hh lam g) := by
  let M := fam.continuousParabolicModerateSubmodule rho hN Q
  let E := fam.cuspidalAnnihilator Kinf rho Q
  let D := hK.twistedConvolutionEnd hsmooth hh lam
  let R := E.mkQ.comp (ContinuousMap.coeFnLinearMap ℂ)
  have hfM : f ∈ M := (fam.mem_continuousParabolicModerateSubmodule_iff rho hN Q f).2 hf
  have hgM : g ∈ M := (fam.mem_continuousParabolicModerateSubmodule_iff rho hN Q g).2 hg
  have hdiff : fam.IsModerateContinuousOnParabolic rho Q (f - g : C(A, ℂ)) :=
    (fam.mem_continuousParabolicModerateSubmodule_iff rho hN Q (f - g)).1 (M.sub_mem hfM hgM)
  have hquot : R (f - g) = 0 := by
    rw [map_sub, show R f = R g from heq, sub_self]
  have hkill : fam.InCuspidalAnnihilator Kinf rho Q (f - g : C(A, ℂ)) :=
    (Submodule.Quotient.mk_eq_zero E).1 hquot
  have hkill' := InCuspidalAnnihilator.twistedConvolutionEnd fam hK hQP rho hN hρ hsmooth
    hKinf hh lam hdiff hkill
  have hquot' : R (D (f - g)) = 0 := (Submodule.Quotient.mk_eq_zero E).2 hkill'
  rw [map_sub, map_sub] at hquot'
  exact sub_eq_zero.mp hquot'

end Langlands.Global.StandardParabolicFamily
