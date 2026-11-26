import Langlands.Global.AdelicPrincipalQuotientMeasure
import Langlands.Global.AdelicPrincipalQuotientProductMeasureProof
import Langlands.Global.AdelicSpectralDecompositionReduction
import Langlands.Global.AdelicWavePacketProductPairingProof
import Langlands.Global.LeftCosetProductMeasureProof
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Isometric lifting of quotient classes by an ambient wave-packet profile -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate

namespace Langlands.Global

open GroupScheme AdelicGroupPoints RestrictionSplitCentre

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G) {m : ℕ}
  (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ)
  (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b) (hbne : b ≠ 0)

local notation "μQ" => canonicalMeasure F G
local notation "μfull" => rationalQuotientHaarMeasure F G
local notation "lift" => ambientProfileQuotientLift hG eG b
local notation "E" => principalQuotientProductEquiv F G hG
local notation "c" => (∫ a : canonicalSubgroup F G, ‖ambientWavePacketProfile eG b (Subtype.val a)‖ ^ 2
  ∂(positiveCentreHaarMeasure F G hG))

include hb hbc hbne in
private theorem memLp_ambientProfileL2Lift (f : Lp ℂ 2 μQ) :
    MemLp (lift f) 2 μfull :=
  ((wavePacketProductPairing_of_productMeasure principalQuotientProductMeasure
    F G hG eG b hb hbc hbne).2.2.1 f).mpr (Lp.memLp f)

/-- Multiplication by the profile gives a linear lift of `L²` classes. -/
private def ambientProfileL2LinearMap : Lp ℂ 2 μQ →ₗ[ℂ] Lp ℂ 2 μfull := by
  have hq : QuasiMeasurePreserving (Prod.snd ∘ E) μfull μQ :=
    Measure.quasiMeasurePreserving_snd.comp (principalQuotientProductMeasure F G hG).quasiMeasurePreserving
  let hLp := memLp_ambientProfileL2Lift hG eG b hb hbc hbne
  refine { toFun := fun f => (hLp f).toLp (lift f), map_add' := ?_, map_smul' := ?_ }
  · intro f g
    apply Lp.ext
    filter_upwards [(hLp (f + g)).coeFn_toLp, (hLp f).coeFn_toLp, (hLp g).coeFn_toLp,
      Lp.coeFn_add ((hLp f).toLp (lift f)) ((hLp g).toLp (lift g)),
      hq.ae_eq_comp (Lp.coeFn_add f g)] with x hsum hf hg hadd hfg
    simp only [Pi.add_apply] at hadd
    rw [hadd, hsum, hf, hg]
    change (f + g : Lp ℂ 2 μQ) (E x).2 = f (E x).2 + g (E x).2 at hfg
    dsimp only [ambientProfileQuotientLift]
    rw [hfg, mul_add]
  · intro z f
    apply Lp.ext
    filter_upwards [(hLp (z • f)).coeFn_toLp, (hLp f).coeFn_toLp,
      Lp.coeFn_smul z ((hLp f).toLp (lift f)),
      hq.ae_eq_comp (Lp.coeFn_smul z f)] with x hsmul hf hLp_smul hzf
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hLp_smul
    rw [hLp_smul, hsmul, hf]
    change (z • f : Lp ℂ 2 μQ) (E x).2 = z • f (E x).2 at hzf
    dsimp only [ambientProfileQuotientLift]
    rw [hzf, smul_eq_mul, smul_eq_mul]
    ac_rfl

/-- Lift by the ambient profile divided by its positive `L²` norm. -/
def ambientProfileL2Isometry : Lp ℂ 2 μQ →ₗᵢ[ℂ] Lp ℂ 2 μfull := by
  let J := ambientProfileL2LinearMap hG eG b hb hbc hbne
  let s : ℝ := (Real.sqrt c)⁻¹
  have hpair := wavePacketProductPairing_of_productMeasure principalQuotientProductMeasure
    F G hG eG b hb hbc hbne
  have hrep (f : Lp ℂ 2 μQ) : (J f : RationalQuotient F G → ℂ) =ᵐ[μfull] lift f :=
    (memLp_ambientProfileL2Lift hG eG b hb hbc hbne f).coeFn_toLp
  have hJ (f g : Lp ℂ 2 μQ) : inner ℂ (J f) (J g) = ((c : ℝ) : ℂ) * inner ℂ f g := by
    rw [l2_inner_eq_integral_mul_conj (hrep g) (hrep f)]
    rw [l2_inner_eq_integral_mul_conj (Filter.EventuallyEq.rfl (f := (g : _ → ℂ)))
      (Filter.EventuallyEq.rfl (f := (f : _ → ℂ)))]
    exact hpair.2.2.2 g f (Lp.memLp g) (Lp.memLp f)
  have hpos : 0 < c := hpair.1
  have hnorm : s * s * c = 1 := by
    dsimp only [s]
    rw [← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  have hnormC : (s : ℂ) * (s : ℂ) * ((c : ℝ) : ℂ) = 1 := by exact_mod_cast hnorm
  refine ((s : ℂ) • J).isometryOfInner fun f g => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hJ, ← mul_assoc, ← mul_assoc, hnormC, one_mul]

end Langlands.Global
