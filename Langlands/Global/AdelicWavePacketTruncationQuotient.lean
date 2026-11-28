import Langlands.Global.AdelicWavePacketTruncationIntegral
import Langlands.Global.AdelicWavePacketSiegelDecayReduction
import Langlands.Global.ArthurNormOneTruncation
import Langlands.Global.ArthurTruncationFixedPoint
import Langlands.Global.AdelicGroupPolish
import Langlands.Global.LeftCosetCompactFactorUnfolding

/-! # Compact spectral integrals on the rational adelic quotients -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

local notation "Z[" n "]" => (Fin n → ℝ)

/-- The full quotient packet is continuous and its truncation is the integral of the truncated
spectral family. The truncated family on the norm-one quotient is jointly measurable and has
the original compact spectral support. -/
def WavePacketTruncationQuotientStatement : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
    {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (_hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (Tp : V T)
    {n : ℕ} (mu : Measure Z[n]) [IsLocallyFiniteMeasure mu]
    {C : Set Z[n]} (_hC : IsCompact C) {φ : Z[n] → AdelicGroupPoints F G → ℂ},
    Continuous (Function.uncurry φ) →
    (∀ a, ∀ r ∈ rationalSubgroup F G, ∀ x, φ a (r * x) = φ a x) →
    (∀ a ∉ C, ∀ x, φ a x = 0) →
    let packet (q : RationalQuotient F G) := ∫ a, φ a q.out ∂mu
    let L₁ (a : Z[n]) (q : NormOneRationalQuotient F G) :=
      normOneTruncation hG hi D hK hρ Tp (fun x => φ a x) q.out
    Continuous packet ∧ Measurable (Function.uncurry L₁) ∧
    (∀ a ∉ C, ∀ q, L₁ a q = 0) ∧
    ∀ q : RationalQuotient F G,
      truncation hG hi D hK hρ Tp (fun x => packet (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out =
        ∫ a, truncation hG hi D hK hρ Tp (φ a) q.out ∂mu

set_option maxHeartbeats 800000 in
/-- Descend the continuous packet and the measurable truncated family using rational
invariance. On the norm-one group, the truncation formula is the restriction of the full one. -/
theorem wavePacketTruncationQuotient : WavePacketTruncationQuotientStatement := by
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ Tp n mu _ C hC φ hφ hinv hzero packet L₁
  obtain ⟨hm, hL⟩ := wavePacketTruncationIntegral hG hi hν D hK hρ Tp mu hC hφ hinv hzero
  let Θ (x : AdelicGroupPoints F G) := ∫ a, φ a x ∂mu
  have hΘinv (r : AdelicGroupPoints F G) (hr : r ∈ rationalSubgroup F G) (x : AdelicGroupPoints F G) :
      Θ (r * x) = Θ x := integral_congr_ae (Filter.Eventually.of_forall fun a => hinv a r hr x)
  have hrep (x : AdelicGroupPoints F G) :
      packet (LeftCosetSpace.mk (rationalSubgroup F G) x) = Θ x := by
    change Θ ((LeftCosetSpace.mk (rationalSubgroup F G) x).out) = Θ x
    exact LeftCosetSpace.out_mk_of_invariant (rationalSubgroup F G) Θ hΘinv x
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (LeftCosetSpace.continuous_iff (rationalSubgroup F G)).2
    change Continuous (fun x => packet (LeftCosetSpace.mk (rationalSubgroup F G) x))
    simp only [hrep]
    exact continuous_integral_of_forall_notMem_eq_zero mu (hφ.comp continuous_swap) hC
      (fun x a ha => hzero a ha x)
  · let f (a : Z[n]) (x : normOneSubgroup F G) := truncation hG hi D hK hρ Tp (φ a) x
    have hcoe : Measurable (fun z : Z[n] × normOneSubgroup F G =>
        (z.1, (z.2 : AdelicGroupPoints F G))) :=
      measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
    have hm' := hm.comp hcoe
    have hf : Measurable (Function.uncurry f) := by
      change Measurable (fun z : Z[n] × normOneSubgroup F G =>
        truncation hG hi D hK hρ Tp (φ z.1) z.2)
      exact hm'
    have hfinv (a : Z[n]) (r : normOneSubgroup F G) (hr : r ∈ rationalNormOneSubgroup F G)
        (x : normOneSubgroup F G) : f a (r * x) = f a x :=
      Idempotence.truncation_rational_mul hG hi hν D hK hρ Tp (φ a) (hinv a)
        (rationalNormOneSubgroupInclusion F G ⟨r, hr⟩).property x
    have hQ := LeftCosetSpace.measurable_out_of_invariant_prod
      (isDiscrete_rationalNormOneSubgroup F G) f hf hfinv
    change Measurable (fun z : Z[n] × NormOneRationalQuotient F G =>
      normOneTruncation hG hi D hK hρ Tp (fun x => φ z.1 x) z.2.out)
    simpa only [normOneTruncation_restrict hG hi D hK hρ hν Tp, f] using hQ
  · intro a ha q
    change normOneTruncation hG hi D hK hρ Tp (fun x => φ a x) q.out = 0
    exact (normOneTruncation_restrict hG hi D hK hρ hν Tp (φ a) q.out).trans ((hL q.out).2.1 a ha)
  · intro q
    rw [funext hrep]
    exact (hL q.out).2.2

end Langlands.Global.ArthurTruncation
