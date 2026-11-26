import Langlands.Global.AdelicIntertwiningNormalizedLevi
import Langlands.Global.AdelicIntertwiningIntegrability

/-! # Compact tests of the normalized Levi kernel -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.QuotientIntegration

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P}
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {l' : M' ⟶ Q}
  (iU : U ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {c : M' ⟶ M} (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))
local notation "wA" => innerAdelicPoint F G w
local notation "Γ" => intertwiningRationalSubgroup F p iU (iV ≫ q) wA
local notation "μ" => intertwiningMeasure F p iU (iV ≫ q) wA
local notation "varg(" x "," y ")" => (wA⁻¹ * Subtype.val (x : Vₐ) * y)
local notation "mP" m => map F M P l (map F M' M c m)
local notation "mQ" m => map F M' Q l' m

/-- The integrand for the normalized target Levi restriction, before the height factor at
its fixed external argument. -/
def IsIwasawaCompact.intertwiningLeviKernel (l : M ⟶ P) (c : M' ⟶ M)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) (m : AdelicGroupPoints F M') (x : LeftCosetSpace Γ) : ℂ :=
  let y := varg(x.out, g)
  let m₀ := map F M P l (map F M' M c m)
  (parameterPower F P (-halfModulusParameter F P) m₀ *
    φ (map F P G p m₀ * y)) * hK.heightPower lam y

private theorem continuous_parameterPower_of_pairing {S : GroupScheme (Spec (CommRingCat.of F))}
    (lam : ComplexCharacterParameter F S) : Continuous (parameterPower F S lam) :=
  Complex.continuous_exp.comp ((continuous_complexParameterPairing_apply lam).comp
    (continuous_characterLog F S))

variable {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
  (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)

include hφc hφ hU in
/-- The normalized kernel is jointly continuous on the Levi and the rational radical quotient. -/
theorem IsIwasawaCompact.continuous_intertwiningLeviKernel
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    Continuous (fun z : AdelicGroupPoints F M' × LeftCosetSpace Γ =>
      hK.intertwiningLeviKernel iU iV w l c φ lam g z.1 z.2) := by
  let a (m : AdelicGroupPoints F M') := map F P G p (mP m)
  let b (m : AdelicGroupPoints F M') := parameterPower F P (-halfModulusParameter F P) (mP m)
  let f (z : AdelicGroupPoints F M' × Vₐ) :=
    (b z.1 * φ (a z.1 * varg(z.2, g))) * hK.heightPower lam (varg(z.2, g))
  have ha : Continuous a := (map F P G p).continuous.comp
    ((map F M P l).continuous.comp (map F M' M c).continuous)
  have hb : Continuous b := (continuous_parameterPower_of_pairing _).comp
    ((map F M P l).continuous.comp (map F M' M c).continuous)
  have harg : Continuous (fun z : AdelicGroupPoints F M' × Vₐ => varg(z.2, g)) :=
    (continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_const
  have hf : Continuous f := ((hb.comp continuous_fst).mul
    (hφc.comp ((ha.comp continuous_fst).mul harg))).mul ((hK.continuous_heightPower lam).comp harg)
  have hq : IsOpenQuotientMap (Prod.map (id : AdelicGroupPoints F M' → AdelicGroupPoints F M')
      (LeftCosetSpace.mk Γ)) :=
    IsOpenQuotientMap.prodMap IsOpenQuotientMap.id (LeftCosetSpace.isOpenQuotientMap_mk Γ)
  apply hq.isQuotientMap.continuous_iff.mpr
  convert hf using 1
  funext z
  let x : Vₐ := (LeftCosetSpace.mk Γ z.2).out
  change f (z.1, x) = f z
  have hx : x * z.2⁻¹ ∈ Γ :=
    (LeftCosetSpace.mk_eq_mk_iff Γ z.2 x).mp (LeftCosetSpace.mk_out Γ _).symm
  have hu := ((mem_intertwiningRationalSubgroup_iff F p iU (iV ≫ q) wA _).mp hx).2
  let u := wA⁻¹ * (x.val * z.2.val⁻¹) * wA
  change u ∈ parabolicUnipotentImage F p iU at hu
  have huv : varg(x, g) = u * varg(z.2, g) := by dsimp only [u]; group
  have hu' : a z.1 * u * (a z.1)⁻¹ ∈ parabolicUnipotentImage F p iU :=
    conj_mem_adelicPoints_range p iU hU.1.isNormal (mP z.1) hu
  obtain ⟨u₀, hu₀⟩ := hu
  have hφeq : φ (a z.1 * varg(x, g)) = φ (a z.1 * varg(z.2, g)) := by
    rw [huv, show a z.1 * (u * varg(z.2, g)) =
      (a z.1 * u * (a z.1)⁻¹) * (a z.1 * varg(z.2, g)) by group, hφ _ hu']
  have hht : hK.heightPower lam (varg(x, g)) = hK.heightPower lam (varg(z.2, g)) := by
    rw [huv, ← hu₀]
    exact hK.heightPower_unipotent_mul hU.1.isUnipotent iU lam u₀ _
  dsimp only [f]
  rw [hφeq, hht]

variable (hw : IsWeylConjugation p l q l' w c) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
  (hi : IsClosedSubgroup (iU ≫ p))

include hw hV hU hi hφc hφ in
/-- A formula for the absolute integral of a normalized Levi slice. -/
theorem IsIwasawaCompact.lintegral_enorm_intertwiningLeviKernel
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) (m : AdelicGroupPoints F M')
    (hHaar : intertwiningLeviHaarFactor iU iV hw hU.1.isNormal hV.1.isNormal hi hV.1.isUnipotent m *
      parameterPower F P (halfModulusParameter F P) (mP m) =
      parameterPower F Q (halfModulusParameter F Q) (mQ m)) :
    (∫⁻ x, ‖hK.intertwiningLeviKernel iU iV w l c φ lam g m x‖ₑ ∂μ) =
      ‖parameterPower F P (-lam) (mP m) *
        parameterPower F Q (-halfModulusParameter F Q) (mQ m)‖ₑ *
      (∫⁻ x, ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam
        (map F Q G q (mQ m) * g) x‖ₑ ∂μ) := by
  let a := map F Q G q (mQ m)
  let α := EisensteinConstantTerm.conjAdelic q iV hV.1.isNormal (mQ m)
  let H := intertwiningAdelicStabilizer p iU (iV ≫ q) w
  let hα := conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hU.1.isNormal hV.1.isNormal m
  let : LocallyCompactSpace Vₐ := (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).locallyCompactSpace
  let : LocallyCompactSpace H := (intertwiningStabilizer p iU (iV ≫ q) w
    (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) hi hV.1.isUnipotent).1.locallyCompactSpace
  let b := mulEquivHaarChar α
  let d := mulEquivHaarChar (subgroupAutomorphism H α hα)
  let mov (x : LeftCosetSpace Γ) := hK.parameterTwist φ lam (wA⁻¹ * a * (x.out : Vₐ).val * g)
  have hchg := (intertwiningIntegralConjugation p iU (iV ≫ q) w hi hV.1.smooth hV.1.connectedSpace
    hV.1.isUnipotent a α hα (fun _ => rfl) K hK φ hφc hφ hU.1.isUnipotent lam g).2.2
  change (∫⁻ x, ‖mov x‖ₑ ∂μ) = ((d / b : ℝ≥0) : ℝ≥0∞) *
    (∫⁻ x, ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam (a * g) x‖ₑ ∂μ) at hchg
  have hcancel (S : GroupScheme (Spec (CommRingCat.of F)))
      (s : ComplexCharacterParameter F S) (m₀ : AdelicGroupPoints F S) :
      parameterPower F S s m₀ * parameterPower F S (-s) m₀ = 1 := by
    simp only [parameterPower, map_neg, LinearMap.neg_apply, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero]
  let tP := parameterPower F P (halfModulusParameter F P) (mP m)
  let tP' := parameterPower F P (-halfModulusParameter F P) (mP m)
  let tQ := parameterPower F Q (halfModulusParameter F Q) (mQ m)
  let tQ' := parameterPower F Q (-halfModulusParameter F Q) (mQ m)
  let t := parameterPower F P (-lam) (mP m)
  have hbd : (((d / b : ℝ≥0) : ℝ) : ℂ) * (((b / d : ℝ≥0) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← NNReal.coe_mul]
    have hd : d ≠ 0 := (mulEquivHaarChar_pos _).ne'
    have hb : b ≠ 0 := (mulEquivHaarChar_pos _).ne'
    rw [div_mul_div_comm, mul_comm d b, div_self (mul_ne_zero hb hd)]
    simp
  change (((b / d : ℝ≥0) : ℝ) : ℂ) * tP = tQ at hHaar
  have horig : (‖(((d / b : ℝ≥0) : ℝ) : ℂ)‖ₑ : ℝ≥0∞) = ((d / b : ℝ≥0) : ℝ≥0∞) := by
    simp [enorm_eq_nnnorm]
  have hPinv : tP * tP' = 1 := hcancel P _ _
  have hQinv : tQ * tQ' = 1 := hcancel Q _ _
  have hsc : (((d / b : ℝ≥0) : ℝ) : ℂ) = tP * tQ' := by
    calc
      _ = (((d / b : ℝ≥0) : ℝ) : ℂ) * tQ * tQ' := by rw [mul_assoc, hQinv, mul_one]
      _ = tP * tQ' := by rw [← hHaar, ← mul_assoc _ _ tP, hbd, one_mul]
  have hn (x : LeftCosetSpace Γ) : hK.intertwiningLeviKernel iU iV w l c φ lam g m x =
      (tP' * t) * mov x := by
    have hy : wA⁻¹ * a * (x.out : Vₐ).val * g = map F P G p (mP m) * varg(x.out, g) := by
      rw [hw.adelic_comp_eq m]
      change wA⁻¹ * a * (x.out : Vₐ).val * g = (wA⁻¹ * a * wA) * varg(x.out, g)
      group
    dsimp only [mov, IsIwasawaCompact.intertwiningLeviKernel]
    rw [hy, IsIwasawaCompact.parameterTwist, hK.heightPower_map_mul]
    have ht : t * parameterPower F P lam (mP m) = 1 := by rw [mul_comm]; exact hcancel P _ _
    generalize φ (map F P G p (mP m) * varg(x.out, g)) = z₁
    generalize hK.heightPower lam (varg(x.out, g)) = z₂
    calc
      _ = (tP' * z₁) * z₂ := rfl
      _ = (tP' * z₁) * z₂ * (t * parameterPower F P lam (mP m)) := by rw [ht, mul_one]
      _ = _ := by ring
  calc
    _ = ‖tP' * t‖ₑ * ∫⁻ x, ‖mov x‖ₑ ∂μ := by
      simp_rw [hn, enorm_mul]
      exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)
    _ = _ := by
      rw [hchg, ← horig, ← mul_assoc, ← enorm_mul, hsc]
      congr 2
      calc
        _ = (tP * tP') * (t * tQ') := by ring
        _ = t * tQ' := by rw [hPinv, one_mul]

/-- Suppose the inducing function is continuous and left invariant under the source adelic
unipotent radical. The normalized Haar identity and a locally uniform integrable majorant
for the ordinary integrand give product integrability of the normalized Levi kernel
against continuous compactly supported tests. The test space has its Borel measurable
structure and a locally finite measure, and it maps continuously into the target Levi. -/
def IsIwasawaCompact.IntertwiningLeviKernelCompactTestsStatement
    (hw : IsWeylConjugation p l q l' w c) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hi : IsClosedSubgroup (iU ≫ p))
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P) : Prop :=
  Continuous φ → IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ →
    (∀ m, intertwiningLeviHaarFactor iU iV hw hU.1.isNormal hV.1.isNormal hi hV.1.isUnipotent m *
      parameterPower F P (halfModulusParameter F P) (mP m) =
      parameterPower F Q (halfModulusParameter F Q) (mQ m)) →
    (∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ b : LeftCosetSpace Γ → ℝ, Integrable b μ ∧
        ∀ x g, g ∈ C → ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g x‖ ≤ b x) →
    ∀ (L : Type v) [TopologicalSpace L] [MeasurableSpace L] [BorelSpace L]
      (ν : Measure L) [IsLocallyFiniteMeasure ν]
      (j : L → AdelicGroupPoints F M'), Continuous j →
      ∀ (g : AdelicGroupPoints F G) (ψ : L → ℂ), Continuous ψ → HasCompactSupport ψ →
        Integrable (fun z : L × LeftCosetSpace Γ =>
          hK.intertwiningLeviKernel iU iV w l c φ lam g (j z.1) z.2 * ψ z.1) (ν.prod μ)

theorem IsIwasawaCompact.intertwiningLeviKernelCompactTests
    (lam : ComplexCharacterParameter F P) :
    hK.IntertwiningLeviKernelCompactTestsStatement.{u, v} iU iV w hw hU hV hi φ lam := by
  intro hφc hφ hHaar hmajor L _ _ _ ν _ j hj g ψ hψ hψc
  let Vclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  let : PolishSpace Vₐ := Vclosed.polishSpace
  have hΓ := isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) wA
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ hΓ
  let : SecondCountableTopology (LeftCosetSpace Γ) :=
    (LeftCosetSpace.isOpenQuotientMap_mk Γ).secondCountableTopology
  let : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_intertwiningMeasure p iU (iV ≫ q) w
    hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent
  let : SFinite μ := inferInstanceAs (SFinite μ)
  let a (x : L) := map F Q G q (mQ (j x)) * g
  have ha : Continuous a :=
    ((map F Q G q).continuous.comp ((map F M' Q l').continuous.comp hj)).mul continuous_const
  obtain ⟨b, hb, hbound⟩ := hmajor (a '' tsupport ψ) (hψc.image ha)
  let scale (x : L) := parameterPower F P (-lam) (mP (j x)) *
    parameterPower F Q (-halfModulusParameter F Q) (mQ (j x))
  have hs : Continuous scale := ((continuous_parameterPower_of_pairing _).comp
    ((map F M P l).continuous.comp ((map F M' M c).continuous.comp hj))).mul
    ((continuous_parameterPower_of_pairing _).comp ((map F M' Q l').continuous.comp hj))
  have htest : HasCompactSupport (fun x => scale x * ψ x) :=
    hψc.of_isClosed_subset isClosed_closure (closure_mono fun x hx => by
      contrapose! hx
      simp [Function.notMem_support.mp hx])
  have hint : Integrable (fun x => scale x * ψ x) ν :=
    (hs.mul hψ).integrable_of_hasCompactSupport htest
  let f (z : L × LeftCosetSpace Γ) := hK.intertwiningLeviKernel iU iV w l c φ lam g (j z.1) z.2 * ψ z.1
  have hf : Continuous f := ((hK.continuous_intertwiningLeviKernel iU iV w hφc hφ hU lam g).comp
    ((hj.comp continuous_fst).prodMk continuous_snd)).mul (hψ.comp continuous_fst)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  change (∫⁻ z, ‖f z‖ₑ ∂(ν.prod μ)) < ∞
  rw [lintegral_prod _ hf.measurable.enorm.aemeasurable]
  calc
    _ ≤ ∫⁻ x, ‖scale x * ψ x‖ₑ * (∫⁻ y, ‖b y‖ₑ ∂μ) ∂ν := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ tsupport ψ
      · have hslice := hK.lintegral_enorm_intertwiningLeviKernel iU iV w hφc hφ hU hw hV hi
          lam g (j x) (hHaar (j x))
        dsimp only [f]
        simp only [enorm_mul]
        rw [lintegral_mul_const' _ _ enorm_ne_top, hslice]
        change (‖scale x‖ₑ * (∫⁻ y, ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam (a x) y‖ₑ ∂μ)) *
          ‖ψ x‖ₑ ≤ _
        rw [mul_right_comm]
        refine mul_le_mul_right ?_ _
        refine lintegral_mono fun y => ?_
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((hbound y (a x) ⟨x, hx, rfl⟩).trans (le_abs_self _))
      · have hzero : ψ x = 0 := Function.notMem_support.mp (fun hx' => hx (subset_tsupport _ hx'))
        simp [f, hzero]
    _ < ∞ := by
      rw [lintegral_mul_const' _ _ hb.hasFiniteIntegral.ne]
      exact ENNReal.mul_lt_top hint.hasFiniteIntegral hb.hasFiniteIntegral

end Langlands.Global.AdelicGroupPoints
