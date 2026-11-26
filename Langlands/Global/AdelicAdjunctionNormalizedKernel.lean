import Langlands.Global.AdelicAdjunctionRefold
import Langlands.Global.AdelicIntertwiningLeviHaarBalance
import Langlands.Global.AdelicIntertwiningLeviQuotient

/-! # Normalized Levi coordinates on the adjunction kernel -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj TensorProduct ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration EisensteinConstantTerm InducedInnerProductIntegrable
open ParabolicIwasawaMeasure LeftCosetSpace

variable {F : Type} [Field F] [NumberField F]
  {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine U.X.left]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine V.X.left]
  [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
  [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
  {c : M' ⟶ M} (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (hw : IsWeylConjugation p l q l' w c)
  (φ ψ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "Mₐ'" => (AdelicGroupPoints F M')
local notation "wA" => (innerAdelicPoint F G w)
local notation "Vₐ" => (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))
local notation "Δ" => (intertwiningRationalSubgroup F p iU (iV ≫ q) wA)
local notation "μV" => (intertwiningMeasure F p iU (iV ≫ q) wA)
local notation "mP" => (fun m => map F M P l (map F M' M c m))
local notation "mQ" => (map F M' Q l')
local notation "gP" => (fun m => map F P G p (mP m))
local notation "gQ" => (fun m => map F Q G q (mQ m))
local notation "xV" => (fun (v : Vₐ) => wA⁻¹ * Subtype.val v)
local notation "B" => (adjunctionKernel l hK hK' c π' w φ ψ lam)
set_option quotPrecheck false in
local notation "C" => (intertwiningLeviHaarFactor iU iV hw hU.1.isNormal hV.1.isNormal
  (inferInstance : IsClosedImmersion (iU ≫ p).hom.hom.left) hV.1.isUnipotent)

/-- After moving the Levi variable past the radical, the product uses the normalized
restrictions of both inducing forms. -/
def normalizedAdjunctionKernel (c : M' ⟶ M) (v : Vₐ) (m : Mₐ') (k : K) : ℂ :=
  hK.heightPower lam (xV v) * normalizedLeviValue p l φ (map F M' M c m) (xV v * k.val) *
    (starRingEnd ℂ) (normalizedLeviValue q l' ψ m k.val)

private theorem star_parameterPower_neg_half (S : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine S.X.left] [LocallyOfFiniteType S.X.hom] (x : AdelicGroupPoints F S) :
    (starRingEnd ℂ) (parameterPower F S (-halfModulusParameter F S) x) =
      parameterPower F S (-halfModulusParameter F S) x := by
  unfold parameterPower halfModulusParameter
  rw [map_neg, LinearMap.neg_apply, complexParameterPairing_tmul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]

private theorem negHalf_add_negHalf (S : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine S.X.left] [LocallyOfFiniteType S.X.hom] :
    -halfModulusParameter F S + -halfModulusParameter F S = -modulusParameter F S := by
  have h := neg_modulus_add_half_add_half (F := F) (P := S)
  calc
    _ = (-modulusParameter F S + halfModulusParameter F S + halfModulusParameter F S) +
        (-halfModulusParameter F S + -halfModulusParameter F S) := by rw [h, zero_add]
    _ = _ := by abel

include hw hU hV in
/-- The Haar factor times the target Iwasawa density gives the two inverse half moduli. -/
private theorem balance_inverse (m : Mₐ')
    (hbal : C m * parameterPower F P (halfModulusParameter F P) (mP m) =
      parameterPower F Q (halfModulusParameter F Q) (mQ m)) :
    (inverseModulus l' m : ℂ) * C m =
        parameterPower F P (-halfModulusParameter F P) (mP m) *
          parameterPower F Q (-halfModulusParameter F Q) (mQ m) := by
  rw [ofReal_inverseModulus, ← negHalf_add_negHalf Q, parameterPower_add]
  have hcancel (S : GroupScheme (Spec (CommRingCat.of F))) [IsAffine S.X.left]
      [LocallyOfFiniteType S.X.hom] (x : AdelicGroupPoints F S) :
      parameterPower F S (halfModulusParameter F S) x *
        parameterPower F S (-halfModulusParameter F S) x = 1 := by
    rw [← parameterPower_add, add_neg_cancel, parameterPower_zero]
  calc
    _ = (parameterPower F Q (-halfModulusParameter F Q) (mQ m) *
      (C m * (parameterPower F P (halfModulusParameter F P) (mP m) *
        parameterPower F P (-halfModulusParameter F P) (mP m)))) *
        parameterPower F Q (-halfModulusParameter F Q) (mQ m) := by
      rw [hcancel, mul_one]
      ring
    _ = _ := by
      rw [← mul_assoc (C m), hbal]
      calc
        _ = (parameterPower F Q (halfModulusParameter F Q) (mQ m) *
          parameterPower F Q (-halfModulusParameter F Q) (mQ m)) *
          (parameterPower F P (-halfModulusParameter F P) (mP m) *
            parameterPower F Q (-halfModulusParameter F Q) (mQ m)) := by ring
        _ = _ := by rw [hcancel, one_mul]

include hw hU hV in
set_option maxHeartbeats 800000 in
private theorem normalizedAdjunctionKernel_eq (hπ' : l' ≫ π' = 𝟙 M')
    (m : Mₐ') (v : Vₐ) (k : K)
    (hbal : C m * parameterPower F P (halfModulusParameter F P) (mP m) =
      parameterPower F Q (halfModulusParameter F Q) (mQ m)) :
    (inverseModulus l' m : ℂ) * C m *
      hK'.heightPower (-weylParameter l c π' lam) (gQ m * k.val) *
      (starRingEnd ℂ) (ψ (gQ m * k.val)) *
      hK.parameterTwist φ lam (wA⁻¹ * gQ m * v.val * k.val) =
        normalizedAdjunctionKernel l iV l' hK w φ ψ lam c v m k := by
  have hg : wA⁻¹ * gQ m * v.val * k.val = gP m * (xV v * k.val) := by
    dsimp only
    rw [hw.adelic_comp_eq m]
    group
  have hpower : hK'.heightPower (-weylParameter l c π' lam) (gQ m * k.val) =
      parameterPower F P (-lam) (mP m) := by
    unfold IsIwasawaCompact.heightPower
    rw [hK'.height_eq k.property rfl]
    change parameterPower F Q (-weylParameter l c π' lam) (mQ m) = _
    rw [← map_neg, weylParameter_power]
    congr 1
    simp only [← map_comp_apply_of_hom, ← Category.assoc l' π', hπ', Category.id_comp]
  have hright : hK.heightPower lam (xV v * k.val) = hK.heightPower lam (xV v) := by
    unfold IsIwasawaCompact.heightPower
    rw [hK.height_mul_right _ k.property]
  have hcancel : parameterPower F P (-lam) (mP m) * parameterPower F P lam (mP m) = 1 := by
    rw [← parameterPower_add, neg_add_cancel, parameterPower_zero]
  rw [balance_inverse iU l iV l' w hw hU hV m hbal, hpower, hg, IsIwasawaCompact.parameterTwist,
    hK.heightPower_map_mul, hright]
  unfold normalizedAdjunctionKernel normalizedLeviValue
  simp only [map_mul, star_parameterPower_neg_half]
  calc
    _ = (parameterPower F P (-lam) (mP m) * parameterPower F P lam (mP m)) *
        (hK.heightPower lam (xV v) *
          (parameterPower F P (-halfModulusParameter F P) (mP m) * φ (gP m * (xV v * k.val))) *
          (parameterPower F Q (-halfModulusParameter F Q) (mQ m) *
            (starRingEnd ℂ) (ψ (gQ m * k.val)))) := by ring
    _ = _ := by rw [hcancel, one_mul]

include hw hU hV in
set_option maxHeartbeats 1300000 in
/-- Moving the Levi point preserves the absolute and complex fibre integrals after inserting
its Haar scale. The two weight factors may depend on the source argument and the target Levi. -/
theorem normalizedAdjunction_fibres (hπ' : l' ≫ π' = 𝟙 M') (hφc : Continuous φ)
    (hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (b : Gₐ → ℝ) (hb : Continuous b)
    (hbInv : ∀ d ∈ parabolicUnipotentImage F p iU, ∀ g, b (d * g) = b g)
    (a : Mₐ' → ℝ) (f : Gₐ → ℂ)
    (hψU : IsLeftInvariantUnder F G (parabolicUnipotentImage F q iV) ψ)
    (hf : ∀ (m : Mₐ') (v : Vₐ) (k : K), f (v.val * gQ m * k.val) =
      (a m : ℂ) * (b (wA⁻¹ * (v.val * gQ m * k.val)) : ℂ) * B (v.val * gQ m * k.val))
    (m : Mₐ') (k : K)
    (hbal : C m * parameterPower F P (halfModulusParameter F P) (mP m) =
      parameterPower F Q (halfModulusParameter F Q) (mQ m)) :
    let lhs := fun v : LeftCosetSpace Δ => unfoldedIntegrand (K := K) q iV l' Δ f ((v, m), k)
    let rhs := fun v : LeftCosetSpace Δ =>
      (a m : ℂ) * (b (gP m * (xV (v.out : Vₐ) * k.val)) : ℂ) *
        normalizedAdjunctionKernel l iV l' hK w φ ψ lam c v.out m k
    (∫⁻ v, ‖lhs v‖ₑ ∂μV) = (∫⁻ v, ‖rhs v‖ₑ ∂μV) ∧
      (∫ v, lhs v ∂μV) = ∫ v, rhs v ∂μV := by
  intro lhs rhs
  let A := (inverseModulus l' m : ℂ) * (a m : ℂ) *
    hK'.heightPower (-weylParameter l c π' lam) (gQ m * k.val) * (starRingEnd ℂ) (ψ (gQ m * k.val))
  let φb : Gₐ → ℂ := fun g => (b g : ℂ) * φ g
  have hφbc : Continuous φb := (Complex.continuous_ofReal.comp hb).mul hφc
  have hφbi : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φb := by
    intro d hd g
    change (b (d * g) : ℂ) * φ (d * g) = _
    rw [hbInv _ hd, hφU _ hd]
  let α := conjAdelic q iV hV.1.isNormal (mQ m)
  let hα := conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hU.1.isNormal hV.1.isNormal m
  let L := hK.intertwiningIntegrand iU (iV ≫ q) w φb lam (gQ m * k.val)
  let R := fun v : LeftCosetSpace Δ => hK.parameterTwist φb lam (wA⁻¹ * gQ m * (v.out : Vₐ).val * k.val)
  have hSub := intertwiningIntegralConjugation p iU (iV ≫ q) w
    (inferInstance : IsClosedImmersion (iU ≫ p).hom.hom.left) hV.1.smooth hV.1.connectedSpace
    hV.1.isUnipotent (gQ m) α hα (fun _ => rfl) K hK φb hφbc hφbi hU.1.isUnipotent lam k.val
  have hL (v : LeftCosetSpace Δ) : lhs v = A * L v := by
    change (inverseModulus l' m : ℂ) * f ((v.out : Vₐ).val * gQ m * k.val) = _
    rw [hf]
    unfold adjunctionKernel IsIwasawaCompact.heightPower
    rw [mul_assoc (v.out : Vₐ).val]
    have hv : (v.out : Vₐ).val ∈ parabolicUnipotentImage F q iV := (v.out : Vₐ).property
    rw [hK'.height_leftInvariant_parabolic iV l' hV.1.isUnipotent _ (Subgroup.mem_sup_left hv), hψU _ hv]
    rw [← mul_assoc wA⁻¹ (v.out : Vₐ).val]
    dsimp only [A, L, IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist,
      IsIwasawaCompact.heightPower, φb]
    ring
  have hR (v : LeftCosetSpace Δ) : rhs v = A * C m * R v := by
    let v' : Vₐ := v.out
    have harg : wA⁻¹ * gQ m * v'.val * k.val = gP m * (xV v' * k.val) := by
      dsimp only
      rw [hw.adelic_comp_eq m]
      group
    have hR' : R v = (b (gP m * (xV v' * k.val)) : ℂ) *
        hK.parameterTwist φ lam (wA⁻¹ * gQ m * v'.val * k.val) := by
      change hK.parameterTwist φb lam (wA⁻¹ * gQ m * v'.val * k.val) = _
      rw [← harg]
      unfold IsIwasawaCompact.parameterTwist
      dsimp only [φb]
      rw [mul_assoc]
    rw [hR']
    change (_ : ℂ) * _ * normalizedAdjunctionKernel l iV l' hK w φ ψ lam c v' m k = _
    rw [← normalizedAdjunctionKernel_eq iU l iV l' hK hK' π' w hw φ ψ lam hU hV hπ' m v' k hbal]
    dsimp only [A]
    ring
  have hInt : (∫ v, L v ∂μV) = C m * ∫ v, R v ∂μV := hSub.1
  have hNorm := hSub.2.2
  let H := intertwiningAdelicStabilizer p iU (iV ≫ q) w
  let : LocallyCompactSpace Vₐ := (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).locallyCompactSpace
  let : LocallyCompactSpace H := (intertwiningStabilizer p iU (iV ≫ q) w
    (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left)
    (inferInstance : IsClosedImmersion (iU ≫ p).hom.hom.left) hV.1.isUnipotent).1.locallyCompactSpace
  let x : ℝ≥0 := mulEquivHaarChar α
  let y : ℝ≥0 := mulEquivHaarChar (subgroupAutomorphism H α hα)
  have hx : x ≠ 0 := (mulEquivHaarChar_pos _).ne'
  have hy : y ≠ 0 := (mulEquivHaarChar_pos _).ne'
  have hEn : ‖C m‖ₑ = ((x / y : ℝ≥0) : ℝ≥0∞) := by
    change ‖(((x / y : ℝ≥0) : ℝ) : ℂ)‖ₑ = _
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hNorm' : (∫⁻ v, ‖R v‖ₑ ∂μV) = ((y / x : ℝ≥0) : ℝ≥0∞) * (∫⁻ v, ‖L v‖ₑ ∂μV) := hNorm
  have hcan : ((x / y : ℝ≥0) : ℝ≥0∞) * ((y / x : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_mul, ENNReal.coe_eq_one]
    field_simp
  refine ⟨?_, ?_⟩
  · have hLeft : (∫⁻ v, ‖lhs v‖ₑ ∂μV) = ‖A‖ₑ * (∫⁻ v, ‖L v‖ₑ ∂μV) := by
      simp_rw [hL, enorm_mul, lintegral_const_mul' _ _ enorm_ne_top]
    have hRight : (∫⁻ v, ‖rhs v‖ₑ ∂μV) = (‖A‖ₑ * ‖C m‖ₑ) * (∫⁻ v, ‖R v‖ₑ ∂μV) := by
      simp_rw [hR, enorm_mul]
      exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)
    rw [hLeft, hRight, hEn, hNorm', mul_assoc ‖A‖ₑ, ← mul_assoc (((x / y : ℝ≥0) : ℝ≥0∞)), hcan, one_mul]
  · simp_rw [hL, hR, integral_const_mul, hInt, mul_assoc]

end Langlands.Global.AdelicGroupPoints
