import Langlands.Global.AdelicAdjunctionKernel

/-! # Refolding the common quotient to an induced pairing -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open InducedInnerProductIntegrable ParabolicIwasawaMeasure LeftCosetSpace

variable {F : Type} [Field F] [NumberField F]
  {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine U.X.left]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine V.X.left]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] [IsIso (subgroupMultiplication l iU)]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
  [IsClosedImmersion (iV ≫ q).hom.hom.left] [IsIso (subgroupMultiplication l' iV)]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
  {c : M' ⟶ M} (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (hw : IsWeylConjugation p l q l' w c)
  (φ ψ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
  (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
  (hψ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F q iV l') ψ)

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "wA" => (innerAdelicPoint F G w)
local notation "Γ" => (adjunctionRationalSubgroup (p := p) (q := q) wA)
local notation "Vₐ" => (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))
local notation "Δ" => (intertwiningRationalSubgroup F p iU (iV ≫ q) wA)
local notation "B" => (adjunctionKernel l hK hK' c π' w φ ψ lam)
local notation "mQ" => (fun m => map F Q G q (map F M' Q l' m))
local notation "op" => (hK.intertwiningOperator hK' iU l iV c π' w φ lam)

include hU hV in
/-- A common principal element lies in both inducing subgroups in the respective coordinates. -/
theorem adjunctionRationalSubgroup_leviRadical {d : Gₐ} (hd : d ∈ Γ) :
    d ∈ parabolicQuotientSubgroup F q iV l' ∧ wA⁻¹ * d * wA ∈ parabolicQuotientSubgroup F p iU l := by
  obtain ⟨hR, hQ, hP⟩ := (mem_adjunctionRationalSubgroup_iff wA d).1 hd
  have hwR : wA ∈ rationalSubgroup F G := ⟨_, (innerAdelicPoint_eq_rational F G w).symm⟩
  exact ⟨mem_parabolicQuotientSubgroup_of_rational_range iV l' hV hR hQ,
    mem_parabolicQuotientSubgroup_of_rational_range iU l hU
      (mul_mem (mul_mem (inv_mem hwR) hR) hwR) hP⟩

/-- Coordinates of the Iwasawa height in the basis used for an induced pairing. -/
def IsIwasawaCompact.heightCoordinates {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (g : Gₐ) : Fin n → ℝ :=
  parameterCoordinates F P e (hK.height g)

theorem IsIwasawaCompact.continuous_heightCoordinates {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) : Continuous (hK.heightCoordinates e) :=
  (continuous_parameterCoordinates e).comp hK.continuous_height

theorem IsIwasawaCompact.heightCoordinates_map_mul {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (x : AdelicGroupPoints F P) (g : Gₐ) :
    hK.heightCoordinates e (map F P G p x * g) =
      parameterCoordinates F P e (characterLog F P x) + hK.heightCoordinates e g := by
  unfold IsIwasawaCompact.heightCoordinates
  rw [hK.height_map_mul]
  funext j
  exact map_add (realParameterPairing F P (e (Pi.single j 1))) _ _

include hU hV hφ hψ in
/-- A weighted twisted product descends to the discrete common quotient. -/
theorem adjunctionKernel_weight_invariant (b : Gₐ → ℝ)
    (hb : ∀ d ∈ Γ, ∀ g, b (d * g) = b g) : ∀ d ∈ Γ, ∀ g,
    (b (d * g) : ℂ) * B (d * g) = (b g : ℂ) * B g := by
  intro d hd g
  obtain ⟨hQ, hP⟩ := adjunctionRationalSubgroup_leviRadical iU l iV l' w hU hV hd
  rw [hb _ hd, adjunctionKernel_leftInvariant iU l iV l' hK hK' c π' w φ ψ lam
    hU.1.isUnipotent hV.1.isUnipotent hφ hψ hQ hP]

include hU hV hψ in
private theorem integral_unfoldedKernel_eq {n : ℕ}
    (e' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F Q) (β' : (Fin n → ℝ) → ℝ)
    (k : K) (m : AdelicGroupPoints F M') :
    (∫ v : LeftCosetSpace Δ, unfoldedIntegrand (K := K) q iV l' Δ
      (fun g => (β' (hK'.heightCoordinates e' g) : ℂ) * B g) ((v, m), k)
        ∂intertwiningMeasure F p iU (iV ≫ q) wA) =
      (β' (parameterCoordinates F Q e' (characterLog F Q (map F M' Q l' m))) : ℂ) *
        parameterPower F Q (-modulusParameter F Q) (map F M' Q l' m) *
        op (mQ m * k.val) * (starRingEnd ℂ) (ψ (mQ m * k.val)) := by
  let g := mQ m * k.val
  let y := parameterCoordinates F Q e' (characterLog F Q (map F M' Q l' m))
  let δ := parameterPower F Q (-modulusParameter F Q) (map F M' Q l' m)
  let a := hK'.heightPower (-weylParameter l c π' lam) g
  let f := hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g
  have hEq (v : LeftCosetSpace Δ) : unfoldedIntegrand (K := K) q iV l' Δ
      (fun g => (β' (hK'.heightCoordinates e' g) : ℂ) * B g) ((v, m), k) =
        (((β' y : ℂ) * δ) * a * (starRingEnd ℂ) (ψ g)) * f v := by
    let u : Vₐ := v.out
    have hu : u.val ∈ parabolicQuotientSubgroup F q iV l' := Subgroup.mem_sup_left u.property
    change (inverseModulus l' m : ℂ) * ((β' (hK'.heightCoordinates e' (u.val * mQ m * k.val)) : ℂ) *
      B (u.val * mQ m * k.val)) = _
    rw [ofReal_inverseModulus, mul_assoc u.val, show mQ m * k.val = g from rfl]
    unfold adjunctionKernel IsIwasawaCompact.heightCoordinates IsIwasawaCompact.heightPower
    rw [hK'.height_leftInvariant_parabolic iV l' hV.1.isUnipotent _ hu, hψ _ hu]
    have hheight : hK'.height g = characterLog F Q (map F M' Q l' m) := hK'.height_eq k.property rfl
    rw [hheight]
    have ha : a = Complex.exp (complexParameterPairing F Q (-weylParameter l c π' lam)
        (characterLog F Q (map F M' Q l' m))) := by
      dsimp only [a, IsIwasawaCompact.heightPower]
      rw [hheight]
    rw [← ha]
    change δ * ((β' y : ℂ) * (hK.parameterTwist φ lam (wA⁻¹ * (u.val * g)) * a * _)) = _
    rw [← mul_assoc wA⁻¹ u.val g]
    change δ * ((β' y : ℂ) * (f v * a * _)) = _
    ring
  simp_rw [hEq, integral_const_mul]
  change ((β' y : ℂ) * δ * a * (starRingEnd ℂ) (ψ g)) *
      (∫ v, f v ∂intertwiningMeasure F p iU (iV ≫ q) wA) = _
  unfold IsIwasawaCompact.intertwiningOperator IsIwasawaCompact.intertwiningIntegral
  change _ = (β' y : ℂ) * δ * (a * (∫ v, f v ∂intertwiningMeasure F p iU (iV ≫ q) wA)) * _
  ring

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

include r hw hU hV hφ hψ in
set_option maxHeartbeats 1300000 in
/-- Refolding the weighted common-quotient integral gives the actual induced pairing and
integrability of its pairing integrand. -/
theorem refoldAdjunctionKernel (hG : IsConnectedReductive G) (hq : IsParabolicSubgroup q)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure]
    (hμM' : IsIwasawaCompatibleMeasure K hK'.isCompact q iV l' μM') {n : ℕ}
    (e' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F Q) (β' : (Fin n → ℝ) → ℝ) (hβ' : Continuous β') :
    let f := fun g => (β' (hK'.heightCoordinates e' g) : ℂ) * B g
    let hΓ : IsDiscrete (Γ : Set Gₐ) := (isDiscrete_rationalSubgroup F G).mono inf_le_left
    let μΓ := discreteQuotientMeasure Γ hΓ Measure.haar
    Integrable (fun z : LeftCosetSpace Γ => f z.out) μΓ →
      Integrable (inducedInnerProductIntegrand K q l' e' β' op ψ)
        ((compactHaarProbability F G K hK'.isCompact).prod
          (discreteQuotientMeasure (rationalSubgroup F M') (isDiscrete_rationalSubgroup F M') μM')) ∧
      inducedInnerProduct K hK'.isCompact q l' μM' e' β' op ψ =
        ∫ z : LeftCosetSpace Γ, f z.out ∂μΓ := by
  intro f hΓ μΓ hI
  let hΔ := isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) wA
  let μV := intertwiningMeasure F p iU (iV ≫ q) wA
  let μK := compactHaarProbability F G K hK'.isCompact
  let : IsClosed (Vₐ : Set Gₐ) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  let : LocallyCompactSpace Vₐ := (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).locallyCompactSpace
  have hΔeq := mem_intertwiningRationalSubgroup_iff_adjunction iU l iV l' r w hw hG hU hq hV inferInstance
  have hfc : Continuous f := ((Complex.continuous_ofReal.comp hβ').comp
    (hK'.continuous_heightCoordinates e')).mul
      (continuous_adjunctionKernel l hK hK' c π' w φ ψ lam hφc hψc)
  have hfInv : ∀ d ∈ Γ, ∀ g, f (d * g) = f g :=
    adjunctionKernel_weight_invariant iU l iV l' hK hK' (c := c) π' w φ ψ lam hU hV hφ hψ
      (fun g => β' (hK'.heightCoordinates e' g)) (by
      intro d hd g
      obtain ⟨hQ, _⟩ := adjunctionRationalSubgroup_leviRadical iU l iV l' w hU hV hd
      dsimp only [IsIwasawaCompact.heightCoordinates]
      rw [hK'.height_leftInvariant_parabolic iV l' hV.1.isUnipotent _ hQ])
  have hu := unfoldDiscreteIwasawa q iV l' hV hK'.isCompact μM' hμM' Γ inf_le_left
    (inf_le_right.trans inf_le_left) (map_levi_mem_adjunctionRationalSubgroup l l' w hw)
    Δ hΔ hΔeq f hfc hfInv
  let H := unfoldedIntegrand (K := K) q iV l' Δ f
  have hHm : Measurable H := measurable_unfoldedIntegrand q iV l' Δ hΔ f hfc.measurable
    (fun u hu g => hfInv u.val ((hΔeq u).1 hu) g)
  let : SFinite μV := inferInstanceAs (SFinite (Measure.map _ ((AdelicSubgroupPoints.quotientMassNormalizer
    F G (SubgroupFunctor.range (iV ≫ q)) • (Measure.haar : Measure Vₐ)).restrict _)))
  have hA := integral_unfoldedKernel_eq iU l iV l' hK hK' (c := c) π' w φ ψ lam hU hV hψ e' β'
  have hleft := hK.intertwiningOperator_leftInvariant iU iV π' hK' hU hV hφ lam hw
    r.isCompatible.levi
  have hInvA (k : K) (d : AdelicGroupPoints F M') (hd : d ∈ rationalSubgroup F M')
      (m : AdelicGroupPoints F M') : (∫ v, H ((v, d * m), k) ∂μV) = ∫ v, H ((v, m), k) ∂μV := by
    change (∫ v, unfoldedIntegrand (K := K) q iV l' Δ f ((v, d * m), k) ∂μV) =
      ∫ v, unfoldedIntegrand (K := K) q iV l' Δ f ((v, m), k) ∂μV
    rw [hA, hA, characterLog_map_mul_left l' (rationalSubgroup_le_normOneSubgroup F M' hd),
      parameterPower_map_mul_left _ l' (rationalSubgroup_le_normOneSubgroup F M' hd),
      form_rational_mul hleft hd, form_rational_mul hψ hd]
  obtain ⟨hInt, hEq⟩ := refold_discrete_fibre (rationalSubgroup F M')
    (isDiscrete_rationalSubgroup F M') μV μM' μK H hHm (hu.1.mp hI) hInvA
  let W := inducedInnerProductIntegrand K q l' e' β' op ψ
  have hW (z : K × RationalQuotient F M') : (∫ v, H ((v, z.2.out), z.1) ∂μV) = W z :=
    hA z.1 z.2.out
  have hWI : Integrable W (μK.prod (discreteQuotientMeasure (rationalSubgroup F M')
      (isDiscrete_rationalSubgroup F M') μM')) := hInt.congr (Filter.Eventually.of_forall hW)
  refine ⟨hWI, ?_⟩
  rw [Langlands.Global.inducedInnerProduct_eq_integral_prod _ _ _ _ _ _ _ hWI]
  exact (integral_congr_ae (Filter.Eventually.of_forall fun z => (hW z).symm)).trans
    (hEq.trans hu.2.symm)

end Langlands.Global.AdelicGroupPoints
