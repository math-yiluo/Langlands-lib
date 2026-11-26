import Langlands.Global.AdelicAdjunctionCutoff
import Langlands.Global.AdelicAdjunctionKernelIntegrable

/-! # The two cutoff integrals on the common quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology TensorProduct
open scoped CategoryTheory.MonObj TensorProduct ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open ParabolicIwasawaMeasure LeftCosetSpace RestrictionSplitCentre
open InducedInnerProductIntegrable InducedInnerProductGram

variable {F : Type} [Field F] [NumberField F]
  {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine U.X.left]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine V.X.left]
  [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] [IsIso (subgroupMultiplication l iU)]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
  [IsClosedImmersion (iV ≫ q).hom.hom.left] [IsIso (subgroupMultiplication l' iV)]
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
  {c : M' ⟶ M} (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (hw : IsWeylConjugation p l q l' w c)
  {φ ψ : AdelicGroupPoints F G → ℂ} (lam : ComplexCharacterParameter F P)
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
  (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
  (hψ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F q iV l') ψ)
  (heφ : IsSplitComponentEquivariant p l φ) (heψ : IsSplitComponentEquivariant q l' ψ)
  {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  (e' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F Q)

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "Mₐ'" => (AdelicGroupPoints F M')
local notation "wA" => (innerAdelicPoint F G w)
local notation "Vₐ" => (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))
local notation "Γ" => (adjunctionRationalSubgroup (p := p) (q := q) wA)
local notation "Δ" => (intertwiningRationalSubgroup F p iU (iV ≫ q) wA)
local notation "Xᵥ" => (LeftCosetSpace Δ)
local notation "μV" => (intertwiningMeasure F p iU (iV ≫ q) wA)
local notation "μK" => (compactHaarProbability F G K (IsIwasawaCompact.isCompact hK'))
local notation "Dm" => (fundamentalDomain (AdelicGroupPoints.rationalSubgroup F M') (isDiscrete_rationalSubgroup F M'))
local notation "mP" => (fun m => map F M P l (map F M' M c m))
local notation "mQ" => (map F M' Q l')
local notation "gP" => (fun m => map F P G p (mP m))
local notation "gQ" => (fun m => map F Q G q (mQ m))
local notation "xV" => (fun (v : Vₐ) => wA⁻¹ * Subtype.val v)
local notation "yQ" => (fun m => parameterCoordinates F Q e' (characterLog F Q (mQ m)))
local notation "B" => (adjunctionKernel l hK hK' c π' w φ ψ lam)
local notation "J₀" => (normalizedAdjunctionKernel l iV l' hK w φ ψ lam c)
local notation "C" => (canonicalRationalSubgroup F M')
set_option quotPrecheck false in
local notation "bal" => (intertwiningLeviHaarFactor iU iV hw hU.1.isNormal hV.1.isNormal
  (inferInstance : IsClosedImmersion (iU ≫ p).hom.hom.left) hV.1.isUnipotent)

private theorem realWeylParameter_pairing (x : RealCharacterParameter F P) (H : RealCharacterDual F Q) :
    realParameterPairing F Q (realWeylParameter l c π' x) H =
      realParameterPairing F P x (realCharacterDualMap F Q P (π' ≫ c ≫ l) H) := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

private theorem equivariant_levi_coordinates (hπ' : l' ≫ π' = 𝟙 M')
    (he : ∀ x, e' x = realWeylParameter l c π' (e x)) (m : Mₐ') :
    parameterCoordinates F P e (characterLog F P (mP m)) = yQ m := by
  funext j
  change realParameterPairing F P (e (Pi.single j 1)) (characterLog F P (mP m)) =
    realParameterPairing F Q (e' (Pi.single j 1)) (characterLog F Q (mQ m))
  rw [he, realWeylParameter_pairing, ← characterLog_map]
  congr 2
  simp only [← map_comp_apply_of_hom, ← Category.assoc l' π', hπ', Category.id_comp]

include hw hφ hψ heφ heψ in
private theorem normalizedAdjunction_canonical_out (v : Vₐ) (m : Mₐ') (k : K) :
    J₀ v (mk C m).out k = J₀ v m k := by
  let : IsIso c := hw.isIso
  apply out_mk_of_invariant C (fun u => J₀ v u k) _ m
  intro d hd u
  have hd' : map F M' M c d ∈ canonicalRationalSubgroup F M :=
    map_mem_canonicalRationalSubgroup (asIso c) hd
  unfold normalizedAdjunctionKernel
  rw [map_mul, normalizedLeviValue_invariant p l hφ heφ _ _ hd',
    normalizedLeviValue_invariant q l' hψ heψ _ _ hd]

include hU hV hφ hψ in
/-- The source cutoff, translated by the inverse Weyl point, descends along with the product. -/
theorem sourceAdjunctionCutoff_invariant (β : (Fin n → ℝ) → ℝ) :
    ∀ d ∈ Γ, ∀ g, (β (hK.heightCoordinates e (wA⁻¹ * (d * g))) : ℂ) * B (d * g) =
      (β (hK.heightCoordinates e (wA⁻¹ * g)) : ℂ) * B g := by
  refine adjunctionKernel_weight_invariant iU l iV l' hK hK' (c := c) π' w φ ψ lam hU hV hφ hψ
    (fun g => β (hK.heightCoordinates e (wA⁻¹ * g))) ?_
  intro d hd g
  have h := (adjunctionRationalSubgroup_leviRadical iU l iV l' w hU hV hd).2
  rw [show wA⁻¹ * (d * g) = (wA⁻¹ * d * wA) * (wA⁻¹ * g) by group]
  unfold IsIwasawaCompact.heightCoordinates
  rw [hK.height_leftInvariant_parabolic iU l hU.1.isUnipotent _ h]

include hU hV hφ hψ in
/-- The target cutoff descends along with the product. -/
theorem targetAdjunctionCutoff_invariant (β' : (Fin n → ℝ) → ℝ) :
    ∀ d ∈ Γ, ∀ g, (β' (hK'.heightCoordinates e' (d * g)) : ℂ) * B (d * g) =
      (β' (hK'.heightCoordinates e' g) : ℂ) * B g := by
  refine adjunctionKernel_weight_invariant iU l iV l' hK hK' (c := c) π' w φ ψ lam hU hV hφ hψ
    (fun g => β' (hK'.heightCoordinates e' g)) ?_
  intro d hd g
  have h := (adjunctionRationalSubgroup_leviRadical iU l iV l' w hU hV hd).1
  unfold IsIwasawaCompact.heightCoordinates
  rw [hK'.height_leftInvariant_parabolic iV l' hV.1.isUnipotent _ h]

include r hw hU hV hφ hψ heφ heψ in
set_option maxHeartbeats 2200000 in
/-- The two cutoff weights give absolutely convergent integrals of the same value on the
common quotient, using the given Iwasawa-compatible measure on the target Levi. -/
theorem integrate_adjunction_cutoffs (hG : IsConnectedReductive G) (hq : IsParabolicSubgroup q)
    (hl' : IsRationalLeviSubgroup l') (hM' : IsConnectedReductive M')
    (hπ' : l' ≫ π' = 𝟙 M') (he : ∀ x, e' x = realWeylParameter l c π' (e x))
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (μM' : Measure Mₐ') [μM'.IsHaarMeasure]
    (hμM' : IsIwasawaCompatibleMeasure K hK'.isCompact q iV l' μM')
    (β β' : (Fin n → ℝ) → ℝ)
    (hβc : Continuous β) (hβs : HasCompactSupport β) (hβ : ∫ u, β u = 1)
    (hβ'c : Continuous β') (hβ's : HasCompactSupport β') (hβ' : ∫ u, β' u = 1)
    (hbal : ∀ m, bal m * parameterPower F P (halfModulusParameter F P) (mP m) =
      parameterPower F Q (halfModulusParameter F Q) (mQ m))
    (hJm : Measurable (fun z : Xᵥ × (K × CanonicalQuotient F M') => J₀ z.1.out z.2.2.out z.2.1))
    (hJi : Integrable (fun z : Xᵥ × (K × CanonicalQuotient F M') => J₀ z.1.out z.2.2.out z.2.1)
      (Measure.prod μV (Measure.prod μK (canonicalMeasure F M')))) :
    let μΓ := discreteQuotientMeasure Γ ((isDiscrete_rationalSubgroup F G).mono inf_le_left) (Measure.haar : Measure Gₐ)
    let f' := fun g => (β' (hK'.heightCoordinates e' g) : ℂ) * B g
    let f := fun g => (β (hK.heightCoordinates e (wA⁻¹ * g)) : ℂ) * B g
    Integrable (fun u : LeftCosetSpace Γ => f' u.out) μΓ ∧
      Integrable (fun u : LeftCosetSpace Γ => f u.out) μΓ ∧
      (∫ u : LeftCosetSpace Γ, f' u.out ∂μΓ) = ∫ u : LeftCosetSpace Γ, f u.out ∂μΓ := by
  intro μΓ f' f
  let hΔ := isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) wA
  let hVclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  let : IsClosed (Vₐ : Set Gₐ) := hVclosed
  let : LocallyCompactSpace Vₐ := hVclosed.locallyCompactSpace
  let : SFinite μV := inferInstanceAs (SFinite (Measure.map _ ((AdelicSubgroupPoints.quotientMassNormalizer
    F G (SubgroupFunctor.range (iV ≫ q)) • (Measure.haar : Measure Vₐ)).restrict _)))
  let νM := μM'.restrict Dm
  let : SFinite νM := inferInstanceAs (SFinite (μM'.restrict Dm))
  let J (z : Xᵥ × (K × CanonicalQuotient F M')) := J₀ z.1.out z.2.2.out z.2.1
  let t (v : Xᵥ) := hK.heightCoordinates e (xV (v.out : Vₐ))
  have ht : Measurable t := measurable_adjunctionHeightShift iU l iV hK w hU e
  obtain ⟨d, hcut⟩ := integrate_cutoffWeightedKernel l' e' hM' hl' μM' μV μK J hJm hJi
  obtain ⟨hW'm, hW'i, hW'e⟩ := hcut β' hβ'c hβ's hβ' (fun _ => 0) measurable_const
  obtain ⟨hWm, hWi, hWe⟩ := hcut β hβc hβs hβ t ht
  let W' := cutoffWeightedKernel l' e' J β' (fun _ => 0)
  let W := cutoffWeightedKernel l' e' J β t
  have hB : Continuous B := continuous_adjunctionKernel l hK hK' c π' w φ ψ lam hφc hψc
  have hfc' : Continuous f' := ((Complex.continuous_ofReal.comp hβ'c).comp (hK'.continuous_heightCoordinates e')).mul hB
  let b : Gₐ → ℝ := fun g => β (hK.heightCoordinates e g)
  have hb : Continuous b := hβc.comp (hK.continuous_heightCoordinates e)
  have hfc : Continuous f := (Complex.continuous_ofReal.comp (hb.comp (continuous_const.mul continuous_id))).mul hB
  have hInv' : ∀ d ∈ Γ, ∀ g, f' (d * g) = f' g :=
    targetAdjunctionCutoff_invariant iU l iV l' hK hK' π' w lam hU hV hφ hψ e' β'
  have hInv : ∀ d ∈ Γ, ∀ g, f (d * g) = f g :=
    sourceAdjunctionCutoff_invariant iU l iV l' hK hK' π' w lam hU hV hφ hψ e β
  have hΔeq := mem_intertwiningRationalSubgroup_iff_adjunction iU l iV l' r w hw hG hU hq hV inferInstance
  let H (f₀ : Gₐ → ℂ) := unfoldedIntegrand (K := K) q iV l' Δ f₀
  have hUnfold (f₀ : Gₐ → ℂ) (hfc₀ : Continuous f₀) (hInv₀ : ∀ d ∈ Γ, ∀ g, f₀ (d * g) = f₀ g) :=
    unfoldDiscreteIwasawa q iV l' hV hK'.isCompact μM' hμM' Γ inf_le_left
      (inf_le_right.trans inf_le_left) (map_levi_mem_adjunctionRationalSubgroup l l' w hw)
      Δ hΔ hΔeq f₀ hfc₀ hInv₀
  have hHm (f₀ : Gₐ → ℂ) (hfc₀ : Continuous f₀) (hInv₀ : ∀ d ∈ Γ, ∀ g, f₀ (d * g) = f₀ g) : Measurable (H f₀) :=
    measurable_unfoldedIntegrand q iV l' Δ hΔ f₀ hfc₀.measurable (fun u hu g => hInv₀ u.val ((hΔeq u).1 hu) g)
  have hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ := fun d hd => hφ d (Subgroup.mem_sup_left hd)
  have hψU : IsLeftInvariantUnder F G (parabolicUnipotentImage F q iV) ψ := fun d hd => hψ d (Subgroup.mem_sup_left hd)
  have hW' (m : Mₐ') (k : K) := normalizedAdjunction_fibres iU l iV l' hK hK' π' w hw φ ψ lam hU hV
    hπ' hφc hφU (fun _ => 1) continuous_const (fun _ _ _ => rfl) (fun m => β' (yQ m)) f' hψU
    (by
      intro m v k
      change (β' (hK'.heightCoordinates e' (v.val * gQ m * k.val)) : ℂ) * B (v.val * gQ m * k.val) = _
      have hv : v.val ∈ parabolicQuotientSubgroup F q iV l' := Subgroup.mem_sup_left v.property
      rw [mul_assoc v.val]
      dsimp only [IsIwasawaCompact.heightCoordinates]
      rw [hK'.height_leftInvariant_parabolic iV l' hV.1.isUnipotent _ hv, hK'.height_eq k.property rfl]
      simp only [Complex.ofReal_one, mul_one]) m k (hbal m)
  have hW (m : Mₐ') (k : K) := normalizedAdjunction_fibres iU l iV l' hK hK' π' w hw φ ψ lam hU hV
    hπ' hφc hφU b hb (fun u hu g => by
      unfold b IsIwasawaCompact.heightCoordinates
      rw [hK.height_leftInvariant_parabolic iU l hU.1.isUnipotent _ (Subgroup.mem_sup_left hu)])
    (fun _ => 1) f hψU (by simp [f, b]) m k (hbal m)
  have hJ (v : Xᵥ) (m : Mₐ') (k : K) : J (v, k, mk C m) = J₀ v.out m k :=
    normalizedAdjunction_canonical_out iU l iV l' hK w hw lam hφ hψ heφ heψ v.out m k
  have hShift (v : Xᵥ) (m : Mₐ') (k : K) : b (gP m * (xV (v.out : Vₐ) * k.val)) = β (yQ m + t v) := by
    unfold b
    rw [hK.heightCoordinates_map_mul, equivariant_levi_coordinates l l' π' e e' hπ' he]
    unfold IsIwasawaCompact.heightCoordinates t
    rw [hK.height_mul_right _ k.property]
    rfl
  have hprod' := integrable_integral_prod₃_of_fibres μV νM μK (H f') W' (hHm f' hfc' hInv') hW'm
    (fun m k => by simpa only [H, W', cutoffWeightedKernel, add_zero, Complex.ofReal_one, mul_one, hJ] using (hW' m k).1)
    (fun m k => by simpa only [H, W', cutoffWeightedKernel, add_zero, Complex.ofReal_one, mul_one, hJ] using (hW' m k).2) hW'i
  have hprod := integrable_integral_prod₃_of_fibres μV νM μK (H f) W (hHm f hfc hInv) hWm
    (fun m k => by simpa only [H, W, cutoffWeightedKernel, Complex.ofReal_one, one_mul, hShift, hJ] using (hW m k).1)
    (fun m k => by simpa only [H, W, cutoffWeightedKernel, Complex.ofReal_one, one_mul, hShift, hJ] using (hW m k).2) hWi
  have hu' := hUnfold f' hfc' hInv'
  have hu := hUnfold f hfc hInv
  exact ⟨hu'.1.mpr hprod'.1, hu.1.mpr hprod.1,
    hu'.2.trans (hprod'.2.trans (hW'e.trans (hWe.symm.trans (hprod.2.symm.trans hu.2.symm))))⟩

end Langlands.Global.AdelicGroupPoints
