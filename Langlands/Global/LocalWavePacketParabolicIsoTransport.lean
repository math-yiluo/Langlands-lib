import Langlands.Global.LocalWavePacketPairLimit
import Langlands.Global.AdelicIntertwiningStandardizationProof
import Langlands.Global.InducedInnerProductSesquilinearProof
import Langlands.Global.AdelicIntertwiningLeviQuotient
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.DiscreteLeftCosetMeasureTransport
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.GroupScheme.Dynamic.AdjointDeterminantModelIndependence
import Langlands.GroupScheme.Rational.RootKernelIdentityAction
import Langlands.Global.AdelicCharacterParameterPullback
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicWeilPointTransport

/-! # Transport of the truncated limit along isomorphisms of parabolic subgroups -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

section Modulus

variable {F : Type} [Field F] {P P₁ : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine P₁.X.left] [LocallyOfFiniteType P₁.X.hom]

/-- The determinant of the adjoint representation restricts along an isomorphism `P₁ ≅ P` to
the determinant of the adjoint representation of `P₁`. -/
theorem characterRestrict_adjointDeterminantCharacter_iso (e : P₁ ≅ P) :
    characterRestrict e.hom (Lie.adjointDeterminantCharacter P) =
      Lie.adjointDeterminantCharacter P₁ :=
  AutomorphicAction.characterRestrict_determinantCharacter_of_intertwining
    (AutomorphicAction.conjugation (𝟙 P₁)) (AutomorphicAction.conjugation (𝟙 P)) e.hom e
    (fun h x => by
      simp only [AutomorphicAction.conjugation_act, MonObj.mul_comp, GrpObj.inv_comp,
        Grp.id_hom_hom, Category.comp_id])
    _ _

/-- The modulus parameter restricts along an isomorphism to the modulus parameter. -/
theorem parameterRestrict_modulusParameter_iso (e : P₁ ≅ P) :
    parameterRestrict e.hom (modulusParameter F P) = modulusParameter F P₁ := by
  change (1 : ℂ) ⊗ₜ[ℤ] characterRestrict e.hom (Lie.adjointDeterminantCharacter P) = _
  rw [characterRestrict_adjointDeterminantCharacter_iso]
  rfl

/-- The half modulus parameter restricts along an isomorphism to the half modulus parameter. -/
theorem parameterRestrict_halfModulusParameter_iso (e : P₁ ≅ P) :
    parameterRestrict e.hom (halfModulusParameter F P) = halfModulusParameter F P₁ := by
  change (1 / 2 : ℂ) ⊗ₜ[ℤ] characterRestrict e.hom (Lie.adjointDeterminantCharacter P) = _
  rw [characterRestrict_adjointDeterminantCharacter_iso]
  rfl

end Modulus

section Forms

variable {F : Type} [Field F] [NumberField F]
  {G P M U P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom]
  [IsAffine P₁.X.left] [LocallyOfFiniteType P₁.X.hom] [IsAffine M₁.X.left]
  [LocallyOfFiniteType M₁.X.hom]
  {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {p₁ : P₁ ⟶ G} {iU₁ : U₁ ⟶ P₁} {l₁ : M₁ ⟶ P₁}
  (jP : P₁ ≅ P) (hjP : jP.hom ≫ p = p₁) (δ : M₁ ≅ M) (hδ : δ.hom ≫ l = l₁ ≫ jP.hom)

include hjP hδ in
/-- The point of `G(𝔸)` of a point of `M₁(𝔸)` is the point of its image in `M(𝔸)`. -/
theorem map_levi_iso (m : AdelicGroupPoints F M₁) :
    map F P₁ G p₁ (map F M₁ P₁ l₁ m) = map F P G p (map F M P l (map F M₁ M δ.hom m)) := by
  rw [← hjP, map_comp_apply_of_hom]
  congr 1
  rw [← map_comp_apply_of_hom, ← hδ, map_comp_apply_of_hom]

include hδ in
/-- Parameter powers of the restricted parameter at a point of `M₁(𝔸)` are those at its image
in `M(𝔸)`. -/
theorem parameterPower_levi_iso (lam : ComplexCharacterParameter F P)
    (m : AdelicGroupPoints F M₁) :
    parameterPower F P₁ (parameterRestrict jP.hom lam) (map F M₁ P₁ l₁ m) =
      parameterPower F P lam (map F M P l (map F M₁ M δ.hom m)) := by
  rw [parameterPower_parameterRestrict, ← map_comp_apply_of_hom, ← hδ, map_comp_apply_of_hom]

include hδ in
theorem modulusPower_levi_iso (m : AdelicGroupPoints F M₁) :
    parameterPower F P₁ (-modulusParameter F P₁) (map F M₁ P₁ l₁ m) =
      parameterPower F P (-modulusParameter F P) (map F M P l (map F M₁ M δ.hom m)) := by
  rw [← parameterRestrict_modulusParameter_iso jP, ← map_neg,
    parameterPower_levi_iso jP δ hδ]

include hjP hδ in
/-- Square integrable induced forms for `p` are square integrable induced forms for `p₁` when
`P₁ ≅ P` over `G`, the Levi subgroups correspond and the unipotent radicals have the same
image. -/
theorem IsSquareIntegrableInducedForm.of_iso {K : Subgroup (AdelicGroupPoints F G)}
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (hU : SubgroupFunctor.range (iU₁ ≫ p₁) = SubgroupFunctor.range (iU ≫ p))
    {v : AdelicGroupPoints F G → ℂ}
    (hv : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l v) :
    IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p₁ iU₁ l₁ v := by
  classical
  have hL : SubgroupFunctor.range (l₁ ≫ p₁) = SubgroupFunctor.range (l ≫ p) := by
    have h : δ.hom ≫ (l ≫ p) = l₁ ≫ p₁ := by
      rw [← Category.assoc, hδ, Category.assoc, hjP]
    exact le_antisymm (SubgroupFunctor.range_le_of_factor δ.hom h)
      (SubgroupFunctor.range_le_of_factor δ.inv (by rw [← h, Iso.inv_hom_id_assoc]))
  refine ⟨?_, ?_, ?_⟩
  · rw [parabolicQuotientSubgroup_eq_of_range_eq hU hL]
    exact hv.1
  · intro a ha g
    rw [map_levi_iso jP hjP δ hδ,
      hv.2.1 _ (RestrictionSplitCentre.map_mem_canonicalSubgroup δ ha),
      ← parameterRestrict_halfModulusParameter_iso jP, parameterPower_levi_iso jP δ hδ]
  · let μK := compactHaarProbability F G K hKc
    let Γ := RestrictionSplitCentre.canonicalRationalSubgroup F M
    let W (k : K) (m : AdelicGroupPoints F M) :=
      InducedInnerProductSesquilinear.normWeight p l v k m
    have hW (k : K) : ∀ x ∈ Γ, ∀ m, W k (x * m) = W k m := by
      apply LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
        (Δ := rationalSubgroup F M)
      · exact fun x hx m =>
          InducedInnerProductSesquilinear.normWeight_splitComponent_mul hv.2.1 hx k m
      · exact fun x hx m => InducedInnerProductSesquilinear.normWeight_rational_mul
          (fun a ha => hv.1.1 a (Subgroup.mem_sup_right ha)) hx k m
    obtain ⟨s, -, hs⟩ := RestrictionSplitCentre.map_canonicalMeasure (F := F) δ
    let Q := RestrictionSplitCentre.canonicalQuotientMap δ
    have hQ : Measurable Q := RestrictionSplitCentre.measurable_canonicalQuotientMap δ
    have hWi : Integrable (fun z : K × LeftCosetSpace Γ => W z.1 z.2.out)
        (μK.prod (RestrictionSplitCentre.canonicalMeasure F M)) := hv.2.2
    have : SFinite (RestrictionSplitCentre.canonicalMeasure F M) := by
      rw [RestrictionSplitCentre.canonicalMeasure, RestrictionSplitCentre.quotientHaarMeasure,
        normOneRationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
        LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
      infer_instance
    have : SFinite (RestrictionSplitCentre.canonicalMeasure F M₁) := by
      rw [RestrictionSplitCentre.canonicalMeasure, RestrictionSplitCentre.quotientHaarMeasure,
        normOneRationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
        LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
      infer_instance
    have hmap : Measure.map (Prod.map id Q)
        (μK.prod (RestrictionSplitCentre.canonicalMeasure F M₁)) =
        (s : ℝ≥0∞) • μK.prod (RestrictionSplitCentre.canonicalMeasure F M) := by
      rw [← Measure.map_prod_map _ _ measurable_id hQ, Measure.map_id, hs,
        Measure.prod_smul_right]
    have hint := hWi.smul_measure (c := (s : ℝ≥0∞)) ENNReal.coe_ne_top
    rw [← hmap] at hint
    refine (hint.comp_measurable (measurable_id.prodMap hQ)).congr
      (Eventually.of_forall fun z => ?_)
    change W z.1 (Q z.2).out = _
    have hz : Q z.2 = LeftCosetSpace.mk Γ (map F M₁ M δ.hom z.2.out) := by
      conv_lhs => rw [← LeftCosetSpace.mk_out _ z.2]
      rfl
    rw [hz, LeftCosetSpace.out_mk_of_invariant Γ (W z.1) (hW z.1)]
    change ‖parameterPower F P (-modulusParameter F P) (map F M P l (map F M₁ M δ.hom z.2.out))‖ *
        ‖v (map F P G p (map F M P l (map F M₁ M δ.hom z.2.out)) * (z.1 : AdelicGroupPoints F G))‖ ^ 2 =
      ‖parameterPower F P₁ (-modulusParameter F P₁) (map F M₁ P₁ l₁ z.2.out)‖ *
        ‖v (map F P₁ G p₁ (map F M₁ P₁ l₁ z.2.out) * (z.1 : AdelicGroupPoints F G))‖ ^ 2
    rw [modulusPower_levi_iso jP δ hδ, map_levi_iso jP hjP δ hδ]

end Forms

section RealParameters

variable {F : Type} [Field F] [NumberField F]

/-- Restriction of real parameters along an isomorphism `e : H' ≅ H`, as a real-linear
isomorphism `X^*(H) ⊗ ℝ ≃ X^*(H') ⊗ ℝ` whose inverse is restriction along `e.inv`. -/
def realParameterRestrictIsoEquiv {H H' : GroupScheme (Spec (CommRingCat.of F))} (e : H' ≅ H) :
    RealCharacterParameter F H ≃ₗ[ℝ] RealCharacterParameter F H' :=
  LinearEquiv.ofLinearMap (realCharacterParameterPullback e.hom)
    (realCharacterParameterPullback e.inv)
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s χ
      change s ⊗ₜ[ℤ] characterRestrict e.hom (characterRestrict e.inv χ) = s ⊗ₜ[ℤ] χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, e.hom_inv_id,
        characterRestrict_id]
      rfl)
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s χ
      change s ⊗ₜ[ℤ] characterRestrict e.inv (characterRestrict e.hom χ) = s ⊗ₜ[ℤ] χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, e.inv_hom_id,
        characterRestrict_id]
      rfl)

theorem realParameterRestrictIsoEquiv_apply {H H' : GroupScheme (Spec (CommRingCat.of F))}
    (e : H' ≅ H) (x : RealCharacterParameter F H) :
    realParameterRestrictIsoEquiv e x = realCharacterParameterPullback e.hom x :=
  rfl

/-- Restriction of parameters commutes with `μ ↦ iμ`. -/
theorem parameterRestrict_imaginaryParameter {H H' : GroupScheme (Spec (CommRingCat.of F))}
    (f : H' ⟶ H) (x : RealCharacterParameter F H) :
    parameterRestrict f (imaginaryParameter F H x) =
      imaginaryParameter F H' (realCharacterParameterPullback f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Real Weyl parameters correspond under restriction along maps compatible with the Levi
projections, the Weyl isomorphisms and the Levi inclusions. -/
theorem realWeylParameter_pullback_eq {P P₁ Q Q₁ M M₁ M' M'₁ : GroupScheme (Spec (CommRingCat.of F))}
    (l : M ⟶ P) (c : M' ⟶ M) (π : Q ⟶ M') (l₁ : M₁ ⟶ P₁) (c₁ : M'₁ ⟶ M₁) (π₁ : Q₁ ⟶ M'₁)
    (jP : P₁ ⟶ P) (jQ : Q₁ ⟶ Q) (h : π₁ ≫ c₁ ≫ l₁ ≫ jP = jQ ≫ π ≫ c ≫ l)
    (x : RealCharacterParameter F P) :
    realWeylParameter l₁ c₁ π₁ (realCharacterParameterPullback jP x) =
      realCharacterParameterPullback jQ (realWeylParameter l c π x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    change s ⊗ₜ[ℤ] characterRestrict (π₁ ≫ c₁ ≫ l₁) (characterRestrict jP χ) =
      s ⊗ₜ[ℤ] characterRestrict jQ (characterRestrict (π ≫ c ≫ l) χ)
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, ← AddMonoidHom.comp_apply,
      ← characterRestrict_comp]
    simp only [Category.assoc, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction of complex parameters along the identity is the identity. -/
theorem parameterRestrict_id_apply (H : GroupScheme (Spec (CommRingCat.of F)))
    (lam : ComplexCharacterParameter F H) : parameterRestrict (𝟙 H) lam = lam := by
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    change s ⊗ₜ[ℤ] characterRestrict (𝟙 H) χ = s ⊗ₜ[ℤ] χ
    rw [characterRestrict_id]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

end RealParameters

section Weyl

variable {F : Type} [Field F] {G P M P₁ M₁ Q M' : GroupScheme (Spec (CommRingCat.of F))}

/-- A Weyl conjugation for `(p₁, l₁)` composed with an isomorphism of Levi subgroups over `G` is
a Weyl conjugation for `(p, l)`. -/
theorem AdelicGroupPoints.IsWeylConjugation.comp_iso {p : P ⟶ G} {l : M ⟶ P} {p₁ : P₁ ⟶ G} {l₁ : M₁ ⟶ P₁}
    {q : Q ⟶ G} {l' : M' ⟶ Q} {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
    {c₁ : M' ⟶ M₁} (h : IsWeylConjugation p₁ l₁ q l' w c₁) (δ : M₁ ≅ M)
    (hδ : δ.hom ≫ l ≫ p = l₁ ≫ p₁) : IsWeylConjugation p l q l' w (c₁ ≫ δ.hom) := by
  have := h.isIso
  refine ⟨inferInstance, ?_⟩
  rw [Category.assoc, hδ, h.comp_eq]

end Weyl

section Source

variable {F : Type} [Field F] [NumberField F]
  {G P M U P₁ M₁ U₁ P' M' U' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsAffine P₁.X.left] [LocallyOfFiniteType P₁.X.hom] [IsAffine M₁.X.left]
  [LocallyOfFiniteType M₁.X.hom] [IsAffine U₁.X.left]
  [IsAffine P'.X.left] [LocallyOfFiniteType P'.X.hom] [IsAffine M'.X.left]
  [LocallyOfFiniteType M'.X.hom] [IsAffine U'.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}
  {Λ : ℕ → (RationalQuotient F G → ℂ) → RationalQuotient F G → ℂ}
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {p₁ : P₁ ⟶ G} [IsClosedImmersion p₁.hom.hom.left] {iU₁ : U₁ ⟶ P₁} {l₁ : M₁ ⟶ P₁}
  {p' : P' ⟶ G} [IsClosedImmersion p'.hom.hom.left] {iU' : U' ⟶ P'} {l' : M' ⟶ P'}
  [IsClosedImmersion (iU' ≫ p').hom.hom.left] {π' : P' ⟶ M'}

/-- The limit for `(p, l)` gives the limit for `(p₁, l₁)` when `P₁ ≅ P` over `G`, the Levi
subgroups correspond and the unipotent radicals have the same image. The regularity predicate
for `p` is that for `p₁` at the restricted parameter. -/
theorem TruncatedWavePacketPairLimit.of_iso_source (hK : IsIwasawaCompact p K)
    (hK₁ : IsIwasawaCompact p₁ K) (hK' : IsIwasawaCompact p' K)
    (jP : P₁ ≅ P) (hjP : jP.hom ≫ p = p₁) (δ : M₁ ≅ M) (hδ : δ.hom ≫ l = l₁ ≫ jP.hom)
    (hU : SubgroupFunctor.range (iU ≫ p) = SubgroupFunctor.range (iU₁ ≫ p₁))
    {Reg₁ : ℝ → ComplexCharacterParameter F P₁ → Prop}
    {Reg' : ℝ → ComplexCharacterParameter F P' → Prop}
    (hlim : TruncatedWavePacketPairLimit K Λ p iU l hK
      (fun R lam => Reg₁ R (parameterRestrictIsoEquiv jP lam)) p' iU' l' π' hK' Reg') :
    TruncatedWavePacketPairLimit K Λ p₁ iU₁ l₁ hK₁ Reg₁ p' iU' l' π' hK' Reg' := by
  classical
  intro N d rho hsmooth hcalc hrho μM' _ hμM' n n' e₁ e' β' hβc hβs hβ1 k q v b₁ c S E₁ D₁ hv
    hb hS hc hD hE hEis k' q' v' b' c' S' E' D' hv' hb' hS' hc' hD' hE' hEis' T _ w cw hw hinj
    hsurj m ψ coeff₁ DM₁ hψ hDM hcoeff hexp
  let iota := parameterRestrictIsoEquiv jP
  let iotaR := realParameterRestrictIsoEquiv (F := F) jP
  let e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P := e₁.trans iotaR.symm
  have hie (x : Fin n → ℝ) :
      iota (imaginaryParameter F P (e x)) = imaginaryParameter F P₁ (e₁ x) := by
    rw [parameterRestrictIsoEquiv_apply, parameterRestrict_imaginaryParameter]
    congr 1
    exact iotaR.apply_symm_apply (e₁ x)
  have hrange : SubgroupFunctor.range p = SubgroupFunctor.range p₁ :=
    le_antisymm (SubgroupFunctor.range_le_of_factor jP.inv (by rw [← hjP, Iso.inv_hom_id_assoc]))
      (SubgroupFunctor.range_le_of_factor jP.hom hjP)
  have hδl : δ.hom ≫ l ≫ p = l₁ ≫ p₁ := by
    rw [← Category.assoc, hδ, Category.assoc, hjP]
  have hδl' : δ.inv ≫ l₁ ≫ p₁ = l ≫ p := by
    rw [← hδl, Iso.inv_hom_id_assoc]
  have hWc (c₁ : M' ⟶ M₁) : π' ≫ c₁ ≫ l₁ ≫ jP.hom = 𝟙 P' ≫ π' ≫ (c₁ ≫ δ.hom) ≫ l := by
    simp only [Category.id_comp, Category.assoc, hδ]
  have hwp (c₁ : M' ⟶ M₁) (lam : ComplexCharacterParameter F P) :
      weylParameter l (c₁ ≫ δ.hom) π' lam = weylParameter l₁ c₁ π' (iota lam) := by
    rw [parameterRestrictIsoEquiv_apply,
      weylParameter_parameterRestrict_eq l (c₁ ≫ δ.hom) π' l₁ c₁ π' jP.hom (𝟙 P') (hWc c₁),
      complexCharacterParameterPullback_id, LinearMap.id_apply]
  have hrwp (c₁ : M' ⟶ M₁) (x : Fin n → ℝ) :
      realWeylParameter l (c₁ ≫ δ.hom) π' (e x) = realWeylParameter l₁ c₁ π' (e₁ x) := by
    have h := realWeylParameter_pullback_eq l (c₁ ≫ δ.hom) π' l₁ c₁ π' jP.hom (𝟙 P') (hWc c₁)
      (e x)
    rw [realCharacterParameterPullback_id, LinearMap.id_apply] at h
    rw [← h]
    congr 1
    exact iotaR.apply_symm_apply (e₁ x)
  have hvP (j : Fin k) (i : Fin q) :
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j i) :=
    IsSquareIntegrableInducedForm.of_iso jP.symm (by simp only [Iso.symm_hom, ← hjP,
      Iso.inv_hom_id_assoc]) δ.symm (by
        simp only [Iso.symm_hom]
        rw [Iso.inv_comp_eq, ← Category.assoc, hδ, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]) hK.isCompact hU (hv j i)
  have hbP (j : Fin k) (i : Fin q) : IsMeromorphicInCoordinatesOn (b₁ j i ∘ iota) Set.univ := by
    simpa only [Set.preimage_univ] using (hb j i).comp_linearEquiv iota
  have hDP : (fun x => imaginaryParameter F P (e x)) '' S ⊆ iota ⁻¹' D₁ := by
    rintro _ ⟨x, hx, rfl⟩
    change iota (imaginaryParameter F P (e x)) ∈ D₁
    rw [hie]
    exact hD ⟨x, hx, rfl⟩
  have hDMP : (fun x => imaginaryParameter F P (e x)) '' S ⊆ iota ⁻¹' DM₁ := by
    rintro _ ⟨x, hx, rfl⟩
    change iota (imaginaryParameter F P (e x)) ∈ DM₁
    rw [hie]
    exact hDM ⟨x, hx, rfl⟩
  have hEisP (j : Fin k) : ∃ R : ℝ, ∀ lam, Reg₁ R (iota lam) → ∀ g,
      E₁ j (iota lam) g = ∑ i, (b₁ j i ∘ iota) lam * hK.eisensteinSeries (v j i) lam g := by
    obtain ⟨R, hR⟩ := hEis j
    refine ⟨R, fun lam hlam g => ?_⟩
    rw [hR _ hlam g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hK.eisensteinSeries_eq_of_range_eq hK₁ jP.hom hjP hrange]
    rfl
  have hwP (t : T) : IsWeylConjugation p l p' l' (w t) (cw t ≫ δ.hom) :=
    (hw t).comp_iso δ hδl
  have hinjP : Function.Injective (fun t => weylParameter l (cw t ≫ δ.hom) π') := by
    intro t t' htt'
    apply hinj
    refine LinearMap.ext fun mu => ?_
    have h := LinearMap.congr_fun htt' (iota.symm mu)
    simp only [hwp, LinearEquiv.apply_symm_apply] at h
    exact h
  have hsurjP : ∀ σ ∈ weylParameterSet p l p' l' π',
      ∃ t, weylParameter l (cw t ≫ δ.hom) π' = σ := by
    rintro σ ⟨w₀, c₀, hc₀, rfl⟩
    obtain ⟨t, ht⟩ := hsurj (weylParameter l₁ (c₀ ≫ δ.inv) π')
      ⟨w₀, c₀ ≫ δ.inv, hc₀.comp_iso δ.symm hδl', rfl⟩
    refine ⟨t, LinearMap.ext fun lam => ?_⟩
    rw [hwp, ht, ← hwp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcoeffP (t : T) (j : Fin k) (i : Fin m) :
      IsMeromorphicInCoordinatesOn (coeff₁ t j i ∘ iota) (iota ⁻¹' DM₁) :=
    (hcoeff t j i).comp_linearEquiv iota
  have hexpP (t : T) (j : Fin k) : ∃ R : ℝ, ∀ lam, Reg₁ R (iota lam) → ∀ g,
      ∑ i, (b₁ j i ∘ iota) lam *
          hK.intertwiningOperator hK' iU l iU' (cw t ≫ δ.hom) π' (w t) (v j i) lam g =
        ∑ i, (coeff₁ t j i ∘ iota) lam * ψ t j i g := by
    obtain ⟨R, hR⟩ := hexp t j
    refine ⟨R, fun lam hlam g => ?_⟩
    simp only [Function.comp_apply]
    rw [← hR _ hlam g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hK.intertwiningOperator_eq_of_transport hK' hK₁ hK' iU l iU' (cw t ≫ δ.hom) π' iU₁ l₁
      iU' (cw t) π' jP.hom hjP (𝟙 P') (Category.id_comp _) hU rfl (hWc (cw t)) (w t) (v j i)
      lam g]
    rfl
  have h := hlim rho hsmooth hcalc hrho μM' hμM' e e' β' hβc hβs hβ1 k q v
    (fun j i => b₁ j i ∘ iota) c S (fun j lam g => E₁ j (iota lam) g) (iota ⁻¹' D₁) hvP hbP hS hc hDP
    (fun j g => (hE j g).comp_linearEquiv iota) hEisP k' q' v' b' c' S' E' D' hv' hb' hS' hc' hD'
    hE' hEis' T w (fun t => cw t ≫ δ.hom) hwP hinjP hsurjP m ψ (fun t j i => coeff₁ t j i ∘ iota)
    (iota ⁻¹' DM₁) hψ hDMP hcoeffP hexpP
  simpa only [Function.comp_apply, hie, hwp, hrwp] using h

end Source

section InnerProduct

variable {F : Type} [Field F] [NumberField F]

/-- The normalized Haar measures of two equal subgroup functors give the same integrals. -/
theorem integral_normalizedHaarMeasure_congr {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] {V V' : SubgroupFunctor G} (h : V = V')
    [IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G))]
    [IsClosed (AdelicSubgroupPoints.adelicPoints F G V' : Set (AdelicGroupPoints F G))]
    (f : AdelicGroupPoints F G → ℂ) :
    ∫ u, f (u : AdelicGroupPoints F G) ∂(AdelicSubgroupPoints.normalizedHaarMeasure F G V) =
      ∫ u, f (u : AdelicGroupPoints F G) ∂(AdelicSubgroupPoints.normalizedHaarMeasure F G V') := by
  subst h
  rfl

theorem map_map_eq_comp_apply {A B C : GroupScheme (Spec (CommRingCat.of F))} (f : A ⟶ B)
    (g : B ⟶ C) (x : AdelicGroupPoints F A) :
    map F B C g (map F A B f x) = map F A C (f ≫ g) x := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]

theorem map_mem_rationalSubgroup_of_hom {A B : GroupScheme (Spec (CommRingCat.of F))}
    (f : A ⟶ B) {x : AdelicGroupPoints F A} (hx : x ∈ rationalSubgroup F A) :
    map F A B f x ∈ rationalSubgroup F B := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨_, DFunLike.congr_fun (rational_naturality F A f) q⟩

/-- A point of `M₁(𝔸)` is rational if and only if its image under an isomorphism is. -/
theorem map_mem_rationalSubgroup_iff_of_iso {M M₁ : GroupScheme (Spec (CommRingCat.of F))}
    (δ : M₁ ≅ M) (x : AdelicGroupPoints F M₁) :
    map F M₁ M δ.hom x ∈ rationalSubgroup F M ↔ x ∈ rationalSubgroup F M₁ := by
  refine ⟨fun hx => ?_, map_mem_rationalSubgroup_of_hom δ.hom⟩
  have h := map_mem_rationalSubgroup_of_hom δ.inv hx
  rwa [map_map_eq_comp_apply, Iso.hom_inv_id, show map F M₁ M₁ (𝟙 M₁) x = x by
    simp only [map_apply, GroupScheme.affinePointsTarget_apply]
    exact Category.comp_id x] at h

/-- The pairing of a real parameter with the image of a log vector under `f` is the pairing of
the pulled back parameter with the log vector. -/
theorem realParameterPairing_realCharacterDualMap {H H' : GroupScheme (Spec (CommRingCat.of F))}
    (f : H' ⟶ H) (x : RealCharacterParameter F H) (Y : RealCharacterDual F H') :
    realParameterPairing F H x (realCharacterDualMap F H' H f Y) =
      realParameterPairing F H' (realCharacterParameterPullback f x) Y := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Coordinates of log vectors are unchanged by an isomorphism `P₁ ≅ P` when the coordinate
system is transported along the restriction of real parameters. -/
theorem parameterCoordinates_iso {P P₁ : GroupScheme (Spec (CommRingCat.of F))} (jP : P₁ ≅ P)
    {n : ℕ} (e₁ : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P₁) (Y : RealCharacterDual F P₁) :
    parameterCoordinates F P (e₁.trans (realParameterRestrictIsoEquiv jP).symm)
        (realCharacterDualMap F P₁ P jP.hom Y) = parameterCoordinates F P₁ e₁ Y := by
  funext j
  simp only [parameterCoordinates]
  rw [realParameterPairing_realCharacterDualMap]
  congr 2
  exact (realParameterRestrictIsoEquiv jP).apply_symm_apply _

variable {G P M P₁ M₁ : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom]
  [IsAffine P₁.X.left] [LocallyOfFiniteType P₁.X.hom] [IsAffine M₁.X.left]
  [LocallyOfFiniteType M₁.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {p₁ : P₁ ⟶ G} {l₁ : M₁ ⟶ P₁}
  (jP : P₁ ≅ P) (hjP : jP.hom ≫ p = p₁) (δ : M₁ ≅ M) (hδ : δ.hom ≫ l = l₁ ≫ jP.hom)

include hjP hδ in
/-- The integrand of the induced inner product at the image of a point of `M₁(𝔸)`. -/
theorem kernel_levi_iso {n : ℕ} (e₁ : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P₁)
    (β : (Fin n → ℝ) → ℝ) (φ ψ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (m : AdelicGroupPoints F M₁) :
    InducedInnerProductSesquilinear.kernel p l (e₁.trans (realParameterRestrictIsoEquiv jP).symm)
        β φ ψ g (map F M₁ M δ.hom m) =
      InducedInnerProductSesquilinear.kernel p₁ l₁ e₁ β φ ψ g m := by
  have hlog : characterLog F P (map F M P l (map F M₁ M δ.hom m)) =
      realCharacterDualMap F P₁ P jP.hom (characterLog F P₁ (map F M₁ P₁ l₁ m)) := by
    rw [← characterLog_map, map_map_eq_comp_apply, map_map_eq_comp_apply, hδ]
  simp only [InducedInnerProductSesquilinear.kernel, InducedInnerProductSesquilinear.weight]
  rw [hlog, parameterCoordinates_iso, ← modulusPower_levi_iso jP δ hδ,
    ← map_levi_iso jP hjP δ hδ]

include hjP hδ in
/-- The induced inner product for `(p, l)` with the image measure of a Haar measure on `M₁(𝔸)`
is the induced inner product for `(p₁, l₁)`, for functions invariant under the rational points
of the Levi subgroup. -/
theorem inducedInnerProduct_levi_iso (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (μ₁ : Measure (AdelicGroupPoints F M₁))
    [μ₁.IsHaarMeasure] {n : ℕ} (e₁ : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P₁)
    (β : (Fin n → ℝ) → ℝ) {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ)
    (hψ : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) ψ) :
    inducedInnerProduct K hKc p l (Measure.map (adelicPointsIso F δ) μ₁)
        (e₁.trans (realParameterRestrictIsoEquiv jP).symm) β φ ψ =
      inducedInnerProduct K hKc p₁ l₁ μ₁ e₁ β φ ψ := by
  rw [InducedInnerProductSesquilinear.inducedInnerProduct_eq_kernel,
    InducedInnerProductSesquilinear.inducedInnerProduct_eq_kernel]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  have hrat (x : AdelicGroupPoints F M₁) :
      adelicPointsIso F δ x ∈ rationalSubgroup F M ↔ x ∈ rationalSubgroup F M₁ :=
    map_mem_rationalSubgroup_iff_of_iso δ x
  have hΦ := LeftCosetSpace.measurePreserving_discreteQuotientMeasure (adelicPointsIso F δ)
    (rationalSubgroup F M₁) (rationalSubgroup F M) hrat (isDiscrete_rationalSubgroup F M₁)
    (isDiscrete_rationalSubgroup F M) μ₁ (Measure.map (adelicPointsIso F δ) μ₁)
    ⟨(adelicPointsIso F δ).continuous.measurable, rfl⟩
  dsimp only
  rw [← hΦ.integral_comp']
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hx : LeftCosetSpace.measurableEquivOfMulEquiv (adelicPointsIso F δ)
      (rationalSubgroup F M₁) (rationalSubgroup F M) hrat x =
      LeftCosetSpace.mk (rationalSubgroup F M) (map F M₁ M δ.hom x.out) := by
    conv_lhs => rw [← LeftCosetSpace.mk_out _ x]
    rfl
  change InducedInnerProductSesquilinear.kernel p l _ β φ ψ k
      (LeftCosetSpace.measurableEquivOfMulEquiv (adelicPointsIso F δ)
        (rationalSubgroup F M₁) (rationalSubgroup F M) hrat x).out = _
  rw [hx, LeftCosetSpace.out_mk_of_invariant (rationalSubgroup F M)
      (InducedInnerProductSesquilinear.kernel p l _ β φ ψ k)
      (fun g0 hg0 m => InducedInnerProductSesquilinear.kernel_rational_mul _ β hφ hψ hg0 k m),
    kernel_levi_iso jP hjP δ hδ]

include hjP hδ in
/-- A Haar measure on `M₁(𝔸)` compatible with the Iwasawa decomposition for `(p₁, l₁)` has an
image on `M(𝔸)` compatible with the Iwasawa decomposition for `(p, l)`, when the unipotent
radicals have the same image. -/
theorem IsIwasawaCompatibleMeasure.map_levi_iso {U U₁ : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine U.X.left] [IsAffine U₁.X.left] {iU : U ⟶ P} {iU₁ : U₁ ⟶ P₁}
    [IsClosedImmersion (iU ≫ p).hom.hom.left] [IsClosedImmersion (iU₁ ≫ p₁).hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)} (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    (hU : SubgroupFunctor.range (iU₁ ≫ p₁) = SubgroupFunctor.range (iU ≫ p))
    {μ₁ : Measure (AdelicGroupPoints F M₁)}
    (hμ : IsIwasawaCompatibleMeasure K hKc p₁ iU₁ l₁ μ₁) :
    IsIwasawaCompatibleMeasure K hKc p iU l (Measure.map (adelicPointsIso F δ) μ₁) := by
  intro f
  rw [hμ f]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  have hme : MeasurableEmbedding (adelicPointsIso F δ) :=
    (adelicPointsIso F δ).toHomeomorph.measurableEmbedding
  dsimp only
  rw [hme.integral_map]
  refine integral_congr_ae (Eventually.of_forall fun m => ?_)
  dsimp only
  change _ = ∫ u : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)),
    parameterPower F P (-modulusParameter F P)
      (map F M P l (map F M₁ M δ.hom m)) *
      f ((u : AdelicGroupPoints F G) * map F P G p (map F M P l (map F M₁ M δ.hom m)) *
        (k : AdelicGroupPoints F G)) ∂_
  rw [← modulusPower_levi_iso jP δ hδ, ← Langlands.Global.map_levi_iso jP hjP δ hδ]
  exact integral_normalizedHaarMeasure_congr hU (fun u => parameterPower F P₁
    (-modulusParameter F P₁) (map F M₁ P₁ l₁ m) *
      f (u * map F P₁ G p₁ (map F M₁ P₁ l₁ m) * (k : AdelicGroupPoints F G)))

end InnerProduct

section Target

variable {F : Type} [Field F] [NumberField F]
  {G P M U P' M' U' P'₁ M'₁ U'₁ : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsAffine P'.X.left] [LocallyOfFiniteType P'.X.hom] [IsAffine M'.X.left]
  [LocallyOfFiniteType M'.X.hom] [IsAffine U'.X.left]
  [IsAffine P'₁.X.left] [LocallyOfFiniteType P'₁.X.hom] [IsAffine M'₁.X.left]
  [LocallyOfFiniteType M'₁.X.hom] [IsAffine U'₁.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}
  {Λ : ℕ → (RationalQuotient F G → ℂ) → RationalQuotient F G → ℂ}
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {p' : P' ⟶ G} [IsClosedImmersion p'.hom.hom.left] {iU' : U' ⟶ P'} {l' : M' ⟶ P'}
  [IsClosedImmersion (iU' ≫ p').hom.hom.left] {π' : P' ⟶ M'}
  {p'₁ : P'₁ ⟶ G} [IsClosedImmersion p'₁.hom.hom.left] {iU'₁ : U'₁ ⟶ P'₁} {l'₁ : M'₁ ⟶ P'₁}
  [IsClosedImmersion (iU'₁ ≫ p'₁).hom.hom.left] {π'₁ : P'₁ ⟶ M'₁}

omit [NumberField F] in
/-- A Weyl conjugation into `(q₁, l'₁)` gives, after an isomorphism of Levi subgroups over `G`,
a Weyl conjugation into `(q, l')`. -/
theorem AdelicGroupPoints.IsWeylConjugation.iso_comp {Q Q₁ : GroupScheme (Spec (CommRingCat.of F))}
    {q : Q ⟶ G} {l'' : M' ⟶ Q} {q₁ : Q₁ ⟶ G} {l''₁ : M'₁ ⟶ Q₁}
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M'₁ ⟶ M}
    (h : IsWeylConjugation p l q₁ l''₁ w c) (κ : M'₁ ≅ M')
    (hκ : κ.hom ≫ l'' ≫ q = l''₁ ≫ q₁) : IsWeylConjugation p l q l'' w (κ.inv ≫ c) := by
  have := h.isIso
  refine ⟨inferInstance, ?_⟩
  rw [Category.assoc, h.comp_eq, ← Category.assoc l''₁, ← hκ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The limit for the target `(p', l', π')` gives the limit for `(p'₁, l'₁, π'₁)` when
`P'₁ ≅ P'` over `G`, the Levi subgroups and Levi projections correspond and the unipotent
radicals have the same image. The regularity predicate for `p'` is that for `p'₁` at the
restricted parameter. -/
theorem TruncatedWavePacketPairLimit.of_iso_target (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact p' K) (hK'₁ : IsIwasawaCompact p'₁ K)
    (jQ : P'₁ ≅ P') (hjQ : jQ.hom ≫ p' = p'₁) (κ : M'₁ ≅ M') (hκ : κ.hom ≫ l' = l'₁ ≫ jQ.hom)
    (hπ : π'₁ ≫ κ.hom = jQ.hom ≫ π')
    (hV : SubgroupFunctor.range (iU' ≫ p') = SubgroupFunctor.range (iU'₁ ≫ p'₁))
    {Reg : ℝ → ComplexCharacterParameter F P → Prop}
    {Reg'₁ : ℝ → ComplexCharacterParameter F P'₁ → Prop}
    (hlim : TruncatedWavePacketPairLimit K Λ p iU l hK Reg p' iU' l' π' hK'
      (fun R lam => Reg'₁ R (parameterRestrictIsoEquiv jQ lam))) :
    TruncatedWavePacketPairLimit K Λ p iU l hK Reg p'₁ iU'₁ l'₁ π'₁ hK'₁ Reg'₁ := by
  classical
  intro N d rho hsmooth hcalc hrho μM'₁ _ hμM'₁ n n' e e'₁ β' hβc hβs hβ1 k q v b c S E D hv
    hb hS hc hD hE hEis k' q' v' b'₁ c' S' E'₁ D'₁ hv' hb' hS' hc' hD' hE' hEis' T _ w cw₁ hw hinj
    hsurj m ψ coeff DM hψ hDM hcoeff hexp
  let iota := parameterRestrictIsoEquiv jQ
  let iotaR := realParameterRestrictIsoEquiv (F := F) jQ
  let e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P' := e'₁.trans iotaR.symm
  let μM' : Measure (AdelicGroupPoints F M') := Measure.map (adelicPointsIso F κ) μM'₁
  have : μM'.IsHaarMeasure := (adelicPointsIso F κ).isHaarMeasure_map μM'₁
  have hie (x : Fin n' → ℝ) :
      iota (imaginaryParameter F P' (e' x)) = imaginaryParameter F P'₁ (e'₁ x) := by
    rw [parameterRestrictIsoEquiv_apply, parameterRestrict_imaginaryParameter]
    congr 1
    exact iotaR.apply_symm_apply (e'₁ x)
  have hes (y : RealCharacterParameter F P') : e'.symm y = e'₁.symm (iotaR y) := rfl
  have hrange : SubgroupFunctor.range p' = SubgroupFunctor.range p'₁ :=
    le_antisymm (SubgroupFunctor.range_le_of_factor jQ.inv (by rw [← hjQ, Iso.inv_hom_id_assoc]))
      (SubgroupFunctor.range_le_of_factor jQ.hom hjQ)
  have hκl : κ.hom ≫ l' ≫ p' = l'₁ ≫ p'₁ := by
    rw [← Category.assoc, hκ, Category.assoc, hjQ]
  have hκl' : κ.inv ≫ l'₁ ≫ p'₁ = l' ≫ p' := by
    rw [← hκl, Iso.inv_hom_id_assoc]
  have hWc (c₁ : M'₁ ⟶ M) : π'₁ ≫ c₁ ≫ l ≫ 𝟙 P = jQ.hom ≫ π' ≫ (κ.inv ≫ c₁) ≫ l := by
    rw [← Category.assoc jQ.hom, ← hπ]
    simp only [Category.comp_id, Category.assoc, Iso.hom_inv_id_assoc]
  have hwp (c₁ : M'₁ ⟶ M) (lam : ComplexCharacterParameter F P) :
      iota (weylParameter l (κ.inv ≫ c₁) π' lam) = weylParameter l c₁ π'₁ lam := by
    rw [parameterRestrictIsoEquiv_apply,
      ← weylParameter_parameterRestrict_eq l (κ.inv ≫ c₁) π' l c₁ π'₁ (𝟙 P) jQ.hom (hWc c₁),
      parameterRestrict_id_apply]
  have hrwp (c₁ : M'₁ ⟶ M) (x : RealCharacterParameter F P) :
      iotaR (realWeylParameter l (κ.inv ≫ c₁) π' x) = realWeylParameter l c₁ π'₁ x := by
    have h := realWeylParameter_pullback_eq l (κ.inv ≫ c₁) π' l c₁ π'₁ (𝟙 P) jQ.hom (hWc c₁) x
    rw [realCharacterParameterPullback_id, LinearMap.id_apply] at h
    rw [h]
    rfl
  have hjQs : jQ.symm.hom ≫ p'₁ = p' := by
    simp only [Iso.symm_hom, ← hjQ, Iso.inv_hom_id_assoc]
  have hκs : κ.symm.hom ≫ l'₁ = l' ≫ jQ.symm.hom := by
    simp only [Iso.symm_hom]
    rw [Iso.inv_comp_eq, ← Category.assoc, hκ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hvP (j : Fin k') (i : Fin q') :
      IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v' j i) :=
    IsSquareIntegrableInducedForm.of_iso jQ.symm hjQs κ.symm hκs hK'.isCompact hV (hv' j i)
  have hψP (t : T) (j : Fin k) (i : Fin m) :
      IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ t j i) :=
    IsSquareIntegrableInducedForm.of_iso jQ.symm hjQs κ.symm hκs hK'.isCompact hV (hψ t j i)
  have hμ : IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' :=
    IsIwasawaCompatibleMeasure.map_levi_iso jQ hjQ κ hκ hK'.isCompact hV.symm hμM'₁
  have hbP (j : Fin k') (i : Fin q') : IsMeromorphicInCoordinatesOn (b'₁ j i ∘ iota) Set.univ := by
    simpa only [Set.preimage_univ] using (hb' j i).comp_linearEquiv iota
  have hDP : (fun x => imaginaryParameter F P' (e' x)) '' S' ⊆ iota ⁻¹' D'₁ := by
    rintro _ ⟨x, hx, rfl⟩
    change iota (imaginaryParameter F P' (e' x)) ∈ D'₁
    rw [hie]
    exact hD' ⟨x, hx, rfl⟩
  have hEisP (j : Fin k') : ∃ R : ℝ, ∀ lam, Reg'₁ R (iota lam) → ∀ g,
      E'₁ j (iota lam) g = ∑ i, (b'₁ j i ∘ iota) lam * hK'.eisensteinSeries (v' j i) lam g := by
    obtain ⟨R, hR⟩ := hEis' j
    refine ⟨R, fun lam hlam g => ?_⟩
    rw [hR _ hlam g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hK'.eisensteinSeries_eq_of_range_eq hK'₁ jQ.hom hjQ hrange]
    rfl
  have hwP (t : T) : IsWeylConjugation p l p' l' (w t) (κ.inv ≫ cw₁ t) :=
    (hw t).iso_comp κ hκl
  have hinjP : Function.Injective (fun t => weylParameter l (κ.inv ≫ cw₁ t) π') := by
    intro t t' htt'
    apply hinj
    refine LinearMap.ext fun lam => ?_
    have h := congrArg iota (LinearMap.congr_fun htt' lam)
    simp only [hwp] at h
    exact h
  have hsurjP : ∀ σ ∈ weylParameterSet p l p' l' π',
      ∃ t, weylParameter l (κ.inv ≫ cw₁ t) π' = σ := by
    rintro σ ⟨w₀, c₀, hc₀, rfl⟩
    obtain ⟨t, ht⟩ := hsurj (weylParameter l (κ.hom ≫ c₀) π'₁)
      ⟨w₀, κ.hom ≫ c₀, hc₀.iso_comp κ.symm hκl', rfl⟩
    refine ⟨t, LinearMap.ext fun lam => iota.injective ?_⟩
    rw [hwp, ht, ← hwp, Iso.inv_hom_id_assoc]
  have hexpP (t : T) (j : Fin k) : ∃ R : ℝ, ∀ lam, Reg R lam → ∀ g,
      ∑ i, b j i lam *
          hK.intertwiningOperator hK' iU l iU' (κ.inv ≫ cw₁ t) π' (w t) (v j i) lam g =
        ∑ i, coeff t j i lam * ψ t j i g := by
    obtain ⟨R, hR⟩ := hexp t j
    refine ⟨R, fun lam hlam g => ?_⟩
    rw [← hR _ hlam g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hK.intertwiningOperator_eq_of_transport hK' hK hK'₁ iU l iU' (κ.inv ≫ cw₁ t) π' iU l
      iU'₁ (cw₁ t) π'₁ (𝟙 P) (Category.id_comp _) jQ.hom hjQ rfl hV (hWc (cw₁ t)) (w t) (v j i)
      lam g, parameterRestrict_id_apply]
  have hip (t : T) (j : Fin k) (i : Fin m) (j' : Fin k') (i' : Fin q') :
      inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ t j i) (v' j' i') =
        inducedInnerProduct K hK'₁.isCompact p'₁ l'₁ μM'₁ e'₁ β' (ψ t j i) (v' j' i') :=
    inducedInnerProduct_levi_iso jQ hjQ κ hκ K hK'.isCompact μM'₁ e'₁ β'
      (fun x hx g' => (hψP t j i).1.1 x (Subgroup.mem_sup_right hx) g')
      (fun x hx g' => (hvP j' i').1.1 x (Subgroup.mem_sup_right hx) g')
  have h := hlim rho hsmooth hcalc hrho μM' hμ e e' β' hβc hβs hβ1 k q v b c S E D hv hb hS hc hD
    hE hEis k' q' v' (fun j i => b'₁ j i ∘ iota) c' S' (fun j lam g => E'₁ j (iota lam) g)
    (iota ⁻¹' D'₁) hvP hbP hS' hc' hDP (fun j g => (hE' j g).comp_linearEquiv iota) hEisP T w
    (fun t => κ.inv ≫ cw₁ t) hwP hinjP hsurjP m ψ coeff DM hψP hDM hcoeff hexpP
  simpa only [Function.comp_apply, hie, hwp, hes, hrwp, hip] using h

end Target

end Langlands.Global
