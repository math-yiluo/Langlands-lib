import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.InducedInnerProductSesquilinearProof
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # Conjugation of the compact subgroup in the Levi pairing -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions
open InducedInnerProductIntegrable

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "Gₐ" => AdelicGroupPoints F G
local notation "P" => fam.P J
local notation "M" => fam.M J
local notation "U" => fam.U J
local notation "M₁" => normOneSubgroup F M
local notation "Q" => NormOneRationalQuotient F M
local notation "Γ" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)
local notation "pₐ" => map F P G (fam.p J)
local notation "lₐ" => map F M P (fam.l J)
local notation "uₐ" => map F U P (fam.iU J)
local notation "mₐ" => map F M G (fam.l J ≫ fam.p J)

private def compactConjugation (K : Subgroup Gₐ) (t : Gₐ) :
    K ≃ₜ* K.map (MulAut.conj t).toMonoidHom where
  toMulEquiv := (MulAut.conj t).subgroupMap K
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

omit [IsAffineHom G.X.hom] in
private theorem measurePreserving_compactConjugation (K : Subgroup Gₐ) (t : Gₐ)
    (hK : IsCompact (K : Set Gₐ))
    (hK' : IsCompact ((K.map (MulAut.conj t).toMonoidHom : Subgroup Gₐ) : Set Gₐ)) :
    MeasurePreserving (compactConjugation K t).symm
      (compactHaarProbability F G _ hK') (compactHaarProbability F G K hK) := by
  let e := (compactConjugation K t).symm
  let measure := compactHaarProbability F G _ hK'
  let : (Measure.map e measure).IsHaarMeasure := e.isHaarMeasure_map measure
  have he : Measurable (⇑e) := e.continuous.measurable
  let : IsProbabilityMeasure (Measure.map e measure) :=
    (Measure.isProbabilityMeasure_map_iff he.aemeasurable).mpr inferInstance
  exact ⟨e.continuous.measurable, eq_compactHaarProbability F G K hK _⟩

private def sliceArgument {K : Subgroup Gₐ} (x : AdelicGroupPoints F P) (z : K × Q) : Gₐ :=
  pₐ x * mₐ (z.2.out : M₁).val * z.1.val

private theorem leviSlice_invariant {E : Type} {f : Gₐ → E}
    (hf : ∀ r ∈ Γ, ∀ g, f (r * g) = f g) (x : fam.positiveSplitComponent J) (k : Gₐ) :
    ∀ r ∈ rationalNormOneSubgroup F M, ∀ m : M₁,
      f (pₐ x.val * mₐ (r * m).val * k) = f (pₐ x.val * mₐ m.val * k) := by
  intro r hr m
  have hr' : r.val ∈ rationalSubgroup F M := by
    obtain ⟨b, hb⟩ := hr
    exact ⟨b, congrArg Subtype.val hb⟩
  have hm : mₐ r.val ∈ Γ := by
    rw [map_comp_apply_of_hom]
    exact map_map_mem_parabolicQuotientSubgroup (fam.p J) (fam.iU J) (fam.l J) hr'
  rw [Subgroup.coe_mul, map_mul, ← mul_assoc (pₐ x.val) (mₐ r.val),
    (fam.commute_positiveSplitComponent_levi J x r.val).eq, mul_assoc, mul_assoc]
  rw [hf _ hm, mul_assoc]

private theorem exists_leviSliceTranslation {K : Subgroup Gₐ}
    (hK : IsIwasawaCompact (fam.p J) K) (t : Gₐ)
    (hK' : IsCompact ((K.map (MulAut.conj t).toMonoidHom : Subgroup Gₐ) : Set Gₐ)) :
    ∃ (a : AdelicGroupPoints F M) (_ : a ∈ RestrictionSplitCentre.canonicalSubgroup F M)
      (y : fam.positiveSplitComponent J), y.val = lₐ a ∧
      ∃ e : (K.map (MulAut.conj t).toMonoidHom × Q) ≃ᵐ (K × Q),
        MeasurePreserving e (fam.squareIntegrablePairingMeasure _ hK' J)
          (fam.squareIntegrablePairingMeasure K hK.isCompact J) ∧
        ∀ (x : fam.positiveSplitComponent J) {E : Type} (f : Gₐ → E),
          (∀ r ∈ Γ, ∀ g, f (r * g) = f g) →
          ∀ z, f (fam.sliceArgument J x.val z * t) =
            f (fam.sliceArgument J (x * y).val (e z)) := by
  obtain ⟨q, k, hk, ht⟩ := hK.exists_eq t
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  let : IsIso (subgroupMultiplication (fam.l J) (fam.iU J)) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication r fam.connectedReductive
      (fam.isUnipotentRadical J)
  let u := radicalComponent (fam.l J) (fam.iU J) q
  let m₀ := leviComponent (fam.l J) (fam.iU J) q
  have hfactor : lₐ m₀ * uₐ u = q := leviComponent_mul_radicalComponent (fam.l J) (fam.iU J) q
  let hM := (fam.isCompatible J).levi.isConnectedReductive
  let d := RestrictionSplitCentre.intrinsicNormOneDecomposition F M hM
  let b := d.symm m₀
  let a := PositiveRealTorus.positivePointMap F M (RestrictionSplitCentre.canonicalTorus F M)
    (RestrictionSplitCentre.canonicalComponent F M) b.1
  have ha : a ∈ RestrictionSplitCentre.canonicalSubgroup F M :=
    InducedInnerProductSesquilinear.mem_canonicalSubgroup_positivePointMap b.1
  have ha' := ha
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup (fam.isCompatible J).splitComponent] at ha'
  obtain ⟨a', ha', ha'eq⟩ := ha'
  let y : fam.positiveSplitComponent J := ⟨lₐ a, ⟨a', ha', by
    change map F (fam.A J).toGrp P (fam.a J ≫ fam.l J) a' = lₐ a
    rw [map_comp_apply_of_hom]
    exact congrArg lₐ ha'eq⟩⟩
  let K' := K.map (MulAut.conj t).toMonoidHom
  let μK := compactHaarProbability F G K hK.isCompact
  let c := compactConjugation K t
  let eK : K' ≃ₜ K := c.symm.toHomeomorph.trans (Homeomorph.mulLeft (⟨k, hk⟩ : K))
  let Δ := rationalNormOneSubgroup F M
  let eM := LeftCosetSpace.rightTranslateHomeomorph Δ b.2
  let e := eK.toMeasurableEquiv.prodCongr eM.toMeasurableEquiv
  let : (Measure.haar : Measure M₁).IsMulRightInvariant :=
    normOneHaarRightInvariant F M hM.smooth hM.connectedSpace
  have hpK : MeasurePreserving eK (compactHaarProbability F G K' hK') μK :=
    (measurePreserving_mul_left μK (⟨k, hk⟩ : K)).comp
      (measurePreserving_compactConjugation K t hK.isCompact hK')
  have hpM : MeasurePreserving eM (normOneRationalQuotientHaarMeasure F M)
      (normOneRationalQuotientHaarMeasure F M) :=
    measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure F M b.2
  refine ⟨a, ha, y, rfl, e, hpK.prod hpM, ?_⟩
  intro x E f hf z
  let m := z.2.out
  have heM : eM z.2 = LeftCosetSpace.mk Δ (m * b.2) := by
    rw [← Quotient.out_eq z.2]
    rfl
  have heK : (eK z.1).val = k * (c.symm z.1).val := rfl
  have hkt : z.1.val * t = t * (c.symm z.1).val := by
    have hc : t * (c.symm z.1).val * t⁻¹ = z.1.val :=
      congrArg Subtype.val (c.apply_symm_apply z.1)
    rw [← hc, inv_mul_cancel_right]
  have hprod : a * b.2.val = m₀ := d.apply_symm_apply _
  let v := x.val * lₐ (m.val * m₀)
  have hv : v * uₐ u * v⁻¹ ∈ (SubgroupFunctor.range (fam.iU J)).carrier _ :=
    (fam.isUnipotentRadical J).1.isNormal _ _ _ trivial ⟨u, rfl⟩
  obtain ⟨n, hn⟩ := SubgroupFunctor.mem_range.mp hv
  have hn' : uₐ n = v * uₐ u * v⁻¹ := hn
  have hng : map F U G (fam.iU J ≫ fam.p J) n ∈ Γ := Subgroup.mem_sup_left ⟨n, rfl⟩
  have hlevi (w : AdelicGroupPoints F M) : pₐ (lₐ w) = mₐ w := by
    rw [map_comp_apply_of_hom]
  have hvG : pₐ v = pₐ x.val * (mₐ m.val * mₐ m₀) := by
    simp only [v, map_mul, hlevi]
  have hcomm : Commute (mₐ a) (mₐ m.val) := by
    simpa only [show y.val = lₐ a from rfl, hlevi] using
      fam.commute_positiveSplitComponent_levi J y m.val
  have hy : pₐ (x * y).val * mₐ (m * b.2).val = pₐ v := by
    change pₐ (x.val * lₐ a) * mₐ (m.val * b.2.val) = _
    simp only [map_mul, hlevi]
    calc
      _ = pₐ x.val * ((mₐ a * mₐ m.val) * mₐ b.2.val) := by group
      _ = pₐ x.val * (mₐ m.val * mₐ m₀) := by
        rw [hcomm.eq, mul_assoc (mₐ m.val), ← map_mul, hprod]
      _ = pₐ v := hvG.symm
  have htp : t = (mₐ m₀ * pₐ (uₐ u)) * k := by
    rw [← ht, ← hfactor, map_mul, hlevi]
  have hnG : map F U G (fam.iU J ≫ fam.p J) n =
      pₐ v * pₐ (uₐ u) * (pₐ v)⁻¹ := by
    rw [map_comp_apply_of_hom, hn', map_mul, map_mul, map_inv]
  change f (pₐ x.val * mₐ m.val * z.1.val * t) =
    f (pₐ (x * y).val * mₐ ((eM z.2).out : M₁).val * (eK z.1).val)
  rw [heM, LeftCosetSpace.out_mk_of_invariant Δ
      (fun m : M₁ => f (pₐ (x * y).val * mₐ m.val * (eK z.1).val))
      (fam.leviSlice_invariant J hf (x * y) (eK z.1).val), hy]
  have he : pₐ x.val * mₐ m.val * z.1.val * t =
      map F U G (fam.iU J ≫ fam.p J) n * (pₐ v * (eK z.1).val) := by
    have htp' := congrArg (fun w : Gₐ => w * (c.symm z.1).val) htp
    rw [mul_assoc (pₐ x.val * mₐ m.val), hkt, htp', hnG, hvG, heK]
    group
  rw [he, hf _ hng]

private theorem integrable_normSq_slice_iff {K : Subgroup Gₐ}
    (hK : IsCompact (K : Set Gₐ)) {φ : Gₐ → ℂ}
    (hφinv : IsLeftInvariantUnder F G Γ φ)
    (hφeq : IsSplitComponentEquivariant (fam.p J) (fam.l J) φ) :
    Integrable (fun z : K × Q => ‖φ (fam.sliceArgument J 1 z)‖ ^ 2)
        (fam.squareIntegrablePairingMeasure K hK J) ↔
      Integrable (fun z : K × RestrictionSplitCentre.CanonicalQuotient F M =>
        InducedInnerProductSesquilinear.normWeight (fam.p J) (fam.l J) φ z.1.val z.2.out)
        ((compactHaarProbability F G K hK).prod (RestrictionSplitCentre.canonicalMeasure F M)) := by
  let hM := (fam.isCompatible J).levi.isConnectedReductive
  let := RestrictionSplitCentre.canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  let c := RestrictionSplitCentre.canonicalNormOneQuotientHomeomorph F M hM
  let e := (MeasurableEquiv.refl K).prodCongr c.toMeasurableEquiv
  let μK := compactHaarProbability F G K hK
  let ν := RestrictionSplitCentre.canonicalMeasure F M
  let : SFinite ν := by
    unfold ν RestrictionSplitCentre.canonicalMeasure RestrictionSplitCentre.quotientHaarMeasure
    infer_instance
  have he : MeasurePreserving e (fam.squareIntegrablePairingMeasure K hK J) (μK.prod ν) :=
    (MeasurePreserving.id μK).prod
      (RestrictionSplitCentre.measurePreserving_canonicalNormOneQuotientHomeomorph F M hM)
  let C := RestrictionSplitCentre.canonicalRationalSubgroup F M
  let W (k : K) := InducedInnerProductSesquilinear.normWeight (fam.p J) (fam.l J) φ k.val
  have hWinv (k : K) : ∀ a ∈ C, ∀ m, W k (a * m) = W k m :=
    fun a ha m => InducedInnerProductSesquilinear.canonicalRationalSubgroup_le_leftStabilizer
      (fun g hg => hφinv g (Subgroup.mem_sup_right hg)) hφeq k.val ha m
  have hEq : (fun z : K × Q => ‖φ (fam.sliceArgument J 1 z)‖ ^ 2) =
      (fun z : K × RestrictionSplitCentre.CanonicalQuotient F M => W z.1 z.2.out) ∘ e := by
    funext z
    have hc : c z.2 = LeftCosetSpace.mk C (z.2.out : M₁).val := by
      calc
        _ = c (LeftCosetSpace.mk (rationalNormOneSubgroup F M) z.2.out) :=
          congrArg c (Quotient.out_eq z.2).symm
        _ = _ := by
          rw [RestrictionSplitCentre.coe_canonicalNormOneQuotientHomeomorph,
            RestrictionSplitCentre.normOneToQuotient_mk]
    change ‖φ (fam.sliceArgument J 1 z)‖ ^ 2 = W z.1 (c z.2).out
    rw [hc, LeftCosetSpace.out_mk_of_invariant C (W z.1) (hWinv z.1)]
    simp only [sliceArgument, map_one, one_mul, W, InducedInnerProductSesquilinear.normWeight,
      parameterPower_map_of_mem_normOne _ (fam.l J) (z.2.out : M₁).property, norm_one,
      map_comp_apply_of_hom]
  rw [hEq]
  exact he.integrable_comp_emb e.measurableEmbedding

variable {d N : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}

/-- Infinite right translation carries the inducing form to the conjugate compact. -/
theorem isSquareIntegrableInducedForm_infiniteRightTranslate_of_maximalCompact
    {K : Subgroup Gₐ} (hK : IsIwasawaCompact (fam.p J) K)
    (a : InfiniteAdelicGroupPoints F G) (hKmax : IsMaximalCompactSubgroup F G K)
    (hK' : IsCompact ((K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom : Subgroup Gₐ) : Set Gₐ))
    {φ : Gₐ → ℂ} (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p J) (fam.iU J) (fam.l J) φ) :
    IsSquareIntegrableInducedForm (K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom) hK'
      rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) (fun g => φ (g * ofInfinite F G a)) := by
  let t := ofInfinite F G a
  let K' := K.map (MulAut.conj t).toMonoidHom
  have hK'max := hKmax.map_conj t
  have hinf : K'.comap (ofInfinite F G).toMonoidHom =
      (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [hK'max.comap_ofInfinite_eq_map_infinite, hKmax.comap_ofInfinite_eq_map_infinite]
    exact map_infinite_map_conj_ofInfinite K a
  let φ' (g : Gₐ) := φ (g * t)
  have hauto : IsAutomorphicFunctionOn F G hsmooth hcalc Γ (K'.comap (ofInfinite F G).toMonoidHom)
      rho φ' := hinf.symm ▸ hφ.1.infiniteRightTranslate hcalc a
  have heq : IsSplitComponentEquivariant (fam.p J) (fam.l J) φ' := by
    intro x hx g
    simp only [φ', mul_assoc, hφ.2.1 x hx]
  refine ⟨hauto, heq, (fam.integrable_normSq_slice_iff J hK' hauto.1 heq).mp ?_⟩
  have hInt := (fam.integrable_normSq_slice_iff J hK.isCompact hφ.1.1 hφ.2.1).mpr hφ.2.2
  obtain ⟨s, hs, y, hy, e, he, hArg⟩ := fam.exists_leviSliceTranslation J hK t hK'
  let f (z : K × Q) := ‖φ (fam.sliceArgument J y.val z)‖ ^ 2
  have hF : Integrable f (fam.squareIntegrablePairingMeasure K hK.isCompact J) := by
    have hEq : f = fun z =>
        ‖parameterPower F P (halfModulusParameter F P) (lₐ s)‖ ^ 2 *
          ‖φ (fam.sliceArgument J 1 z)‖ ^ 2 := by
      funext z
      simp only [f, sliceArgument, hy, map_one, one_mul, mul_assoc, map_comp_apply_of_hom,
        hφ.2.1 s hs, norm_mul, mul_pow]
    rw [hEq]
    exact hInt.const_mul _
  have hEq : (fun z : K' × Q => ‖φ' (fam.sliceArgument J 1 z)‖ ^ 2) = f ∘ e := by
    funext z
    simpa only [φ', f, Function.comp_apply, Subgroup.coe_one, one_mul] using
      hArg 1 (fun g => ‖φ g‖ ^ 2) (fun r hr g => by rw [hφ.1.1 r hr g]) z
  rw [hEq]
  exact he.integrable_comp_of_integrable hF

/-- Orthogonality at every Levi slice for the translated weak term implies
orthogonality for the original weak term and compact. -/
theorem isSquareIntegrableOrthogonal_of_infiniteRightTranslate
    {K : Subgroup Gₐ} (hK : IsIwasawaCompact (fam.p J) K)
    (a : InfiniteAdelicGroupPoints F G) (hKmax : IsMaximalCompactSubgroup F G K)
    (hK' : IsCompact ((K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom : Subgroup Gₐ) : Set Gₐ))
    {ψ : Gₐ → ℂ} (hψ : IsLeftInvariantUnder F G Γ ψ)
    (hOrth : fam.IsSquareIntegrableOrthogonal (K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom)
      hK' rho hsmooth hcalc J (fun g => ψ (g * ofInfinite F G a))) :
    fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc J ψ := by
  intro φ hφ x hx
  let t := ofInfinite F G a
  let K' := K.map (MulAut.conj t).toMonoidHom
  let φ' (g : Gₐ) := φ (g * t)
  let ψ' (g : Gₐ) := ψ (g * t)
  have hφ' := fam.isSquareIntegrableInducedForm_infiniteRightTranslate_of_maximalCompact J hK a hKmax hK' hφ
  obtain ⟨_, _, y, _, e, he, hArg⟩ := fam.exists_leviSliceTranslation J hK t hK'
  let x' : fam.positiveSplitComponent J := (⟨x, hx⟩ : fam.positiveSplitComponent J) * y⁻¹
  have hxy : x' * y = ⟨x, hx⟩ := inv_mul_cancel_right _ _
  let pairing := fam.squareIntegrablePairingIntegrand K J x φ ψ
  have hEq : fam.squareIntegrablePairingIntegrand K' J x'.val φ' ψ' = pairing ∘ e := by
    funext z
    simpa only [squareIntegrablePairingIntegrand, sliceArgument, pairing, φ', ψ',
      Function.comp_apply, hxy] using
      hArg x' (fun g => φ g * starRingEnd ℂ (ψ g))
        (fun r hr g => by rw [hφ.1.1 r hr g, hψ r hr g]) z
  obtain ⟨hInt, hZero⟩ := hOrth φ' hφ' x'.val x'.property
  rw [hEq] at hInt hZero
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mp hInt, ?_⟩
  exact (he.integral_comp' pairing).symm.trans hZero

/-- Infinite compact conjugation carries square-integrable inducing forms forward
and carries orthogonality of the translated Levi pairings back. -/
def LeviPairingCompactTranslationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p J) K)
    (b : InfiniteAdelicGroupPoints F G) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (hmax : IsMaximalCompactSubgroup F G K),
    let t := ofInfinite F G b
    let L := K.map (MulAut.conj t).toMonoidHom
    let hL := (hmax.map_conj t).1
    (∀ φ : AdelicGroupPoints F G → ℂ,
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ →
      IsSquareIntegrableInducedForm L hL rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J)
        (fun g => φ (g * t))) ∧
    ∀ ψ : AdelicGroupPoints F G → ℂ,
      IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)) ψ →
      fam.IsSquareIntegrableOrthogonal L hL rho hsmooth hcalc J (fun g => ψ (g * t)) →
      fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc J ψ

theorem leviPairingCompactTranslation : LeviPairingCompactTranslationStatement := by
  intro F _ _ G _ _ _ fam J K hK b N d rho hsmooth hcalc hmax t L hL
  exact ⟨fun _ hφ => fam.isSquareIntegrableInducedForm_infiniteRightTranslate_of_maximalCompact J hK b hmax hL hφ,
    fun _ hψ hOrth => fam.isSquareIntegrableOrthogonal_of_infiniteRightTranslate J hK b hmax hL hψ hOrth⟩

end Langlands.Global.StandardParabolicFamily
