import Langlands.Automorphic.GroupSchemeAutomorphicRightTranslation
import Langlands.Global.AdelicEisensteinConjugateCompactProof
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicSquareIntegrableHeightExpansion
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Square-integrable height expansions under infinite compact conjugation -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints InducedInnerProductIntegrable Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

variable {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hK : IsIwasawaCompact (fam.p J) K) (xinf : InfiniteAdelicGroupPoints F G)

local notation "A" => ofInfinite F G xinf
local notation "L" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (ofInfinite F G xinf))) K

/-- Right translation by an infinite adelic point carries an inducing form to the space for
its conjugate compact. The shift has a fixed effect on the Levi quotient coordinate. -/
theorem isSquareIntegrableInducedForm_infiniteRightTranslate
    (hL : IsCompact (L : Set (AdelicGroupPoints F G)))
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p J) (fam.iU J) (fam.l J) φ) :
    IsSquareIntegrableInducedForm L hL rho hsmooth hcalc
      (fam.p J) (fam.iU J) (fam.l J) (fun g => φ (g * A)) := by
  have hKinf : (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj xinf).toMonoidHom =
      Subgroup.comap (ofInfinite F G).toMonoidHom L := by
    ext t
    change t ∈ (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj xinf).toMonoidHom ↔
      ofInfinite F G t ∈ L
    simp only [Subgroup.mem_map_equiv, Subgroup.mem_comap, MulAut.conj_symm_apply, map_mul, map_inv]
    rfl
  refine ⟨hKinf ▸ hφ.1.infiniteRightTranslate hcalc xinf, fun b hb g => ?_, ?_⟩
  · dsimp only
    rw [mul_assoc, hφ.2.1 b hb]
  let P := fam.P J
  let M := fam.M J
  let U := fam.U J
  let ml := map F M P (fam.l J)
  let pg := map F P G (fam.p J)
  let up := map F U P (fam.iU J)
  let Γ := RestrictionSplitCentre.canonicalRationalSubgroup F M
  let measureM := RestrictionSplitCentre.canonicalMeasure F M
  let : SFinite measureM := by
    dsimp only [measureM, RestrictionSplitCentre.canonicalMeasure, RestrictionSplitCentre.quotientHaarMeasure]
    infer_instance
  let δ := modulusParameter F P
  let weight (k : AdelicGroupPoints F G) (m : AdelicGroupPoints F M) :=
    ‖parameterPower F P (-δ) (ml m)‖ * ‖φ (pg (ml m) * k)‖ ^ 2
  have hinv (k : AdelicGroupPoints F G) : ∀ b ∈ Γ, ∀ m, weight k (b * m) = weight k m := by
    apply LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
      (Δ := rationalSubgroup F M)
    · intro b hb m
      have hcancel : ‖parameterPower F P (-δ) (ml b)‖ *
          ‖parameterPower F P (halfModulusParameter F P) (ml b)‖ ^ 2 = 1 := by
        rw [pow_two, ← mul_assoc, ← norm_mul, ← parameterPower_add, ← norm_mul, ← parameterPower_add,
          neg_modulus_add_half_add_half, parameterPower_zero, norm_one]
      dsimp only [weight]
      rw [form_canonical_mul hφ.2.1 hb, map_mul, parameterPower_mul, norm_mul, norm_mul, mul_pow,
        mul_mul_mul_comm, hcancel, one_mul]
    · intro b hb m
      dsimp only [weight]
      rw [parameterPower_map_mul_left _ (fam.l J) (rationalSubgroup_le_normOneSubgroup F M hb),
        form_rational_mul hφ.1.1 hb]
  obtain ⟨q, k, hk, hA⟩ := hK.exists_eq A
  change pg q * k = A at hA
  let eP : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  let : IsIso (subgroupMultiplication (fam.l J) (fam.iU J)) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication eP fam.connectedReductive
      (fam.isUnipotentRadical J)
  let m₀ := leviComponent (fam.l J) (fam.iU J) q
  let u := radicalComponent (fam.l J) (fam.iU J) q
  have hsplit : ml m₀ * up u = q := leviComponent_mul_radicalComponent (fam.l J) (fam.iU J) q
  let e : K ≃* L := (MulAut.conj A).subgroupMap K
  let κ := compactHaarProbability F G K hK.isCompact
  let κ' := compactHaarProbability F G L hL
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let k₀ : K := ⟨k, hk⟩
  let rK : L → K := fun v => k₀ * e.symm v
  let rM := LeftCosetSpace.rightTranslate Γ m₀
  have hconj : MeasurePreserving e.symm κ' κ := by
    have he : Continuous e.symm := by
      apply Continuous.subtype_mk
      change Continuous (fun v : L => A⁻¹ * v.val * A)
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    exact MonoidHom.measurePreserving (f := e.symm.toMonoidHom) he e.symm.surjective
      (show κ' Set.univ = κ Set.univ by rw [measure_univ, measure_univ])
  have hKmeasure : MeasurePreserving rK κ' κ := (measurePreserving_mul_left κ k₀).comp hconj
  have hMmeasure : MeasurePreserving rM measureM measureM :=
    RestrictionSplitCentre.canonicalMeasure_rightInvariant F M centralSplitTorusCharacter
      (fam.isCompatible J).levi.isConnectedReductive m₀
  have hSource : Integrable (fun z : K × RestrictionSplitCentre.CanonicalQuotient F M =>
      weight z.1.val z.2.out) (κ.prod measureM) := hφ.2.2
  have hPres : MeasurePreserving (Prod.map rK rM) (κ'.prod measureM) (κ.prod measureM) := by
    refine ⟨hKmeasure.measurable.prodMap hMmeasure.measurable, ?_⟩
    rw [← Measure.map_prod_map _ _ hKmeasure.measurable hMmeasure.measurable,
      hKmeasure.map_eq, hMmeasure.map_eq]
  have hComp := (hPres.integrable_comp_of_integrable hSource).const_mul
    ‖parameterPower F P δ (ml m₀)‖
  convert hComp using 1
  funext z
  let m := z.2.out
  have hr : rM z.2 = LeftCosetSpace.mk Γ (m * m₀) := by
    change LeftCosetSpace.rightTranslate Γ m₀ z.2 = _
    rw [← Quotient.out_eq z.2]
    rfl
  have hU : ml (m * m₀) * up u * (ml (m * m₀))⁻¹ ∈
      (SubgroupFunctor.range (fam.iU J)).carrier _ :=
    (fam.isUnipotentRadical J).1.isNormal _ _ _ trivial ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hU
  have hvP : up v = ml (m * m₀) * up u * (ml (m * m₀))⁻¹ := hv
  have hprod : ml m * q = up v * ml (m * m₀) := by
    rw [hvP, inv_mul_cancel_right, ← hsplit, map_mul, mul_assoc]
  have hvG : map F U G (fam.iU J ≫ fam.p J) v ∈
      parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J) :=
    Subgroup.mem_sup_left ⟨v, rfl⟩
  have hcompact : z.1.val * A = A * (e.symm z.1).val := by
    change z.1.val * A = A * (A⁻¹ * z.1.val * A)
    group
  have hvalue : φ ((pg (ml m) * z.1.val) * A) = φ (pg (ml (m * m₀)) * (rK z.1).val) := by
    calc
      _ = φ (pg (ml m * q) * (rK z.1).val) := by
        change φ ((pg (ml m) * z.1.val) * A) = φ (pg (ml m * q) * (k * (e.symm z.1).val))
        rw [mul_assoc, hcompact]
        refine (congrArg (fun y => φ (pg (ml m) * (y * (e.symm z.1).val))) hA.symm).trans ?_
        rw [map_mul]
        congr 1
        group
      _ = _ := by
        rw [hprod, map_mul, ← map_comp_apply_of_hom, mul_assoc]
        exact hφ.1.1 _ hvG _
  change ‖parameterPower F P (-δ) (ml m)‖ * ‖φ ((pg (ml m) * z.1.val) * A)‖ ^ 2 =
    ‖parameterPower F P δ (ml m₀)‖ * weight (rK z.1).val (rM z.2).out
  rw [hvalue, hr, LeftCosetSpace.out_mk_of_invariant Γ _ (hinv _)]
  dsimp only [weight]
  rw [map_mul ml m m₀, parameterPower_mul, norm_mul]
  have hmod : ‖parameterPower F P δ (ml m₀)‖ * ‖parameterPower F P (-δ) (ml m₀)‖ = 1 := by
    rw [← norm_mul, ← parameterPower_add, add_neg_cancel, parameterPower_zero, norm_one]
  rw [← mul_assoc, mul_left_comm ‖parameterPower F P δ (ml m₀)‖, mul_assoc, hmod, one_mul]

/-- Transport a height expansion by the same infinite right translation of all its forms.
Each scalar coefficient is shifted by the height of the translating element. -/
theorem HasSquareIntegrableHeightExpansion.infiniteRightTranslate
    [IsClosedImmersion (fam.p J).hom.hom.left]
    (hL : IsIwasawaCompact (fam.p J) L) {ψ : AdelicGroupPoints F G → ℂ}
    (hψ : fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hK ψ) :
    fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hL (fun g => ψ (g * A)) := by
  obtain ⟨n, v, c, hv, heq⟩ := hψ
  refine ⟨n, fun i g => v i (g * A), fun i H => c i (H + hK.height A),
    fun i => fam.isSquareIntegrableInducedForm_infiniteRightTranslate J rho hsmooth hcalc hK xinf hL.isCompact
      (hv i), ?_⟩
  intro g
  have hheight : hK.height (g * A) = hL.height g + hK.height A := by
    obtain ⟨q, l, hl, rfl⟩ := hL.exists_eq g
    obtain ⟨k, hk, hkl⟩ := hl
    have he : l * A = A * k := by
      rw [← hkl]
      change (A * k * A⁻¹) * A = _
      group
    rw [mul_assoc, he, ← mul_assoc, hK.height_mul_right _ hk, hK.height_map_mul,
      hL.height_eq (show l ∈ L from ⟨k, hk, hkl⟩) rfl]
  simpa only [hheight] using heq (g * A)

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- Infinite right translation transports a finite square-integrable height expansion to the
conjugate Iwasawa compact. -/
def AdelicSquareIntegrableHeightConjugateCompactStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p J) K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (xinf : InfiniteAdelicGroupPoints F G),
    ∃ hL : IsIwasawaCompact (fam.p J) (K.map (MulAut.conj (ofInfinite F G xinf)).toMonoidHom),
      haveI : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
      ∀ ψ : AdelicGroupPoints F G → ℂ,
        fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hK ψ →
        fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hL
          (fun g => ψ (g * ofInfinite F G xinf))

theorem adelicSquareIntegrableHeightConjugateCompact :
    AdelicSquareIntegrableHeightConjugateCompactStatement := by
  intro F _ _ G _ _ _ fam J K hK N d rho hsmooth hcalc xinf
  let g := ofInfinite F G xinf
  let hL : IsIwasawaCompact (fam.p J) (K.map (MulAut.conj g).toMonoidHom) := by
    simpa only [inv_inv] using hK.conjInv g⁻¹
  refine ⟨hL, fun ψ hψ => ?_⟩
  let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
  exact StandardParabolicFamily.HasSquareIntegrableHeightExpansion.infiniteRightTranslate
    fam J rho hsmooth hcalc hK xinf hL hψ

end Langlands.Global
