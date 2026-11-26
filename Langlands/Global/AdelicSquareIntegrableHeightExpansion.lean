import Langlands.Automorphic.OperatorDeterminantSliceMeasure
import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.AdelicSquareIntegrableInducedSubmodule
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # Orthogonality of finite square-integrable expansions on height slices -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν

/-- Coverage by the minimal parabolic and a compact subgroup gives coverage by each standard
parabolic and the same compact subgroup. -/
theorem isIwasawaCompact_of_bot {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p fam.bot) K) (J : Idx) : IsIwasawaCompact (fam.p J) K := by
  refine ⟨hK.isCompact, Set.eq_univ_of_forall fun g => ?_⟩
  obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
  have hle : SubgroupFunctor.range (fam.p fam.bot) ≤ SubgroupFunctor.range (fam.p J) :=
    (fam.le_iff_range_le fam.bot J).mp (Set.empty_subset _)
  obtain ⟨w, hw⟩ : ∃ w : AdelicGroupPoints F (fam.P J),
      map F (fam.P J) G (fam.p J) w = map F (fam.P fam.bot) G (fam.p fam.bot) q :=
    hle _ (SubgroupFunctor.mem_range.mpr ⟨q, rfl⟩)
  exact ⟨_, ⟨w, hw⟩, k, hk, rfl⟩

variable {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

variable (J : StandardIndex F G fam.i fam.ν)

variable [IsClosedImmersion (fam.p J).hom.hom.left]
  (hK : IsIwasawaCompact (fam.p J) K)

/-- Finite sums of `A²_P` forms with scalar coefficients depending on the Iwasawa height.
This includes the exponential-polynomial expansions in Delorme, Lemma 3.10 (i). -/
def HasSquareIntegrableHeightExpansion (ψ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ (n : ℕ) (v : Fin n → AdelicGroupPoints F G → ℂ)
    (c : Fin n → RealCharacterDual F (fam.P J) → ℂ),
    (∀ i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) (v i)) ∧
      ∀ g, ψ g = ∑ i, c i (hK.height g) * v i g

omit [IsClosedImmersion (fam.p J).hom.hom.left] in
private theorem exists_canonical_preimage_of_positive {x : AdelicGroupPoints F (fam.P J)}
    (hx : x ∈ fam.positiveSplitComponent J) :
    ∃ a ∈ RestrictionSplitCentre.canonicalSubgroup F (fam.M J), map F (fam.M J) (fam.P J) (fam.l J) a = x := by
  obtain ⟨a, ha, hax⟩ := hx
  let t := map F (fam.A J).toGrp (fam.M J) (fam.a J) a
  refine ⟨t, ?_, ?_⟩
  · rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup (fam.isCompatible J).splitComponent]
    exact ⟨a, ha, rfl⟩
  · rw [← map_comp_apply_of_hom]
    exact hax

private def slicePoint (x : AdelicGroupPoints F (fam.P J)) (k : K) (m : normOneSubgroup F (fam.M J)) :
    AdelicGroupPoints F G :=
  map F (fam.P J) G (fam.p J) x * map F (fam.M J) G (fam.l J ≫ fam.p J) (m : AdelicGroupPoints F (fam.M J)) * k.val

private theorem slicePoint_height (x : AdelicGroupPoints F (fam.P J)) (k : K) (m : normOneSubgroup F (fam.M J)) :
    hK.height (fam.slicePoint J x k m) = characterLog F (fam.P J) x := by
  rw [slicePoint, mul_assoc, hK.height_map_mul, map_comp_apply_of_hom,
    hK.height_map_mul, InducedInnerProductIntegrable.characterLog_map_of_mem_normOne (fam.l J) m.property,
    hK.height_of_mem k.property, add_zero, add_zero]

omit [IsClosedImmersion (fam.p J).hom.hom.left] in
include hK in
private theorem exists_radical_slice (g : AdelicGroupPoints F G) :
    ∃ (u : AdelicGroupPoints F (fam.U J)) (x : AdelicGroupPoints F (fam.P J)) (_ : x ∈ fam.positiveSplitComponent J)
      (k : K) (m : normOneSubgroup F (fam.M J)),
      g = map F (fam.U J) G (fam.iU J ≫ fam.p J) u * fam.slicePoint J x k m := by
  obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  let : IsIso (subgroupMultiplication (fam.l J) (fam.iU J)) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication r fam.connectedReductive
      (fam.isUnipotentRadical J)
  let u : AdelicGroupPoints F (fam.U J) := radicalComponent (fam.l J) (fam.iU J) q⁻¹
  let m : AdelicGroupPoints F (fam.M J) := leviComponent (fam.l J) (fam.iU J) q⁻¹
  have hq : q = map F (fam.U J) (fam.P J) (fam.iU J) u⁻¹ * map F (fam.M J) (fam.P J) (fam.l J) m⁻¹ := by
    have h : map F (fam.M J) (fam.P J) (fam.l J) m *
        map F (fam.U J) (fam.P J) (fam.iU J) u = q⁻¹ :=
      leviComponent_mul_radicalComponent (fam.l J) (fam.iU J) q⁻¹
    simpa only [mul_inv_rev, map_inv, inv_inv] using (congrArg Inv.inv h).symm
  let e := RestrictionSplitCentre.intrinsicNormOneDecomposition F (fam.M J) (fam.isCompatible J).levi.isConnectedReductive
  let z := e.symm m⁻¹
  let a : AdelicGroupPoints F (fam.M J) := PositiveRealTorus.positivePointMap F (fam.M J)
    (RestrictionSplitCentre.canonicalTorus F (fam.M J)) (RestrictionSplitCentre.canonicalComponent F (fam.M J)) z.1
  have hmn : a * (z.2 : AdelicGroupPoints F (fam.M J)) = m⁻¹ := e.apply_symm_apply _
  have ha : a ∈ RestrictionSplitCentre.canonicalSubgroup F (fam.M J) := by
    rw [RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup]
    exact ⟨z.1.val, z.1.property, rfl⟩
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup (fam.isCompatible J).splitComponent] at ha
  obtain ⟨b, hb, hba⟩ := ha
  refine ⟨u⁻¹, map F (fam.M J) (fam.P J) (fam.l J) a, ⟨b, hb, ?_⟩, ⟨k, hk⟩, z.2, ?_⟩
  · change map F (fam.A J).toGrp (fam.P J) (fam.a J ≫ (fam.l J)) b = map F (fam.M J) (fam.P J) (fam.l J) a
    rw [map_comp_apply_of_hom]
    exact congrArg (map F (fam.M J) (fam.P J) (fam.l J)) hba
  · rw [hq, ← hmn, slicePoint]
    simp only [map_mul, map_comp_apply_of_hom]
    group

omit [IsClosedImmersion (fam.p J).hom.hom.left] in
private theorem slice_vanishes_of_pairing {ψ φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ)
    (hOrth : fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc J ψ)
    {x : AdelicGroupPoints F (fam.P J)} (hx : x ∈ fam.positiveSplitComponent J)
    (hMatch : ∀ (k : K) (m : normOneSubgroup F (fam.M J)), ψ (fam.slicePoint J x k m) = φ (fam.slicePoint J x k m)) :
    ∀ (k : K) (m : normOneSubgroup F (fam.M J)), ψ (fam.slicePoint J x k m) = 0 := by
  let Γ := rationalNormOneSubgroup F (fam.M J)
  let measure := fam.squareIntegrablePairingMeasure K hK.isCompact J
  let f (k : K) (m : normOneSubgroup F (fam.M J)) := φ (fam.slicePoint J x k m)
  let w (z : K × NormOneRationalQuotient F (fam.M J)) : ℝ := ‖f z.1 z.2.out‖ ^ 2
  have hfc : Continuous (fun z : K × normOneSubgroup F (fam.M J) => f z.1 z.2) := by
    exact hφ.1.2.1.1.comp ((continuous_const.mul ((map F (fam.M J) G (fam.l J ≫ fam.p J)).continuous.comp
      (continuous_subtype_val.comp continuous_snd))).mul (continuous_subtype_val.comp continuous_fst))
  have hfinv (k : K) : ∀ r ∈ Γ, ∀ m, f k (r * m) = f k m := by
    obtain ⟨a, ha, rfl⟩ := fam.exists_canonical_preimage_of_positive J hx
    have hf (n : normOneSubgroup F (fam.M J)) : f k n =
        parameterPower F (fam.P J) (halfModulusParameter F (fam.P J)) (map F (fam.M J) (fam.P J) (fam.l J) a) *
          φ (map F (fam.P J) G (fam.p J) (map F (fam.M J) (fam.P J) (fam.l J) (n : AdelicGroupPoints F (fam.M J))) * k.val) := by
      dsimp only [f, slicePoint]
      rw [map_comp_apply_of_hom, mul_assoc, hφ.2.1 a ha]
    intro r hr m
    have hp : (r : AdelicGroupPoints F (fam.M J)) ∈ rationalSubgroup F (fam.M J) := by
      obtain ⟨t, ht⟩ := hr
      exact ⟨t, congrArg Subtype.val ht⟩
    rw [hf, hf]
    change _ * φ (map F (fam.P J) G (fam.p J) (map F (fam.M J) (fam.P J) (fam.l J) ((r : AdelicGroupPoints F (fam.M J)) * m.val)) * k.val) = _
    rw [InducedInnerProductIntegrable.form_rational_mul hφ.1.1 hp]
  have hwc : Continuous w := (LeftCosetSpace.continuous_out_of_invariant Γ f hfc hfinv).norm.pow 2
  have hweq : fam.squareIntegrablePairingIntegrand K J x φ ψ = fun z => (w z : ℂ) := by
    funext z
    change f z.1 z.2.out * starRingEnd ℂ (ψ (fam.slicePoint J x z.1 z.2.out)) = _
    rw [hMatch]
    simpa only [w, Complex.ofReal_pow] using Complex.mul_conj' (f z.1 z.2.out)
  obtain ⟨hi, hz⟩ := hOrth φ hφ x hx
  rw [hweq] at hi hz
  have hwi : Integrable w measure := by
    exact hi.re
  have hwz : ∫ z, w z ∂measure = 0 := by
    rwa [integral_complex_ofReal, Complex.ofReal_eq_zero] at hz
  have hae : w =ᵐ[measure] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hwi).mp hwz
  let : (normOneRationalQuotientHaarMeasure F (fam.M J)).IsOpenPosMeasure :=
    LeftCosetSpace.isOpenPosMeasure_discreteQuotientMeasure Γ (isDiscrete_rationalNormOneSubgroup F (fam.M J))
      Measure.haar
  have : measure.IsOpenPosMeasure := by dsimp only [measure, squareIntegrablePairingMeasure]; infer_instance
  have hw : w = 0 := Measure.eq_of_ae_eq hae hwc continuous_const
  intro k m
  have h := congrFun hw (k, LeftCosetSpace.mk Γ m)
  change ‖f k (LeftCosetSpace.mk Γ m).out‖ ^ 2 = 0 at h
  rw [LeftCosetSpace.out_mk_of_invariant Γ (f k) (hfinv k)] at h
  exact (hMatch k m).trans (norm_eq_zero.mp (eq_zero_of_pow_eq_zero h))

/-- Testing a finite square-integrable height expansion on every split-component slice forces
pointwise vanishing. On the slice through `x`, freeze each coefficient at `H_P(x)` and test with
the resulting finite linear combination in `A²_P`. -/
theorem eq_zero_of_squareIntegrableHeightExpansion_of_orthogonal {ψ : AdelicGroupPoints F G → ℂ}
    (hψ : fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hK ψ)
    (hOrth : fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc J ψ) : ψ = 0 := by
  obtain ⟨n, v, c, hv, hsum⟩ := hψ
  funext g
  obtain ⟨u, x, hx, k, m, rfl⟩ := fam.exists_radical_slice J hK g
  have hu : map F (fam.U J) G (fam.iU J ≫ fam.p J) u ∈ parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J) :=
    Subgroup.mem_sup_left ⟨u, rfl⟩
  have hh : hK.height (map F (fam.U J) G (fam.iU J ≫ fam.p J) u * fam.slicePoint J x k m) =
      hK.height (fam.slicePoint J x k m) := by
    rw [map_comp_apply_of_hom]
    exact hK.height_unipotent_mul (fam.isUnipotentRadical J).1.isUnipotent (fam.iU J) u _
  have hΓ : ψ (map F (fam.U J) G (fam.iU J ≫ fam.p J) u * fam.slicePoint J x k m) = ψ (fam.slicePoint J x k m) := by
    rw [hsum, hsum, hh]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hv i).1.1 _ hu _]
  rw [hΓ]
  let φ : AdelicGroupPoints F G → ℂ := ∑ i, c i (characterLog F (fam.P J) x) • v i
  have hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ :=
    (squareIntegrableInducedForms (fam.p J) (fam.l J) hK.isCompact rho hsmooth hcalc (fam.iU J)).sum_mem
      (fun i _ => (squareIntegrableInducedForms (fam.p J) (fam.l J) hK.isCompact rho hsmooth hcalc (fam.iU J)).smul_mem _ (hv i))
  have hMatch (k' : K) (m' : normOneSubgroup F (fam.M J)) :
      ψ (fam.slicePoint J x k' m') = φ (fam.slicePoint J x k' m') := by
    rw [hsum, fam.slicePoint_height J hK]
    simp only [φ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact fam.slice_vanishes_of_pairing rho hsmooth hcalc J hK hφ hOrth hx hMatch k m

end Langlands.Global.StandardParabolicFamily
