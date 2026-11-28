import Langlands.Global.AdelicRelativeTruncationCoordinates
import Langlands.Global.AdelicWeakConstantTermRightTranslation
import Langlands.Global.AdelicWeakConstantTermDirectness
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicPositiveTorusSplitComponentProof
import Langlands.Global.AdelicSplitCentreUnitaryCharacter
import Langlands.GroupScheme.Rational.NestedSplitComponentFactorization
import Langlands.GroupScheme.Rational.RelativeCentralDirectionsProof

/-! # Orthogonality on relative Levi slices -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus
  RestrictionSplitCentre Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "P" => fam.P J
local notation "Z" => canonicalTorus F G
local notation "iZ" => canonicalComponent F G

attribute [local instance] isClosedImmersion_p

private theorem characterLog_eq_splitDual_of_torus
    (x : AdelicGroupPoints F P) (t : AdelicGroupPoints F fam.T.toGrp)
    (v : V fam.T) (ht : characterLog F fam.T.toGrp t = cocharacterFunctional v)
    (hx : map F P G (fam.p J) x = map F fam.T.toGrp G fam.i t) :
    characterLog F P x = fam.splitDual J v := by
  let j := fam.torus J ≫ fam.l J
  have he : map F P G (fam.p J) (map F fam.T.toGrp P j t) = map F P G (fam.p J) x := by
    rw [← map_comp_apply_of_hom, Category.assoc, fam.torus_comp, hx]
  rw [← (isClosedEmbedding_map F P G (fam.p J)).injective he, characterLog_map, ht]
  apply AddMonoidHom.ext
  intro χ
  change pair fam.T (1 ⊗ₜ[ℤ] characterRestrict j χ) v =
    pair fam.T (fam.chamberEmbedding J (1 ⊗ₜ[ℤ] χ)) v
  rfl

/-- Every positive split-component point is the product of a lifted positive central
point and a positive point whose logarithm is a sum of the relative coroots.
The half-modulus is trivial on the lifted central factor. -/
theorem positiveSplitComponent_factor_coroot (x : fam.positiveSplitComponent J) :
    ∃ (a y : fam.positiveSplitComponent J) (z : canonicalSubgroup F G)
      (c : fam.relativeSimpleRoots J → ℝ),
      a * y = x ∧ map F P G (fam.p J) a.val = z.val ∧ fam.halfModulus J a.val = 1 ∧
      characterLog F P y.val = ∑ α, c α • fam.relativeCoroot J α := by
  let hZ := isSplitComponent_canonicalComponent F G
  have hZT : IsSplitTorus (Z).toGrp := hZ.isCentralSplitTorus.isSplitSubtorus.1
  let : IsAffineHom (Z).toGrp.X.hom := hZT.isAffineHom
  let : IsAffine (Z).toGrp.X.left := isAffine_of_isAffineHom (Z).toGrp.X.hom
  obtain ⟨u, _, hu⟩ := x.property
  change map F (fam.A J).toGrp P (fam.a J ≫ fam.l J) u = x.val at hu
  let t := map F (fam.A J).toGrp fam.T.toGrp (CommGroupScheme.groupHom (fam.f J)) u
  have hxt : map F P G (fam.p J) x.val = map F fam.T.toGrp G fam.i t := by
    rw [← hu, ← map_comp_apply_of_hom (fam.a J ≫ fam.l J) u, Category.assoc]
    dsimp only [t]
    rw [← map_comp_apply_of_hom, (fam.isCompatible J).factor_comp]
  obtain ⟨v, hv⟩ := exists_cocharacterFunctional_eq fam.maximalSplit.isSplitSubtorus.1
    (characterLog F fam.T.toGrp t)
  have hxLog := fam.characterLog_eq_splitDual_of_torus J x.val t v hv.symm hxt
  let d := ArthurRelative.toCorootSpan fam.connectedReductive fam.maximalSplit fam.coroots v
  have hd : v - d.val ∈ relativeCentralDirections fam.i :=
    ArthurRelative.sub_toCorootSpan_mem fam.connectedReductive fam.maximalSplit fam.coroots v
  obtain ⟨f, hf, _, _, hRange, _, _⟩ := (GroupScheme.relativeCentralDirections.2 F G
    fam.connectedReductive fam.T fam.i fam.maximalSplit).2.2.2.2.2.2 Z iZ hZ
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (hRange.symm ▸ hd)
  obtain ⟨b, hb, hbLog⟩ := exists_characterLog_eq hZT (cocharacterFunctional w)
  let tZ := map F (Z).toGrp fam.T.toGrp (CommGroupScheme.groupHom f) b
  have htZ : characterLog F fam.T.toGrp tZ = cocharacterFunctional (v - d.val) := by
    rw [characterLog_map, hbLog, ← cocharacterFunctional_cocharacterMapReal, hw]
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  have hid : IsClosedSubgroup (𝟙 G) := by
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  obtain ⟨j, hj⟩ := r.exists_intermediateSplitComponentFactor (𝟙 G) hid
    (fam.l J ≫ fam.p J) (Category.comp_id _) iZ hZ.isCentralSplitTorus.isCentral hZT
  let e := j ≫ fam.a J ≫ fam.l J
  have he : e ≫ fam.p J = iZ := by simpa only [e, Category.assoc] using hj
  let A := map F (Z).toGrp P e b
  have hA : A ∈ fam.positiveSplitComponent J := by
    refine ⟨map F (Z).toGrp (fam.A J).toGrp j b,
      map_intrinsicSubgroup_le F Z (fam.A J) (Additive.ofMul j) ⟨b, hb, rfl⟩, ?_⟩
    change map F (fam.A J).toGrp P (fam.a J ≫ fam.l J)
      (map F (Z).toGrp (fam.A J).toGrp j b) = A
    rw [← map_comp_apply_of_hom]
  let a : fam.positiveSplitComponent J := ⟨A, hA⟩
  let y := a⁻¹ * x
  have hxy : a * y = x := by simp [y, ← mul_assoc]
  have haz : map F P G (fam.p J) a.val = map F (Z).toGrp G iZ b := by
    change map F P G (fam.p J) (map F (Z).toGrp P e b) = _
    rw [← map_comp_apply_of_hom, he]
  have htmap : map F fam.T.toGrp G fam.i tZ = map F (Z).toGrp G iZ b := by
    dsimp only [tZ]
    rw [← map_comp_apply_of_hom, hf]
  have haLog := fam.characterLog_eq_splitDual_of_torus J a.val tZ (v - d.val) htZ
    (haz.trans htmap.symm)
  have hz : map F (Z).toGrp G iZ b ∈ canonicalSubgroup F G := by
    rw [canonicalSubgroup_eq_imageSubgroup]
    exact ⟨b, hb, rfl⟩
  let : Mono (fam.p J).hom.hom := Over.mono_of_mono_left _
  have hhalf : fam.halfModulus J a.val = 1 :=
    parameterPower_halfModulus_map_of_isCentral (p := fam.p J) (he.symm ▸ hZ.isCentralSplitTorus.isCentral) b
  refine ⟨a, y, ⟨_, hz⟩, fam.weightCoordinate J d.val, hxy, haz, hhalf, ?_⟩
  have hlog := congrArg (fun p : fam.positiveSplitComponent J => characterLog F P p.val) hxy
  change characterLog F P (a.val * y.val) = characterLog F P x.val at hlog
  rw [characterLog_mul, haLog, hxLog] at hlog
  have hyLog : characterLog F P y.val = fam.splitDual J d.val := by
    apply add_left_cancel (a := fam.splitDual J (v - d.val))
    rw [hlog, ← map_add, sub_add_cancel]
  rw [hyLog, fam.splitDual_eq_sum_relativeCoroot J d.property]

variable {N d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {rho : MatrixRepresentation G (Fin N)}
  {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}

private theorem hasExponent_smul {lam : ComplexCharacterParameter F P}
    {f : AdelicGroupPoints F G → ℂ} (hf : fam.HasExponent J lam f) (b : ℂ) :
    fam.HasExponent J lam (b • f) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, fun g => ?_⟩
  obtain ⟨p, hp, h⟩ := hn g
  refine ⟨b • p, (polynomialFunctions _ n).smul_mem b hp, fun x hx => ?_⟩
  simp only [normalizedAction, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [← h x hx]
  ring

/-- A scalar right-translation law of the form passes to its weak constant term.
Apply this to the ambient split-central character by centrality. -/
theorem IsWeakConstantTerm.rightTranslate_eq_smul
    {Φ ψ : AdelicGroupPoints F G → ℂ} (hψ : fam.IsWeakConstantTerm hsmooth Kinf rho J Φ ψ)
    (a : AdelicGroupPoints F G) (b : ℂ) (hΦ : ∀ g, Φ (g * a) = b * Φ g) :
    ∀ g, ψ (g * a) = b * ψ g := by
  classical
  obtain ⟨s, f, hdec, hsum⟩ := hψ
  have hΦ' : (fun g => Φ (g * a)) = b • Φ := funext hΦ
  have hCT (g : AdelicGroupPoints F G) : fam.constantTerm J Φ (g * a) = b * fam.constantTerm J Φ g := by
    unfold constantTerm
    rw [← subgroupConstantTerm_rightTranslate, hΦ', subgroupConstantTerm_smul]
    rfl
  have hEq : (∑ lam ∈ s, fun g => f lam (g * a)) = ∑ lam ∈ s, b • f lam := by
    funext g
    have h (x : AdelicGroupPoints F G) : fam.constantTerm J Φ x = ∑ lam ∈ s, f lam x := by
      simpa only [Finset.sum_apply] using congrFun hdec.sum_eq x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← h, hCT]
  have hFiltered := fam.sum_filter_eq_of_hasExponent J s s (fun lam g => f lam (g * a))
    (fun lam => b • f lam)
    (fun lam h => (hdec.exponent lam h).rightTranslate fam a)
    (fun lam h => fam.hasExponent_smul J (hdec.exponent lam h) b)
    hEq (fun lam => parameterRealPart F P lam = 0)
  intro g
  simpa only [hsum, unitaryExponentSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    using congrFun hFiltered g

private theorem inducing_mul_at_central_lift
    {φ : AdelicGroupPoints F G → ℂ} (hφ : IsSplitComponentEquivariant (fam.p J) (fam.l J) φ)
    {a : AdelicGroupPoints F P} (ha : a ∈ fam.positiveSplitComponent J)
    (hhalf : fam.halfModulus J a = 1) (g : AdelicGroupPoints F G) :
    φ (map F P G (fam.p J) a * g) = φ g := by
  obtain ⟨t, ht, rfl⟩ := ha
  change fam.halfModulus J (map F (fam.A J).toGrp P (fam.a J ≫ fam.l J) t) = 1 at hhalf
  change φ (map F P G (fam.p J) (map F (fam.A J).toGrp P (fam.a J ≫ fam.l J) t) * g) = φ g
  have htM : map F (fam.A J).toGrp (fam.M J) (fam.a J) t ∈ canonicalSubgroup F (fam.M J) := by
    rw [← imageSubgroup_eq_canonicalSubgroup (fam.isCompatible J).splitComponent]
    exact ⟨t, ht, rfl⟩
  have htP := map_comp_apply_of_hom (F := F) (p := fam.l J) (fam.a J) t
  have h := hφ _ htM g
  rw [← htP, ← halfModulus, hhalf, one_mul] at h
  exact h

/-- Pairing integrability and vanishing on positive slices with logarithm in
the relative coroot space imply integrability and vanishing on every positive
Levi slice of a weak constant term. -/
def WeakConstantTermRelativeSliceReductionStatement : Prop :=
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (K : Subgroup (AdelicGroupPoints F G)) (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    (Φ ψ : AdelicGroupPoints F G → ℂ) (ν : RealCharacterParameter F G),
    (∀ a ∈ canonicalSubgroup F G, ∀ g,
      Φ (a * g) = parameterPower F G (imaginaryParameter F G ν) a * Φ g) →
    fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
    (∀ φ : AdelicGroupPoints F G → ℂ,
      IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ →
      ∀ (x : fam.positiveSplitComponent J) (c : fam.relativeSimpleRoots J → ℝ),
        characterLog F P x.val = ∑ α, c α • fam.relativeCoroot J α →
        Integrable (fam.squareIntegrablePairingIntegrand K J x.val φ ψ)
          (fam.squareIntegrablePairingMeasure K hKc J) ∧
        (∫ z, fam.squareIntegrablePairingIntegrand K J x.val φ ψ z
            ∂(fam.squareIntegrablePairingMeasure K hKc J)) = 0) →
    fam.IsSquareIntegrableOrthogonal K hKc rho hsmooth hcalc J ψ

theorem weakConstantTermRelativeSliceReduction : fam.WeakConstantTermRelativeSliceReductionStatement J := by
  intro N d rho hsmooth hcalc K hKc Φ ψ ν hΦ hψ hRel φ hφ x hx
  obtain ⟨a, y, z, c, hxy, haz, hhalf, hyLog⟩ := fam.positiveSplitComponent_factor_coroot J ⟨x, hx⟩
  have hcomm (g : AdelicGroupPoints F G) : Commute z.val g :=
    ((Subgroup.mem_center_iff.mp (canonicalSubgroup_le_center F G z.property)) g).symm
  let b := parameterPower F G (imaginaryParameter F G ν) z.val
  have hψz (g : AdelicGroupPoints F G) : ψ (z.val * g) = b * ψ g := by
    rw [(hcomm g).eq]
    exact hψ.rightTranslate_eq_smul fam J z.val b (fun w => by rw [← (hcomm w).eq]; exact hΦ _ z.property w) g
  have hφz (g : AdelicGroupPoints F G) : φ (z.val * g) = φ g := by
    rw [← haz]
    exact fam.inducing_mul_at_central_lift J hφ.2.1 a.property hhalf g
  have hmap : map F P G (fam.p J) x = z.val * map F P G (fam.p J) y.val := by
    have h := congrArg (fun w : fam.positiveSplitComponent J => w.val) hxy
    change a.val * y.val = x at h
    rw [← h, map_mul, haz]
  have hIntegrand :
      fam.squareIntegrablePairingIntegrand K J x φ ψ = fun u =>
        (starRingEnd ℂ) b * fam.squareIntegrablePairingIntegrand K J y.val φ ψ u := by
    funext u
    simp only [squareIntegrablePairingIntegrand, hmap, mul_assoc, hφz, hψz, map_mul]
    ring
  obtain ⟨hInt, hZero⟩ := hRel φ hφ y c hyLog
  rw [hIntegrand, integral_const_mul, hZero, mul_zero]
  exact ⟨hInt.const_mul _, rfl⟩

end Langlands.Global.StandardParabolicFamily
