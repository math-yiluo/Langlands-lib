import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.AdelicStandardConstantTermTwist
import Langlands.Global.AdelicSpringerCentralCompactnessProof
import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor

/-! # The norm-one Levi criterion for square-integrable inducing forms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints InducedInnerProductIntegrable Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

variable {K : Subgroup (AdelicGroupPoints F G)} (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "M" => fam.M J
local notation "P" => fam.P J
local notation "Q₁" => NormOneRationalQuotient F M

/-- The absolute square on the norm-one Levi slice. -/
def normOneLeviSquare (f : AdelicGroupPoints F G → ℂ) (z : K × Q₁) : ℝ :=
  ‖f (map F P G (fam.p J) (map F M P (fam.l J) (z.2.out : normOneSubgroup F M)) * z.1.val)‖ ^ 2

local notation "V" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)
local notation "μ₁" => Measure.prod (compactHaarProbability F G K hKc) (normOneRationalQuotientHaarMeasure F M)

/-- With split-component covariance, the defining weighted square is integrable exactly when
its norm-one slice has integrable absolute square. -/
theorem isSquareIntegrableInducedForm_iff_normOneLeviSquare {f : AdelicGroupPoints F G → ℂ}
    (hf : IsAutomorphicFunctionOn F G hsmooth hcalc V (K.comap (ofInfinite F G).toMonoidHom) rho f)
    (hcov : IsSplitComponentEquivariant (fam.p J) (fam.l J) f) :
    IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) f ↔
      Integrable (fam.normOneLeviSquare J f : K × Q₁ → ℝ) μ₁ := by
  let ml := map F M P (fam.l J)
  let pg := map F P G (fam.p J)
  let Γ := RestrictionSplitCentre.canonicalRationalSubgroup F M
  let δ := modulusParameter F P
  let weight (k : K) (m : AdelicGroupPoints F M) :=
    ‖parameterPower F P (-δ) (ml m)‖ * ‖f (pg (ml m) * k.val)‖ ^ 2
  have hInv (k : K) : ∀ b ∈ Γ, ∀ m, weight k (b * m) = weight k m := by
    apply LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
      (Δ := rationalSubgroup F M)
    · intro b hb m
      have hcancel : ‖parameterPower F P (-δ) (ml b)‖ *
          ‖parameterPower F P (halfModulusParameter F P) (ml b)‖ ^ 2 = 1 := by
        rw [pow_two, ← mul_assoc, ← norm_mul, ← parameterPower_add, ← norm_mul, ← parameterPower_add,
          neg_modulus_add_half_add_half, parameterPower_zero, norm_one]
      dsimp only [weight]
      rw [form_canonical_mul hcov hb, map_mul, parameterPower_mul, norm_mul, norm_mul, mul_pow,
        mul_mul_mul_comm, hcancel, one_mul]
    · intro b hb m
      dsimp only [weight]
      rw [parameterPower_map_mul_left _ (fam.l J) (rationalSubgroup_le_normOneSubgroup F M hb),
        form_rational_mul hf.1 hb]
  let κ := compactHaarProbability F G K hKc
  let m₁ := normOneRationalQuotientHaarMeasure F M
  let mC := RestrictionSplitCentre.canonicalMeasure F M
  let hM := (fam.isCompatible J).levi.isConnectedReductive
  let : BorelSpace (RestrictionSplitCentre.CanonicalQuotient F M) :=
    RestrictionSplitCentre.canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  let : IsFiniteMeasure m₁ := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F M hM
  let e := (RestrictionSplitCentre.canonicalNormOneQuotientHomeomorph F M hM).toMeasurableEquiv
  let E := (MeasurableEquiv.refl K).prodCongr e
  have he : MeasurePreserving e m₁ mC :=
    RestrictionSplitCentre.measurePreserving_canonicalNormOneQuotientHomeomorph F M hM
  have hE : MeasurePreserving E (κ.prod m₁) (κ.prod mC) := by
    refine ⟨E.measurable, ?_⟩
    change (κ.prod m₁).map (Prod.map id e) = κ.prod mC
    rw [← Measure.map_prod_map _ _ measurable_id he.measurable, Measure.map_id, he.map_eq]
  let W (z : K × RestrictionSplitCentre.CanonicalQuotient F M) := weight z.1 z.2.out
  have hEq : W ∘ E = fam.normOneLeviSquare J f := by
    funext z
    let n : normOneSubgroup F M := z.2.out
    have hq : e z.2 = LeftCosetSpace.mk Γ n.val := by
      refine (congrArg e (Quotient.out_eq z.2).symm).trans ?_
      change RestrictionSplitCentre.canonicalNormOneQuotientHomeomorph F M hM
        (LeftCosetSpace.mk (rationalNormOneSubgroup F M) n) = _
      rw [RestrictionSplitCentre.coe_canonicalNormOneQuotientHomeomorph,
        RestrictionSplitCentre.normOneToQuotient_mk]
    change weight z.1 (e z.2).out = ‖f (pg (ml n.val) * z.1.val)‖ ^ 2
    rw [hq, LeftCosetSpace.out_mk_of_invariant Γ _ (hInv z.1)]
    have hδ : parameterPower F P (-δ) (ml n.val) = 1 :=
      parameterPower_map_of_mem_normOne (-δ) (fam.l J) n.property
    simp only [weight, hδ, norm_one, one_mul]
  change (_ ∧ _ ∧ Integrable W (κ.prod mC)) ↔ Integrable _ (κ.prod m₁)
  rw [← hEq, hE.integrable_comp_emb E.measurableEmbedding]
  exact ⟨fun h => h.2.2, fun h => ⟨hf, hcov, h⟩⟩

/-- Untwisting an ordinary split-component eigenvector supplies the covariance. The norm-one
slice of the inverse twist agrees with that of the original vector. -/
theorem isSquareIntegrableInducedForm_parameterTwist_of_eigenvector
    [IsClosedImmersion (fam.p J).hom.hom.left] (hK : IsIwasawaCompact (fam.p J) K)
    {lam : ComplexCharacterParameter F P} {w : AdelicGroupPoints F G → ℂ}
    (heig : ∀ a : fam.positiveSplitComponent J, fam.splitComponentRepresentation J a w =
      parameterPower F P (lam + halfModulusParameter F P) a • w)
    (hAut : IsAutomorphicFunctionOn F G hsmooth hcalc V (K.comap (ofInfinite F G).toMonoidHom) rho
      (hK.parameterTwist w (-lam)))
    (hSq : Integrable (fam.normOneLeviSquare J w : K × Q₁ → ℝ) μ₁) :
    IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J)
      (hK.parameterTwist w (-lam)) := by
  let f := hK.parameterTwist w (-lam)
  have hCov : IsSplitComponentEquivariant (fam.p J) (fam.l J) f := by
    intro m hm g
    let a := map F M P (fam.l J) m
    have ha : a ∈ fam.positiveSplitComponent J := by
      rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup (fam.isCompatible J).splitComponent] at hm
      obtain ⟨b, hb, rfl⟩ := hm
      exact ⟨b, hb, (map_comp_apply_of_hom (fam.a J) b).symm⟩
    have hw := congrFun (heig ⟨a, ha⟩) g
    change w (map F P G (fam.p J) a * g) =
      parameterPower F P (lam + halfModulusParameter F P) a * w g at hw
    have hh : hK.heightPower (-lam) (map F P G (fam.p J) a * g) =
        parameterPower F P (-lam) a * hK.heightPower (-lam) g := by
      simp only [IsIwasawaCompact.heightPower, hK.height_map_mul, map_add, Complex.exp_add, parameterPower]
    have hc : parameterPower F P (lam + halfModulusParameter F P) a * parameterPower F P (-lam) a =
        parameterPower F P (halfModulusParameter F P) a := by
      rw [← StandardParabolicFamily.parameterPower_add]
      congr 1
      abel
    change f (map F P G (fam.p J) a * g) = parameterPower F P (halfModulusParameter F P) a * f g
    simp only [f, IsIwasawaCompact.parameterTwist, hw, hh]
    rw [mul_mul_mul_comm, hc]
  refine (fam.isSquareIntegrableInducedForm_iff_normOneLeviSquare J hKc rho hsmooth hcalc hAut hCov).mpr ?_
  have he : (fam.normOneLeviSquare J f : K × Q₁ → ℝ) = fam.normOneLeviSquare J w := by
    funext z
    have hre := fam.heightPower_normOneLevi_mul J J hK le_rfl (-lam) z.2.out z.1.val
    have hk : hK.heightPower (-lam) z.1.val = 1 := by
      rw [IsIwasawaCompact.heightPower, hK.height_of_mem z.1.property, map_zero, Complex.exp_zero]
    simp only [normOneLeviSquare, f, IsIwasawaCompact.parameterTwist, ← map_comp_apply_of_hom, hre, hk, mul_one]
  rwa [he]

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints InducedInnerProductIntegrable Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- The actual norm-one rational quotient of the minimal standard Levi is compact. -/
theorem compactSpace_normOneRationalQuotient_bot :
    CompactSpace (NormOneRationalQuotient F (fam.M fam.bot)) := by
  let M := fam.M fam.bot
  let j := fam.l fam.bot ≫ fam.p fam.bot
  have hM := (fam.isCompatible fam.bot).levi.isConnectedReductive
  have hj : IsClosedSubgroup j := (fam.isCompatible fam.bot).levi.isClosedSubgroup.comp
    (fam.isCompatible fam.bot).parabolic.isClosedSubgroup
  let : IsAffineHom M.X.hom := hj.isAffineHom
  have hRep : (standardLevi fam.i fam.ν ∅).IsRepresentedBy j := by
    have he : SubgroupFunctor.range j = standardLevi fam.i fam.ν ∅ :=
      (fam.isCompatible fam.bot).levi_eq
    rw [← he]
    exact hj.isRepresentedBy_range
  let t := standardLeviTorusFactor fam.i fam.ν ∅ hRep
  have hMax : IsMaximalSplitTorus t :=
    fam.maximalSplit.isMaximalSplitTorus_standardLeviTorusFactor fam.i fam.ν ∅ hRep hj
  have hCentral : IsCentral t := by
    apply isCentral_of_range_le_torusCentralizer hRep.1
    rw [show t ≫ j = fam.i from standardLeviTorusFactor_comp fam.i fam.ν ∅ hRep, hRep.2,
      standardLevi_empty_eq_torusCentralizer_of_generic fam.i fam.ν fam.connectedReductive
        fam.maximalSplit fam.generic]
  have hcover : HasCompactNormOneRationalCover M :=
    AdelicSiegelFactors.centralSplitCompactQuotient F M hM fam.T t hMax hCentral
  exact hcover.compactSpace

/-- At the minimal standard Levi, continuity and left rational invariance on the parabolic
quotient imply integrability of the norm-one absolute square. -/
theorem integrable_normOneLeviSquare_bot
    {K : Subgroup (AdelicGroupPoints F G)} (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    {f : AdelicGroupPoints F G → ℂ} (hf : Continuous f)
    (hInv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p fam.bot)
      (fam.iU fam.bot) (fam.l fam.bot)) f) :
    Integrable (fam.normOneLeviSquare fam.bot f : K × NormOneRationalQuotient F (fam.M fam.bot) → ℝ)
      ((compactHaarProbability F G K hKc).prod (normOneRationalQuotientHaarMeasure F (fam.M fam.bot))) := by
  let J := fam.bot
  let M := fam.M J
  let P := fam.P J
  let Γ := rationalNormOneSubgroup F M
  let r (k : K) (m : normOneSubgroup F M) : ℝ :=
    ‖f (map F P G (fam.p J) (map F M P (fam.l J) m.val) * k.val)‖ ^ 2
  have hr : Continuous (fun z : K × normOneSubgroup F M => r z.1 z.2) :=
    (hf.comp (((map F P G (fam.p J)).continuous.comp ((map F M P (fam.l J)).continuous.comp
      (continuous_subtype_val.comp continuous_snd))).mul (continuous_subtype_val.comp continuous_fst))).norm.pow 2
  have hΓ (k : K) : ∀ b ∈ Γ, ∀ m, r k (b * m) = r k m := by
    intro b hb m
    have hb' : b.val ∈ rationalSubgroup F M := by
      obtain ⟨q, hq⟩ := hb
      exact ⟨q, congrArg Subtype.val hq⟩
    dsimp only [r]
    rw [show (b * m).val = b.val * m.val from rfl, form_rational_mul hInv hb']
  have hcont : Continuous (fam.normOneLeviSquare J f : K × NormOneRationalQuotient F M → ℝ) :=
    LeftCosetSpace.continuous_out_of_invariant Γ r hr hΓ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let : CompactSpace (NormOneRationalQuotient F M) := fam.compactSpace_normOneRationalQuotient_bot
  let : IsFiniteMeasure (normOneRationalQuotientHaarMeasure F M) :=
    AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F M
      (fam.isCompatible J).levi.isConnectedReductive
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- The square-integrability condition for an automorphic half-modulus-equivariant form on a
standard parabolic quotient can be tested on the norm-one Levi slice. -/
def AdelicSquareIntegrableInducedNormOneStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
      (K : Subgroup (AdelicGroupPoints F G)) (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
      {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (f : AdelicGroupPoints F G → ℂ),
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J))
        (K.comap (ofInfinite F G).toMonoidHom) rho f →
      IsSplitComponentEquivariant (fam.p J) (fam.l J) f →
        (IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) f ↔
          Integrable (fam.normOneLeviSquare J f : K × NormOneRationalQuotient F (fam.M J) → ℝ)
            ((compactHaarProbability F G K hKc).prod (normOneRationalQuotientHaarMeasure F (fam.M J))))

theorem adelicSquareIntegrableInducedNormOne : AdelicSquareIntegrableInducedNormOneStatement := by
  intro F _ _ G _ _ _ fam J K hKc N d rho hsmooth hcalc f hf hcov
  exact fam.isSquareIntegrableInducedForm_iff_normOneLeviSquare J hKc rho hsmooth hcalc hf hcov

end Langlands.Global
