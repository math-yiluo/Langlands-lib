import Langlands.Correspondence.ArithmeticEpsilonMonomial
import Langlands.Correspondence.BaseReciprocityCandidate
import Langlands.Correspondence.BaseGeometricResidue
import Langlands.LocalFactor.NonabelianScalingProof
import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeMeasures

/-!
# Change of additive character for arithmetic pair epsilon certificates

For a supplied local-constant system and continuous Weil representations `A`, `B`,
the arithmetic pair epsilon certificate `ε(s, A ⊗ B, ψ) = c q^(-ms)` is read on the
canonical bottom-field data: the transported character, the transported self-dual
measure and the bottom restrictions. Deligne's scaling law
(`LocalFactor.NonabelianSystem.additiveCharacterScaling`) and the Haar scaling law
of the system then give the certificate for `ψ^a(x) = ψ(ax)`:
`ε(s, A ⊗ B, ψ^a) = det(A ⊗ B)(w) |a|^(N(s - 1/2)) ε(s, A ⊗ B, ψ)` with
`N = dim A · dim B` and `w` a Weil element with reciprocity image `a`.
-/

noncomputable section

set_option autoImplicit false

universe uF uP uV

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The determinant of a twist by a continuous character `χ` is `χ^deg` times the
determinant, on the exact virtual group of continuous representations. -/
theorem determinantCharacter_continuousTwist (χ : G →ₜ* ℂˣ)
    (x : ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, _, uV} ℂ G => A.IsContinuous))
    (g : G) :
    determinantCharacter _ (continuousTwist χ x) g =
      χ g ^ degree _ x * determinantCharacter _ x g := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y z hy hz =>
    simp only [map_add, determinantCharacter_add, MonoidHom.mul_apply, hy, hz]
    rw [zpow_add]
    apply Units.ext
    simp only [Units.val_mul]
    ring
  | single c n =>
    have hs : Finsupp.single c n = n • generator c := by simp [generator]
    rw [hs, map_zsmul, map_zsmul, map_zsmul, determinantCharacter_zsmul,
      determinantCharacter_zsmul]
    change (determinantCharacter _ (continuousTwist χ (ofClass _ c)) ^ n) g =
      χ g ^ (n • degree _ (ofClass _ c)) * (determinantCharacter _ (ofClass _ c) ^ n) g
    induction c using Quotient.inductionOn with
    | h A =>
      change (determinantCharacter _ (continuousTwist χ (ofRepresentation _ A)) ^ n) g =
        χ g ^ (n • degree _ (ofRepresentation _ A)) *
          (determinantCharacter _ (ofRepresentation _ A) ^ n) g
      have ht : continuousTwist χ (ofRepresentation _ A) =
          ofRepresentation _ ⟨FiniteRepresentation.twist χ.toMonoidHom A.val,
            FiniteRepresentation.isContinuous_twist χ A.property⟩ :=
        twist_ofRepresentation _ _ _ _ A
      rw [ht, MonoidHom.zpow_apply, MonoidHom.zpow_apply, degree_ofRepresentation]
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val,
        determinantCharacter_ofRepresentation_apply, smul_eq_mul]
      change LinearMap.det (Langlands.twist χ.toMonoidHom A.val.representation g) ^ n = _
      rw [Langlands.det_twist, mul_zpow, ← zpow_natCast, ← zpow_mul, mul_comm _ n]
      rfl

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne
open LocalFactor.CommonClosureSpectral Weil.Local VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance arithmeticEpsilonScalingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance arithmeticEpsilonScalingValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance arithmeticEpsilonScalingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance arithmeticEpsilonScalingMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance arithmeticEpsilonScalingBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance arithmeticEpsilonScalingBottomTopology :
    TopologicalSpace (baseExtension F).field :=
  (fieldData F (baseExtension F)).topology
local instance arithmeticEpsilonScalingBottomValuativeRel :
    ValuativeRel (baseExtension F).field :=
  (fieldData F (baseExtension F)).valuativeRel
local instance arithmeticEpsilonScalingBottomLocalField :
    IsNonarchimedeanLocalField (baseExtension F).field :=
  (fieldData F (baseExtension F)).localField
local instance arithmeticEpsilonScalingBottomMeasurable :
    MeasurableSpace (baseExtension F).field := borel (baseExtension F).field
local instance arithmeticEpsilonScalingBottomBorel : BorelSpace (baseExtension F).field := ⟨rfl⟩

/-- The bottom restriction pair has the dimension of the representation. -/
theorem rank_baseRestrictionPair (A : LocalWeilRepresentation.{uF, uP} F) :
    (baseRestrictionPair F A : Pair.{uF, uV} F (baseExtension F)).toFiniteRepresentation.rank =
      A.rank :=
  (FiniteRepresentation.transportLinearEquiv _).finrank_eq

/-- The bottom restriction pair has the determinant of the representation. -/
theorem det_baseRestrictionPair (A : LocalWeilRepresentation.{uF, uP} F)
    (w : localWeilGroup F) :
    LinearMap.det ((baseRestrictionPair F A : Pair.{uF, uV} F (baseExtension F)).representation
      (baseWeilEquiv F w)) = LinearMap.det (A.representation w) := by
  change LinearMap.det ((FiniteRepresentation.transportLinearEquiv
      (FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype A)).symm.toLinearMap ∘ₗ
    (A.representation w) ∘ₗ (FiniteRepresentation.transportLinearEquiv
      (FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype A)).toLinearMap) = _
  exact LinearMap.det_conj _ (FiniteRepresentation.transportLinearEquiv _).symm

/-- The dimension of the bottom tensor class is `dim A · dim B`. -/
theorem degree_baseTensorClass (A B : LocalWeilRepresentation.{uF, uP} F)
    (hA : A.IsContinuous) (hB : B.IsContinuous) :
    degree F (baseExtension F) (baseTensorClass F A B hA hB : Virtual.{uF, uV} F (baseExtension F)) =
      (A.rank : ℤ) * B.rank := by
  rw [baseTensorClass, underlyingClass, ExactGrothendieckGroup.degree_ofRepresentation]
  change ((Module.finrank ℂ (TensorProduct ℂ
    (baseRestrictionPair F A : Pair.{uF, uV} F (baseExtension F)).toFiniteRepresentation
    (baseRestrictionPair F B : Pair.{uF, uV} F (baseExtension F)).toFiniteRepresentation) : ℕ) : ℤ) = _
  rw [Module.finrank_tensorProduct]
  change (((baseRestrictionPair F A : Pair.{uF, uV} F (baseExtension F)).toFiniteRepresentation.rank *
    (baseRestrictionPair F B : Pair.{uF, uV} F (baseExtension F)).toFiniteRepresentation.rank : ℕ) : ℤ) = _
  rw [rank_baseRestrictionPair, rank_baseRestrictionPair]
  push_cast
  rfl

/-- The determinant of the bottom tensor class at a base Weil element is
`det(A)^(dim B) det(B)^(dim A)`. -/
theorem determinantCharacter_baseTensorClass (A B : LocalWeilRepresentation.{uF, uP} F)
    (hA : A.IsContinuous) (hB : B.IsContinuous) (w : localWeilGroup F) :
    ((ExactGrothendieckGroup.determinantCharacter _
        (baseTensorClass F A B hA hB : Virtual.{uF, uV} F (baseExtension F))
        (baseWeilEquiv F w) : ℂˣ) : ℂ) =
      LinearMap.det (A.representation w) ^ B.rank * LinearMap.det (B.representation w) ^ A.rank := by
  rw [baseTensorClass, underlyingClass,
    ExactGrothendieckGroup.determinantCharacter_ofRepresentation_apply]
  change LinearMap.det (TensorProduct.map
    ((baseRestrictionPair F A : Pair.{uF, uV} F (baseExtension F)).representation (baseWeilEquiv F w))
    ((baseRestrictionPair F B : Pair.{uF, uV} F (baseExtension F)).representation
      (baseWeilEquiv F w))) = _
  rw [Langlands.det_tensorProduct_map, det_baseRestrictionPair, det_baseRestrictionPair]
  change _ ^ (baseRestrictionPair F B : Pair.{uF, uV} F (baseExtension F)).toFiniteRepresentation.rank *
    _ ^ (baseRestrictionPair F A : Pair.{uF, uV} F (baseExtension F)).toFiniteRepresentation.rank = _
  rw [rank_baseRestrictionPair, rank_baseRestrictionPair]

/-- Transport to the bottom field commutes with scaling the additive character. -/
theorem baseFieldAdditiveCharacterEquiv_scale (ψ : NontrivialAdditiveCharacter F)
    (a : F.Carrierˣ) :
    baseFieldAdditiveCharacterEquiv F (ψ.scale a) =
      (baseFieldAdditiveCharacterEquiv F ψ).scale ((baseFieldUnitsEquiv F).symm a) := by
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro x
  rw [baseFieldAdditiveCharacterEquiv_apply, HarmonicAnalysis.UnitaryAdditiveCharacter.scale_apply,
    HarmonicAnalysis.UnitaryAdditiveCharacter.scale_apply, baseFieldAdditiveCharacterEquiv_apply]
  congr 1
  rw [map_mul (baseFieldPadicEquiv F)]
  congr 1
  have h := baseFieldUnitsEquiv_apply F ((baseFieldUnitsEquiv F).symm a)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  exact h

/-- The self-dual measure of `ψ^a` is `|a|^(1/2)` times that of `ψ`. -/
theorem localSelfDualHaar_scale (ψ : NontrivialAdditiveCharacter F) (a : F.Carrierˣ) :
    localSelfDualHaar F (ψ.scale a) =
      (localSelfDualHaar F ψ).scale (PadicAbelian.sqrtNormalizedAbs F a)
        (PadicAbelian.sqrtNormalizedAbs_pos F a) :=
  (eq_localSelfDualHaar F (ψ.scale a) _
    (PadicAbelian.isSelfDual_scale F ψ a
      ⟨localSelfDualHaar F ψ, isSelfDual_localSelfDualHaar F ψ⟩)).symm

/-- Transport to the bottom field commutes with scaling the Haar measure. -/
theorem baseFieldHaarMeasureEquiv_scale (μ : LocalAdditiveHaarMeasure F) (c : NNReal)
    (hc : 0 < c) :
    baseFieldHaarMeasureEquiv F (μ.scale c hc) =
      scaleHaar F (baseExtension F) (baseFieldHaarMeasureEquiv F μ) c hc :=
  HarmonicAnalysis.FieldTransport.haarMeasure_scale _
    (by
      let : Algebra (Padic p) (baseExtension F).field :=
        ((baseExtension F).asPadicField (p := p)).algebra
      let := ((baseExtension F).asPadicField (p := p)).canonicalNormedField
      let := F.canonicalNormedField
      exact (Weil.Local.extension_isometry F ((baseExtension F).asPadicField (p := p))
        (baseFieldPadicEquiv F).symm.toAlgHom).continuous)
    (by
      let : Algebra (Padic p) (baseExtension F).field :=
        ((baseExtension F).asPadicField (p := p)).algebra
      let := ((baseExtension F).asPadicField (p := p)).canonicalNormedField
      let := F.canonicalNormedField
      exact (Weil.Local.extension_isometry ((baseExtension F).asPadicField (p := p)) F
        (baseFieldPadicEquiv F).toAlgHom).continuous) μ c hc

/-- The bottom-field absolute value of a transported unit. -/
theorem normalizedAbs_baseFieldUnitsEquiv_symm (a : F.Carrierˣ) :
    (fieldData F (baseExtension F)).normalizedAbs
        (((baseFieldUnitsEquiv F).symm a : (baseExtension F).fieldˣ) : (baseExtension F).field) =
      F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) := by
  have hm := PadicField.CanonicalTransport.normalizedAbs_map
    ((baseExtension F).asPadicField (p := p)) F (baseFieldPadicEquiv F)
    (((baseFieldUnitsEquiv F).symm a : (baseExtension F).fieldˣ) : (baseExtension F).field)
  have h := baseFieldUnitsEquiv_apply F ((baseFieldUnitsEquiv F).symm a)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  change F.canonicalTopologicalData.normalizedAbs (IntermediateField.botEquiv F.Carrier
      (AlgebraicClosure F.Carrier) _) = _ at hm
  rw [← h] at hm
  exact hm.symm

/-- The bottom component of the reciprocity family on a base Weil element. -/
theorem reciprocityUnits_baseWeilEquiv (eC : ReciprocityFamily F) (w : localWeilGroup F) :
    reciprocityUnits F eC (baseExtension F) (baseWeilEquiv F w) =
      (baseFieldUnitsEquiv F).symm (reciprocityHom F (baseReciprocityCandidate F eC) w) := by
  rw [ContinuousMulEquiv.eq_symm_apply,
    IsBaseReciprocity.units_eq F (baseReciprocityCandidate_spec F eC)]
  rfl

/-- The order of the reciprocity image of a base Weil element is its degree. -/
theorem ord_reciprocityHom_baseReciprocityCandidate (eC : ReciprocityFamily F)
    (he : NormalizedReciprocity F eC) (w : localWeilGroup F) :
    F.canonicalTopologicalData.ord (reciprocityHom F (baseReciprocityCandidate F eC) w : F.Carrier) =
      localDegreeInt F w := by
  have h := normalizedAbs_baseReciprocityCandidate F eC he w
  rw [F.canonicalTopologicalData.normalizedAbs_of_ne_zero
    (reciprocityHom F (baseReciprocityCandidate F eC) w).ne_zero] at h
  have hq : (1 : ℝ) < (F.canonicalTopologicalData.residueCardinality : ℝ) := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) (ne_of_gt hq) h)

/-- The spectral character `|·|^s` at a base Weil element is `(q^(-s))^deg`. -/
theorem character_baseWeilEquiv (s : ℂ) (w : localWeilGroup F) :
    (CommonClosureSpectral.character F (baseExtension F) s (baseWeilEquiv F w) : ℂ) =
      RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s ^
        localDegreeInt F w := by
  have hq : 0 < (F.canonicalTopologicalData.residueCardinality : ℝ) := by
    exact_mod_cast zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one
  rw [CommonClosureSpectral.character_apply, RankinSelberg.spectralPoint_eq_spectralParameter _ hq]
  rfl

/-- An arithmetic pair epsilon certificate of two continuous zero-monodromy pairs is
read on the canonical bottom-field data. -/
theorem isArithmeticPairEpsilonFactor_zeroMonodromy_iff (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (A B : LocalWeilRepresentation.{uF, uP} F)
    (hA : A.IsContinuous) (hB : B.IsContinuous) (c : ℂˣ) (m : ℤ) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B)) c m ↔
      ∀ s : ℂ, (ε (baseExtension F) (baseFieldAdditiveCharacterEquiv F ψ)
          (baseFieldHaarMeasureEquiv F (localSelfDualHaar F ψ))
          (virtualTwist F (baseExtension F) s
            (baseTensorClass F A B hA hB : Virtual.{uF, uV} F (baseExtension F))) : ℂ) =
        RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality c m s := by
  let ψ' := baseFieldAdditiveCharacterEquiv F ψ
  have hψ' : IsBaseCharacter F ψ ψ' :=
    (isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ ψ').mpr rfl
  let μ' := baseFieldHaarMeasureEquiv F (localSelfDualHaar F ψ)
  have hμ' : CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ' := by
    rw [isSelfDual_of_isBaseCharacter_iff F ψ ψ' hψ' μ', Equiv.symm_apply_apply]
    exact isSelfDual_localSelfDualHaar F ψ
  let A' : Pair.{uF, uV} F (baseExtension F) := baseRestrictionPair F A
  let B' : Pair.{uF, uV} F (baseExtension F) := baseRestrictionPair F B
  have hAr : IsBaseRestriction F _ A' := isBaseRestriction_baseRestrictionPair F A
  have hBr : IsBaseRestriction F _ B' := isBaseRestriction_baseRestrictionPair F B
  have hAc : A'.toFiniteRepresentation.IsContinuous := baseRestrictionPair_isContinuous F A hA
  have hBc : B'.toFiniteRepresentation.IsContinuous := baseRestrictionPair_isContinuous F B hB
  have h0 : (WeilDeligneRepresentation.tensor A' B').monodromy = 0 :=
    WeilDeligneRepresentation.tensor_monodromy_eq_zero rfl rfl
  -- The value of the canonical datum.
  have hval : ∀ (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ),
      CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ'
        A' B' hAc hBc Φ s =
      ε (baseExtension F) ψ' μ'
        (virtualTwist F (baseExtension F) s
          (baseTensorClass F A B hA hB : Virtual.{uF, uV} F (baseExtension F))) := by
    intro Φ s
    change conditionalEpsilonValue F eC ε hε _ _ _ (WeilDeligneRepresentation.tensor A' B')
      (CommonClosureGamma.tensor_isContinuous F _ A' B' hAc hBc) Φ s = _
    rw [conditionalEpsilonValue_of_monodromy_zero F eC ε hε _ _ _ _ _ h0 Φ s]
    rfl
  constructor
  · intro h s
    rw [← hval (baseGeometricFrobenius F) s]
    exact h.2.2 ψ' μ' A' B' ⟨hψ', hμ', hAr, hBr⟩ hAc hBc (baseGeometricFrobenius F) s
  · intro h
    refine ⟨⟨ψ', μ', A', B', ⟨hψ', hμ', hAr, hBr⟩, hAc, hBc⟩, ⟨baseGeometricFrobenius F⟩, ?_⟩
    rintro ψ'' μ'' A'' B'' ⟨hψ'', hμ'', hA'', hB''⟩ hAc'' hBc'' Φ s
    obtain rfl : ψ'' = ψ' :=
      (isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ ψ'').mp hψ''
    have hμeq : μ'' = μ' := by
      have h1 := (isSelfDual_of_isBaseCharacter_iff F ψ _ hψ'' μ'').mp hμ''
      have h2 := eq_localSelfDualHaar F ψ _ h1
      change μ'' = baseFieldHaarMeasureEquiv F (localSelfDualHaar F ψ)
      rw [← h2, Equiv.apply_symm_apply]
    subst hμeq
    obtain ⟨fA⟩ := IsBaseRestriction.nonempty_equiv F rfl hA''
    obtain ⟨gA⟩ := IsBaseRestriction.nonempty_equiv F rfl hAr
    obtain ⟨fB⟩ := IsBaseRestriction.nonempty_equiv F rfl hB''
    obtain ⟨gB⟩ := IsBaseRestriction.nonempty_equiv F rfl hBr
    rw [CommonClosureGamma.conditionalPairEpsilonValue_eq_of_equiv F eC ε hε _ _ _ hAc'' hAc
      hBc'' hBc (fA.symm.trans gA) (fB.symm.trans gB) Φ s, hval Φ s]
    exact h s

/-- Change of additive character for the arithmetic pair epsilon certificate of two
continuous zero-monodromy pairs (Deligne's scaling law with self-dual measures): if
`ε(s, A ⊗ B, ψ) = c q^(-ms)` and `a` is the reciprocity image of `w`, then
`ε(s, A ⊗ B, ψ^a) = c det(A)(w)^(dim B) det(B)(w)^(dim A) |a|^(-N/2) q^(-(m + N ord a)s)`
with `N = dim A · dim B`. -/
theorem isArithmeticPairEpsilonFactor_zeroMonodromy_scale (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (A B : LocalWeilRepresentation.{uF, uP} F)
    (hA : A.IsContinuous) (hB : B.IsContinuous) (w : localWeilGroup F) {c : ℂˣ} {m : ℤ}
    (h : IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B)) c m) :
    IsArithmeticPairEpsilonFactor F eC ε hε
      (ψ.scale (reciprocityHom F (baseReciprocityCandidate F eC) w))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B))
      (c * FiniteRepresentation.determinantCharacter A w ^ (B.rank : ℤ) *
        FiniteRepresentation.determinantCharacter B w ^ (A.rank : ℤ) *
        (NonabelianSystem.positiveScale
          (PadicAbelian.sqrtNormalizedAbs F (reciprocityHom F (baseReciprocityCandidate F eC) w))
          (PadicAbelian.sqrtNormalizedAbs_pos F _))⁻¹ ^ ((A.rank : ℤ) * B.rank))
      (m + (A.rank : ℤ) * B.rank * F.canonicalTopologicalData.ord
        (reciprocityHom F (baseReciprocityCandidate F eC) w : F.Carrier)) := by
  set a := reciprocityHom F (baseReciprocityCandidate F eC) w with ha
  set κ := PadicAbelian.sqrtNormalizedAbs F a with hκdef
  have hκ : 0 < κ := PadicAbelian.sqrtNormalizedAbs_pos F a
  have hq : 0 < F.canonicalTopologicalData.residueCardinality :=
    zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one
  rw [isArithmeticPairEpsilonFactor_zeroMonodromy_iff F eC ε hε ψ A B hA hB] at h
  rw [isArithmeticPairEpsilonFactor_zeroMonodromy_iff F eC ε hε _ A B hA hB]
  intro s
  set x := (baseTensorClass F A B hA hB : Virtual.{uF, uV} F (baseExtension F)) with hx
  set ψ' := baseFieldAdditiveCharacterEquiv F ψ with hψ'
  set μ' := baseFieldHaarMeasureEquiv F (localSelfDualHaar F ψ) with hμ'
  set a' := (baseFieldUnitsEquiv F).symm a with ha'
  have hw' : reciprocityUnits F eC (baseExtension F) (baseWeilEquiv F w) = a' :=
    reciprocityUnits_baseWeilEquiv F eC w
  rw [baseFieldAdditiveCharacterEquiv_scale, localSelfDualHaar_scale,
    baseFieldHaarMeasureEquiv_scale, hε.2.2.1, Units.val_mul]
  have hscale := NonabelianSystem.additiveCharacterScaling F eC ε hε (baseExtension F) ψ' μ' a'
    (baseWeilEquiv F w) hw' (virtualTwist F (baseExtension F) s x)
  rw [← hψ', ← hμ', ← ha', hscale, h s]
  have hN := degree_baseTensorClass.{uF, uP, uV} F A B hA hB
  have hdet : ((ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F (baseExtension F))
        (virtualTwist F (baseExtension F) s x) (baseWeilEquiv F w) : ℂˣ) : ℂ) =
      (RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s ^
          localDegreeInt F w) ^ ((A.rank : ℤ) * B.rank) *
        (LinearMap.det (A.representation w) ^ B.rank *
          LinearMap.det (B.representation w) ^ A.rank) := by
    have ht := ExactGrothendieckGroup.determinantCharacter_continuousTwist
      (CommonClosureSpectral.character F (baseExtension F) s) x (baseWeilEquiv F w)
    change ((ExactGrothendieckGroup.determinantCharacter _
      (ExactGrothendieckGroup.continuousTwist (CommonClosureSpectral.character F (baseExtension F) s)
        x) (baseWeilEquiv F w) : ℂˣ) : ℂ) = _
    rw [ht, Units.val_mul, Units.val_zpow_eq_zpow_val, character_baseWeilEquiv]
    change _ ^ (degree F (baseExtension F) x) * _ = _
    rw [hN, hx, determinantCharacter_baseTensorClass]
  have hord : F.canonicalTopologicalData.ord (a : F.Carrier) = localDegreeInt F w :=
    ord_reciprocityHom_baseReciprocityCandidate F eC hε.1 w
  have hdA : ((FiniteRepresentation.determinantCharacter A w : ℂˣ) : ℂ) =
      LinearMap.det (A.representation w) := rfl
  have hdB : ((FiniteRepresentation.determinantCharacter B w : ℂˣ) : ℂ) =
      LinearMap.det (B.representation w) := rfl
  rw [hdet, CommonClosureSpectral.degree_virtualTwist, hN, normalizedAbs_baseFieldUnitsEquiv_symm,
    ← PadicAbelian.sqrtNormalizedAbs_sq, hord]
  simp only [RankinSelberg.epsilonMonomial, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.val_inv_eq_inv_val, NonabelianSystem.positiveScale, Units.val_mk0, hdA, hdB]
  have hsp := RankinSelberg.spectralPoint_ne_zero_of_pos hq s
  generalize RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s = S at hsp ⊢
  have hK : ((PadicAbelian.sqrtNormalizedAbs F a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  rw [Complex.ofReal_pow]
  generalize ((PadicAbelian.sqrtNormalizedAbs F a : ℝ) : ℂ) = K at hK ⊢
  generalize (FiniteRepresentation.rank A : ℤ) * FiniteRepresentation.rank B = N
  generalize localDegreeInt F w = d
  rw [zpow_add₀ hsp, mul_comm N d, zpow_mul, sq, mul_zpow, zpow_neg, inv_zpow, zpow_natCast,
    zpow_natCast]
  have hKN : K ^ N ≠ 0 := zpow_ne_zero N hK
  field_simp

end Langlands.Correspondence
