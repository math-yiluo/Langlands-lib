import Langlands.LocalFactor.SpectralConductorReduction
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Correspondence.ArithmeticEpsilonDirectSum
import Langlands.Correspondence.BlockPairEpsilon
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.Weil.Representation.InductionContinuity
import Langlands.VirtualRepresentation.ExactUniverseTransport

/-!
# Integral monomiality of arithmetic epsilon factors

For a supplied local-constant system, the spectral value `ε(V ω_s, ψ)` of every
continuous exact virtual class over the bottom field is `ε(V, ψ) q^(-ms)` for an
integer `m`. The proof is the rank-one formula, the degree-zero induction law and
degree-zero generation, as in Tate's spectral conductor formula, but keeping only
the integrality of the exponent.
-/

noncomputable section

universe uF uV uG uW uP

namespace Langlands.LocalFactor.SpectralConductor

open CommonClosure CommonClosureSpectral CommonClosureSpectralAnalytic ConductorExponent
open VirtualRepresentation NonabelianSystem

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- `exp(-s m log q) = (q^(-s))^m` for the residue cardinality `q` of the base field. -/
theorem exp_logCardinality_base (m : ℤ) (s : ℂ) :
    Complex.exp (-s * ((m : ℂ) * logCardinality (base F))) =
      RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s ^ m := by
  have hpos : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one
  have hlog : logCardinality (base F) =
      Complex.log (F.canonicalTopologicalData.residueCardinality : ℂ) := by
    unfold logCardinality
    rw [residueCardinality_base, Complex.ofReal_log hpos.le, Complex.ofReal_natCast]
  have hq : (F.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  rw [RankinSelberg.spectralPoint, Complex.cpow_def_of_ne_zero hq, ← Complex.exp_int_mul, hlog]
  congr 1
  ring

/-- `log q_L = f_L log q` for the residue degree `f_L` of an intermediate field over
the base field. -/
theorem logCardinality_eq_residueDegreeL_mul {e : ReciprocityFamily F}
    (he : NormalizedReciprocity F e) (L : Extension F) :
    logCardinality L = (residueDegreeL e L : ℂ) * logCardinality (base F) := by
  have h1 : logCardinality (base F) = ((Real.log (baseCardinality F) : ℝ) : ℂ) := by
    unfold logCardinality
    rw [residueCardinality_base]
    rfl
  rw [h1]
  change ((Real.log ((fieldData F L).residueCardinality : ℝ) : ℝ) : ℂ) = _
  rw [log_residueCardinality e L he]
  push_cast
  rfl

/-- The bottom-field virtual classes whose spectral value is the ordinary value
times an integral power of `q^(-s)`. -/
def monomialSubgroup {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : IsSystem F e ε) (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F)) :
    AddSubgroup (Virtual.{uF, uV} F (base F)) where
  carrier := {x | ∃ m : ℤ, ∀ s : ℂ,
    (ε (base F) ψ μ (virtualTwist F (base F) s x) : ℂ) =
      ε (base F) ψ μ x *
        RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s ^ m}
  zero_mem' := ⟨0, fun s => by simp [value_zero hε.2.1]⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    have hq : 0 < F.canonicalTopologicalData.residueCardinality :=
      zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one
    refine ⟨m + n, fun s => ?_⟩
    rw [map_add, hε.2.1, hε.2.1, Units.val_mul, Units.val_mul, hm, hn,
      zpow_add₀ (RankinSelberg.spectralPoint_ne_zero_of_pos hq s)]
    ring
  neg_mem' := by
    rintro x ⟨m, hm⟩
    refine ⟨-m, fun s => ?_⟩
    rw [map_neg, value_neg hε.2.1, value_neg hε.2.1, Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val, hm, zpow_neg, mul_inv]

theorem characterClass_one_mem_monomialSubgroup {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hε : IsSystem F e ε) (ψ : AdditiveCharacter F (base F))
    (μ : HaarMeasure F (base F)) :
    ExactGrothendieckGroup.characterClass (1 : weilSubgroup F (base F) →ₜ* ℂˣ) ∈
      monomialSubgroup hε ψ μ := by
  refine ⟨(fieldData F (base F)).additiveConductor ψ, fun s => ?_⟩
  rw [value_virtualTwist_characterClass hε, characterConductor_one,
    ← exp_logCardinality_base (F := F)]
  push_cast
  ring_nf

theorem induce_mem_monomialSubgroup {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hε : IsSystem F e ε) (ψ : AdditiveCharacter F (base F))
    (μ : HaarMeasure F (base F)) (L : Extension F) (h : (base F).field ≤ L.field)
    (χ χ' : weilSubgroup F L →ₜ* ℂˣ) :
    induce F (base F) L h (ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass χ') ∈ monomialSubgroup hε ψ μ := by
  refine ⟨residueDegreeL e L *
    ((characterConductor e L χ : ℤ) - (characterConductor e L χ' : ℤ)), fun s => ?_⟩
  rw [value_virtualTwist_induce hε, ← exp_logCardinality_base (F := F),
    logCardinality_eq_residueDegreeL_mul hε.1 L]
  push_cast
  ring_nf

/-- Every bottom-field continuous virtual class has spectral value
`ε(x) q^(-ms)` for an integer `m`. -/
theorem mem_monomialSubgroup {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : IsSystem F e ε) (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F))
    (x : Virtual.{uF, uV} F (base F)) : x ∈ monomialSubgroup hε ψ μ := by
  have hgen : CommonClosureDegreeZeroGeneration.{uF, uV} F :=
    commonClosureDegreeZeroGeneration p F
  obtain ⟨S₀, hS₀, hx⟩ := exists_finset_generators hgen (base F) x
  let S := monomialSubgroup hε ψ μ
  have hS : (S₀ : Set (Virtual.{uF, uV} F (base F))) ⊆ S := by
    intro y hy
    obtain ⟨L, h, χ, χ', rfl⟩ := hS₀ hy
    exact induce_mem_monomialSubgroup hε ψ μ L h χ χ'
  have hy : x - degree F (base F) x • ExactGrothendieckGroup.characterClass
      (1 : weilSubgroup F (base F) →ₜ* ℂˣ) ∈ S :=
    (Submodule.span_le.mpr
      (show (S₀ : Set (Virtual.{uF, uV} F (base F))) ⊆
        (AddSubgroup.toIntSubmodule S : Set _) from hS)) hx
  have := S.add_mem hy (S.zsmul_mem (characterClass_one_mem_monomialSubgroup hε ψ μ)
    (degree F (base F) x))
  rwa [sub_add_cancel] at this

end Langlands.LocalFactor.SpectralConductor


namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne
open LocalFactor.CommonClosureSpectral Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance arithmeticEpsilonExistenceTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The zero-monodromy pair of the restriction of `A` to the bottom field, copied to
the carrier universe of a local-constant system. -/
def baseRestrictionPair (A : LocalWeilRepresentation.{uF, uP} F) :
    Pair.{uF, uV} F (baseExtension F) :=
  WeilDeligneRepresentation.zeroMonodromy (normCharacter F (baseExtension F)).toMonoidHom
    (FiniteRepresentation.transport
      (FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype A) :
        FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (baseExtension F)))

theorem isBaseRestriction_baseRestrictionPair (A : LocalWeilRepresentation.{uF, uP} F) :
    IsBaseRestriction F
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A))
      (baseRestrictionPair F A : Pair.{uF, uV} F (baseExtension F)) :=
  ⟨WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A, rfl,
    ⟨WeilDeligneRepresentation.zeroMonodromyCongr _
      (FiniteRepresentation.coordinatesEquiv _).symm⟩⟩

theorem baseRestrictionPair_isContinuous (A : LocalWeilRepresentation.{uF, uP} F)
    (hA : A.IsContinuous) :
    (baseRestrictionPair F A : Pair.{uF, uV} F (baseExtension F)).toFiniteRepresentation.IsContinuous :=
  (FiniteRepresentation.isContinuous_iff_of_equiv
    (FiniteRepresentation.coordinatesEquiv _)).mpr
    (FiniteRepresentation.isContinuous_restrict (weilSubgroup F (baseExtension F)).subtype
      continuous_subtype_val hA)

/-- The transported self-dual measure of the base field. -/
def baseSelfDualMeasure (ψ : NontrivialAdditiveCharacter F) : HaarMeasure F (baseExtension F) :=
  baseFieldHaarMeasureEquiv F (localSelfDualHaar F ψ)

theorem isSelfDual_baseSelfDualMeasure (ψ : NontrivialAdditiveCharacter F) :
    CommonClosureSpectral.IsSelfDual F (baseExtension F) (baseFieldAdditiveCharacterEquiv F ψ)
      (baseSelfDualMeasure F ψ) := by
  rw [isSelfDual_of_isBaseCharacter_iff F ψ _
    ((isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ _).mpr rfl),
    baseSelfDualMeasure, Equiv.symm_apply_apply]
  exact isSelfDual_localSelfDualHaar F ψ

/-- The bottom-field exact class of `A ⊗ B`, through the restriction data
`baseRestrictionPair`. -/
def baseTensorClass (A B : LocalWeilRepresentation.{uF, uP} F) (hA : A.IsContinuous)
    (hB : B.IsContinuous) : Virtual.{uF, uV} F (baseExtension F) :=
  underlyingClass F (baseExtension F)
    (WeilDeligneRepresentation.tensor (baseRestrictionPair F A : Pair.{uF, uV} F _)
      (baseRestrictionPair F B : Pair.{uF, uV} F _))
    (CommonClosureGamma.tensor_isContinuous F _ _ _ (baseRestrictionPair_isContinuous F A hA)
      (baseRestrictionPair_isContinuous F B hB))

/-- If the spectral value of the bottom-field class of `A ⊗ B` is `ε(x) (q^(-s))^m`, then
`(ε(x), m)` is an arithmetic pair epsilon certificate of the zero-monodromy pairs. -/
theorem isArithmeticPairEpsilonFactor_of_monomial (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (A B : LocalWeilRepresentation.{uF, uP} F)
    (hA : A.IsContinuous) (hB : B.IsContinuous) (m : ℤ)
    (hm : ∀ s : ℂ, (ε (baseExtension F) (baseFieldAdditiveCharacterEquiv F ψ)
        (baseSelfDualMeasure F ψ)
        (virtualTwist F (baseExtension F) s (baseTensorClass F A B hA hB)) : ℂ) =
      ε (baseExtension F) (baseFieldAdditiveCharacterEquiv F ψ) (baseSelfDualMeasure F ψ)
        (baseTensorClass F A B hA hB) *
      RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s ^ m) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B))
      (ε (baseExtension F) (baseFieldAdditiveCharacterEquiv F ψ) (baseSelfDualMeasure F ψ)
        (baseTensorClass F A B hA hB)) m := by
  let ψ' := baseFieldAdditiveCharacterEquiv F ψ
  have hψ' : IsBaseCharacter F ψ ψ' :=
    (isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ ψ').mpr rfl
  let μ' := baseSelfDualMeasure F ψ
  have hμ' : CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ' :=
    isSelfDual_baseSelfDualMeasure F ψ
  let A' : Pair.{uF, uV} F (baseExtension F) := baseRestrictionPair F A
  let B' : Pair.{uF, uV} F (baseExtension F) := baseRestrictionPair F B
  have hAr : IsBaseRestriction F _ A' := isBaseRestriction_baseRestrictionPair F A
  have hBr : IsBaseRestriction F _ B' := isBaseRestriction_baseRestrictionPair F B
  have hAc : A'.toFiniteRepresentation.IsContinuous := baseRestrictionPair_isContinuous F A hA
  have hBc : B'.toFiniteRepresentation.IsContinuous := baseRestrictionPair_isContinuous F B hB
  refine ⟨⟨ψ', μ', A', B', ⟨hψ', hμ', hAr, hBr⟩, hAc, hBc⟩, ⟨baseGeometricFrobenius F⟩, ?_⟩
  rintro ψ'' μ'' A'' B'' ⟨hψ'', hμ'', hA'', hB''⟩ hAc'' hBc'' Φ s
  obtain rfl : ψ'' = ψ' := (isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ ψ'').mp hψ''
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
    hBc'' hBc (fA.symm.trans gA) (fB.symm.trans gB) Φ s]
  have h0 : (WeilDeligneRepresentation.tensor A' B').monodromy = 0 :=
    WeilDeligneRepresentation.tensor_monodromy_eq_zero rfl rfl
  change (conditionalEpsilonValue F eC ε hε _ _ _ (WeilDeligneRepresentation.tensor A' B')
    (CommonClosureGamma.tensor_isContinuous F _ A' B' hAc hBc) Φ s : ℂ) = _
  rw [conditionalEpsilonValue_of_monodromy_zero F eC ε hε _ _ _ _ _ h0 Φ s]
  exact hm s

end Langlands.Correspondence
