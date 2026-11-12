import Langlands.Representation.Classification.BernsteinDerivativePositivity
import Langlands.Representation.Classification.ConstituentCompatibilityAlgebraicProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.UnitaryWeylRigidityProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Unitary.Basic

/-!
# Central exponents of subquotients and the order-zero shifted derivative

A scalar character passes to every actual smooth subquotient, and on a nonzero
representation it fixes the Bernstein central exponent. For an irreducible
unitarizable representation of `GL_N(F)` with `N > 0`, every irreducible
subquotient of the order-zero shifted derivative `ν^(1/2) π` has central
exponent `N / 2`, hence a positive one (Bernstein 1984, §§7.2, 8.2).
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uF uV uG uC

section Subquotient

variable {G : Type uG} [Group G] [TopologicalSpace G] {C : Type uC} [Group C]

/-- A scalar character of a smooth representation is a scalar character of every
actual smooth subquotient. -/
theorem HasScalarCharacter.of_isSubquotient {A D : SmoothRep.{0, uG, uV} ℂ G}
    {z : C →* G} {ω : C →* ℂˣ} (h : HasScalarCharacter A.representation z ω)
    (hD : SmoothRep.IsSubquotient D A) : HasScalarCharacter D.representation z ω := by
  obtain ⟨S, S', ⟨e⟩⟩ := hD
  have h₁ : HasScalarCharacter (SmoothRep.subrepresentation A S).representation z ω :=
    h.of_injective (SmoothRep.hom (SmoothRep.subtype A S)) (SmoothRep.subtype_injective A S)
  have h₂ : HasScalarCharacter (SmoothRep.subquotient A S S').representation z ω :=
    h₁.of_surjective (SmoothRep.hom (SmoothRep.mkQ _ S')) (SmoothRep.mkQ_surjective _ S')
  refine h₂.of_surjective (SmoothRep.hom e.inv) fun x => ⟨SmoothRep.hom e.hom x, ?_⟩
  change SmoothRep.hom (e.hom ≫ e.inv) x = x
  rw [e.hom_inv_id]
  rfl

end Subquotient

section Exponent

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Two real powers of the normalized absolute value that agree at the chosen
uniformizer have equal exponents. -/
theorem eq_of_normalizedAbs_uniformizer_rpow_eq {e s : ℝ}
    (h : T.normalizedAbs T.uniformizer ^ e = T.normalizedAbs T.uniformizer ^ s) : e = s := by
  obtain ⟨hpos, hne⟩ := UnitaryWeylRigidity.normalizedAbs_uniformizer_pos_ne_one T
  have hlog := congrArg Real.log h
  rw [Real.log_rpow hpos, Real.log_rpow hpos] at hlog
  exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one hpos hne) hlog

/-- On a nonzero representation, any scalar character whose norm is a real power
`s` of the normalized absolute value pins every Bernstein central exponent to `s`. -/
theorem HasBernsteinCentralExponent.eq_of_hasScalarCharacter {n : ℕ}
    {D : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    [Nontrivial D] {e s : ℝ} (he : HasBernsteinCentralExponent T D e)
    {ω : F.Carrierˣ →* ℂˣ}
    (hω : letI := T.topology; HasScalarCharacter D.representation GeneralLinear.scalar ω)
    (hnorm : ∀ a : F.Carrierˣ, ‖(ω a : ℂ)‖ = T.normalizedAbs (a : F.Carrier) ^ s) :
    e = s := by
  let := T.topology
  obtain ⟨ω', hω', hnorm'⟩ := he
  obtain ⟨v, hv⟩ := exists_ne (0 : D)
  let ϖ : F.Carrierˣ := Units.mk0 T.uniformizer (UnitaryWeylRigidity.uniformizer_ne_zero T)
  have hval : (ω' ϖ : ℂ) = (ω ϖ : ℂ) := by
    apply smul_left_injective ℂ hv
    exact (hω' ϖ v).symm.trans (hω ϖ v)
  have h := hnorm' ϖ
  rw [hval, hnorm ϖ] at h
  exact (eq_of_normalizedAbs_uniformizer_rpow_eq T h).symm

end Exponent

section OrderZero

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An irreducible unitarizable smooth representation of `GL_N(F)` has a scalar
character of norm one. Admissibility comes from the cuspidal embedding theorem
and the character from Schur's lemma. -/
theorem exists_hasScalarCharacter_norm_one_of_isUnitarizable {N : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier))
    (hirr : letI := T.topology; Representation.IsIrreducible π.representation)
    (hunit : letI := T.topology; IsUnitarizable π.representation) :
    letI := T.topology
    ∃ ω : F.Carrierˣ →* ℂˣ, HasScalarCharacter π.representation GeneralLinear.scalar ω ∧
      ∀ a, ‖(ω a : ℂ)‖ = 1 := by
  let := T.topology
  have := T.generalLinearTopologicalGroup N
  have hadm : IsAdmissible π.representation :=
    (CuspidalSupport.cuspidalEmbedding F T N π hirr).1
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ := admissibleSchur_centralCharacter π.representation hadm hirr
  have hω : HasScalarCharacter π.representation GeneralLinear.scalar
      (χ.comp GeneralLinear.scalarToCenter) := fun a w => hχ (scalarToCenter a) w
  have := hirr
  have : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear N F.Carrier))
      π.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : π)
  exact ⟨_, hω, fun a => UnitaryWeylRigidity.norm_eq_one_of_isUnitarizable hunit (hω a) hv⟩

/-- Order zero of Bernstein's lower positivity: for an irreducible unitarizable
smooth representation of `GL_N(F)` with `N > 0`, every central exponent of the
shifted derivative `ν^(1/2) π` is `N / 2`, hence positive. -/
theorem bernsteinShiftedDerivative_zero_positive {N : ℕ} (hN : 0 < N)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (π : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier))
    (hirr : letI := T.topology; Representation.IsIrreducible π.representation)
    (hunit : letI := T.topology; IsUnitarizable π.representation) (hk : 0 ≤ N) :
    BernsteinPositiveCentralExponents T (bernsteinShiftedDerivative T ψ π 0 hk) := by
  let := T.topology
  rintro e ⟨D, hDirr, hDsub, he⟩
  obtain ⟨ω, hω, hω1⟩ := exists_hasScalarCharacter_norm_one_of_isUnitarizable F T π hirr hunit
  have hshift := T.hasScalarCharacter_segmentFactor π (1 / 2) hω
  have hD := HasScalarCharacter.of_isSubquotient hshift hDsub
  have := hDirr
  have : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear N F.Carrier))
      D.representation.asModule
  have hes := he.eq_of_hasScalarCharacter T hD fun a => by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hω1, one_mul, MonoidHom.comp_apply,
      T.norm_determinantPowerCharacter_scalar]
  rw [hes]
  have : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  positivity

end OrderZero

end Langlands.Classification
