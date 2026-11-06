import Langlands.WeilDeligne.TensorDual
import Langlands.Correspondence.SupercuspidalGammaCompatibility
import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.Representation.RankinSelberg.PadicGenericGammaFactor
import Langlands.Representation.RankinSelberg.SmoothDualPairFactors
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality

/-!
# Supercuspidal gamma compatibility from L, epsilon and duality

The JPSS gamma factor of a generic pair is the published epsilon-times-L-ratio
expression. The dual L-polynomial is identified with the L-polynomial of the
image pair of the dual Weil classes, and the arithmetic L-ratio with the same
rational function, through the dual of a tensor product.
-/

noncomputable section

open Polynomial



namespace Langlands.LocalFactor.WeilDeligne

universe uK uG uV

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}
  (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ)

/-- The class-level reflected ratio is the reflected L-factor of the dual class
divided by the L-factor of the class. -/
theorem rationalLRatioClass_eq
    (X : WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν) :
    rationalLRatioClass I g c X =
      RationalReflection.subst c
        (rationalLFactorClass I g (WeilDeligneRepresentation.dualClass X)) /
        rationalLFactorClass I g X := by
  induction X using Quotient.inductionOn with
  | h A => rfl

end Langlands.LocalFactor.WeilDeligne

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW uV₂ uW₂

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An equal-rank epsilon factor of a representation with itself supplies a
nonzero standard Whittaker functional, hence genericity. -/
theorem isGeneric_of_isPadicSymmetricEpsilonFactor_self
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hirr : Representation.IsIrreducible π)
    (hadm : letI := F.canonicalTopologicalData.topology; IsAdmissible π) {e : ℂˣ × ℤ}
    (he : IsPadicSymmetricEpsilonFactor F ψ ν π π e) :
    letI := F.canonicalTopologicalData.topology
    Whittaker.IsGeneric ψ r π := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (r + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (r + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient r F.Carrier)
  have h : IsPairEpsilonFactor F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) ν π π e :=
    (isPadicSymmetricEpsilonFactor_of_le le_rfl).mp he
  exact ⟨hirr, hadm, (isPairEpsilonFactor_self.mp h).2.1⟩

/-- For a generic pair whose smooth contragredients are equivalent to `π'` and
`σ'`, the symmetric gamma factor is the epsilon monomial times the original
L-polynomial divided by the reflected L-polynomial of `(π', σ')` for the inverse
character. -/
theorem isPadicSymmetricGammaFactor_of_smoothDual
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (π' : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
    (σ' : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂)
    (hπ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π)
    (hσ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n σ)
    (eπ : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      (smoothContragredient π).Equiv π')
    (eσ : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      (smoothContragredient σ).Equiv σ')
    {e : ℂˣ × ℤ} {P P' : ℂ[X]}
    (he : IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e)
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val π σ P)
    (hP' : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val π' σ' P') :
    IsPadicSymmetricGammaFactor F ψ ν.val π σ
      (rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P P') := by
  let := F.canonicalNormedField
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have hPd : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback σ) P' :=
    (isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient F
      hπ.2.1 hσ.2.1 hπ.1 hσ.1).mpr
      ((IsPadicSymmetricLPolynomial.congr_equiv eπ eσ).mpr hP')
  exact (symmetricGammaExpression.{uF, uV, uW} p F ψ ν r n π σ
    (genericSymmetricGammaConstructionInput F ψ ν.val ν.property π σ hπ hσ)
    e P P' he hP hPd _).mpr rfl

end Langlands.RankinSelberg

namespace Langlands.Correspondence

universe uF uP uA

open LocalFactor Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The pair class of the dual irreducible Weil class is the dual pair class. -/
theorem weilPairClass_continuousIrreducibleDualEquiv {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uP} F n) :
    weilPairClass F (FiniteRepresentation.continuousIrreducibleDualEquiv (n : ℕ) σ) =
      WeilDeligneRepresentation.dualClass (weilPairClass F σ) := by
  unfold weilPairClass weilClassForget
  rw [FiniteRepresentation.forget_continuousIrreducibleDualEquiv]
  generalize FiniteRepresentation.forgetPropertyClass _ σ.val = x
  induction x using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨(WeilDeligneRepresentation.dualZeroMonodromyEquiv A).symm⟩

/-- The reflected arithmetic L-ratio of `σ ⊗ τ` is the reflected pair L-factor of
the dual classes divided by the pair L-factor of `σ`, `τ`. -/
theorem rationalLRatioClass_tensor_weilPairClass {r n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uP} F r) (τ : IrreducibleWeilClass.{uF, uP} F n) :
    WeilDeligne.rationalLRatioClass (localInertia F) (localGeometricFrobenius F)
        (residueReflection F)
        (WeilDeligneRepresentation.tensorClass (weilPairClass F σ) (weilPairClass F τ)) =
      RationalReflection.subst (residueReflection F)
          (arithmeticPairLFactor F
            (weilPairClass F (FiniteRepresentation.continuousIrreducibleDualEquiv (r : ℕ) σ))
            (weilPairClass F (FiniteRepresentation.continuousIrreducibleDualEquiv (n : ℕ) τ))) /
        arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) := by
  rw [WeilDeligne.rationalLRatioClass_eq, WeilDeligneRepresentation.dualClass_tensorClass,
    weilPairClass_continuousIrreducibleDualEquiv, weilPairClass_continuousIrreducibleDualEquiv]
  rfl

section Main

local instance supercuspidalGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance supercuspidalGammaValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance supercuspidalGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- A dual-compatibility witness at supercuspidal representatives `A`, `B` gives an
irreducible admissible representation equivalent to `A` whose smooth
contragredient is equivalent to `B`. -/
theorem exists_equiv_of_isSupercuspidalSmoothDual {n : ℕ+}
    (A B : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := (n : ℕ)))
    (h : IsSupercuspidalSmoothDual F (Quotient.mk _ A : SupercuspidalAutomorphicClass.{uF, uA} F n)
      (Quotient.mk _ B)) :
    ∃ A₁ : AutomorphicObject.{uF, uA} F n,
      Nonempty (A₁.obj.representation.Equiv A.obj.representation) ∧
      Nonempty ((smoothContragredient A₁.obj.representation).Equiv B.obj.representation) := by
  obtain ⟨A₁, B₁, h₁, h₂, ⟨e⟩⟩ := h
  obtain ⟨e₁⟩ := (automorphicClassOf_eq_iff F A₁ A.toIrreducibleAdmissible).mp h₁
  obtain ⟨e₂⟩ := (automorphicClassOf_eq_iff F B₁ B.toIrreducibleAdmissible).mp h₂
  exact ⟨A₁, ⟨e₁⟩, ⟨e.trans e₂⟩⟩

/-- **Derived supercuspidal gamma compatibility.** For every local-constant
system and every supercuspidal map, the pair L- and epsilon-factor conditions and
dual compatibility imply pair gamma compatibility for the same system and map. -/
theorem supercuspidalGammaFromFactors :
    SupercuspidalGammaFromFactorsStatement.{uF, uP, uA} F := by
  intro eC ε hε c hfac hdual ψ r n σ τ
  obtain ⟨hνex, hfacν⟩ := hfac ψ r n σ τ
  refine ⟨hνex, fun ν hν => ?_⟩
  obtain ⟨⟨P, hP, hPL⟩, e, he, heA⟩ := hfacν ν hν
  have hν' : IsSelfDualMeasure F (ψ.scale (-1)) ν :=
    (RankinSelberg.DominantRankTransport.negatedSelfDualHaar F ψ ⟨ν, hν⟩).property
  obtain ⟨⟨P', hP', hP'L⟩, -⟩ := (hfac (ψ.scale (-1)) r n
    (FiniteRepresentation.continuousIrreducibleDualEquiv (r.succPNat : ℕ) σ)
    (FiniteRepresentation.continuousIrreducibleDualEquiv (n.succPNat : ℕ) τ)).2 ν hν'
  refine ⟨RankinSelberg.rationalGammaExpression (residueReflection F) e.1 e.2 P P', ?_,
    e.1, e.2, heA, ?_⟩
  · obtain ⟨Aσ, hAσ⟩ := Quotient.exists_rep (c r.succPNat σ)
    obtain ⟨Aτ, hAτ⟩ := Quotient.exists_rep (c n.succPNat τ)
    obtain ⟨Aσ', hAσ'⟩ := Quotient.exists_rep (c r.succPNat
      (FiniteRepresentation.continuousIrreducibleDualEquiv (r.succPNat : ℕ) σ))
    obtain ⟨Aτ', hAτ'⟩ := Quotient.exists_rep (c n.succPNat
      (FiniteRepresentation.continuousIrreducibleDualEquiv (n.succPNat : ℕ) τ))
    have hdσ := hdual r.succPNat σ
    have hdτ := hdual n.succPNat τ
    rw [← hAσ, ← hAσ'] at hdσ
    rw [← hAτ, ← hAτ'] at hdτ
    obtain ⟨Bσ, ⟨eσ⟩, ⟨dσ⟩⟩ := exists_equiv_of_isSupercuspidalSmoothDual F Aσ Aσ' hdσ
    obtain ⟨Bτ, ⟨eτ⟩, ⟨dτ⟩⟩ := exists_equiv_of_isSupercuspidalSmoothDual F Aτ Aτ' hdτ
    obtain ⟨eσσ, heσσ, -⟩ := ((hfac ψ r r σ σ).2 ν hν).2
    obtain ⟨eττ, heττ, -⟩ := ((hfac ψ n n τ τ).2 ν hν).2
    rw [← hAσ] at heσσ
    rw [← hAτ] at heττ
    rw [← hAσ, ← hAτ] at he hP
    rw [← hAσ', ← hAτ'] at hP'
    have gσ := RankinSelberg.isGeneric_of_isPadicSymmetricEpsilonFactor_self F ψ ν
      Bσ.obj.representation Bσ.property.1 Bσ.property.2
      ((RankinSelberg.IsPadicSymmetricEpsilonFactor.congr_equiv eσ eσ).mpr heσσ)
    have gτ := RankinSelberg.isGeneric_of_isPadicSymmetricEpsilonFactor_self F ψ ν
      Bτ.obj.representation Bτ.property.1 Bτ.property.2
      ((RankinSelberg.IsPadicSymmetricEpsilonFactor.congr_equiv eτ eτ).mpr heττ)
    rw [← hAσ, ← hAτ]
    exact (RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv eσ eτ).mp
      (RankinSelberg.isPadicSymmetricGammaFactor_of_smoothDual F ψ ⟨ν, hν⟩
        Bσ.obj.representation Bτ.obj.representation
        Aσ'.obj.representation Aτ'.obj.representation gσ gτ dσ dτ
        ((RankinSelberg.IsPadicSymmetricEpsilonFactor.congr_equiv eσ eτ).mpr he)
        ((RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv eσ eτ).mpr hP) hP')
  · rw [rationalLRatioClass_tensor_weilPairClass, hPL, hP'L, map_inv₀,
      RationalReflection.subst_polynomial, inv_div_inv]
    unfold RankinSelberg.rationalGammaExpression
    rw [mul_div_assoc]

end Main

end Langlands.Correspondence
