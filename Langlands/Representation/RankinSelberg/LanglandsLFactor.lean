import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.Classification.RegularLanglandsStatement
import Mathlib.Order.Fin.Basic

/-!
# Constructing L-factors through tempered Langlands data

Ordered block matching gives an actual isomorphism of standard modules.
The published regular classification statements and standard-module factor
existence then construct a polynomial satisfying the existing nongeneric relation.
-/

noncomputable section

namespace Langlands

open CategoryTheory MeasureTheory HarmonicAnalysis Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

namespace PadicField.TopologicalData.TemperedLanglandsDatum

/-- Ordered matching of block ranks, exponents and representation classes
induces an isomorphism of the actual standard modules. -/
theorem nonempty_standardModule_iso_of_matching
    {F : PadicField.{uF} p} {T : F.TopologicalData} {n : ℕ}
    (d e : TemperedLanglandsDatum.{uV, uF} T n)
    (a : Fin d.shape.length ≃o Fin e.shape.length)
    (h : ∀ i, d.shape.size i = e.shape.size (a i))
    (hb : ∀ i, d.exponent i = e.exponent (a i) ∧
      Nonempty ((h i ▸ d.blocks i) ≅ e.blocks (a i))) :
    Nonempty (d.standardModule ≅ e.standardModule) := by
  let := T.topology
  rcases d with ⟨⟨l, s, hp, hs⟩, b, hi, ht, x, hx⟩
  rcases e with ⟨⟨l', s', hp', hs'⟩, b', hi', ht', x', hx'⟩
  have hl : l = l' := by
    simpa only [Fintype.card_fin] using Fintype.card_congr a.toEquiv
  subst l'
  have ha : a = OrderIso.refl (Fin l) := by
    ext i
    exact Fin.coe_orderIso_apply a i
  subst a
  change ∀ i, s i = s' i at h
  have hsizes : s = s' := funext h
  subst s'
  change ∀ i, x i = x' i ∧ Nonempty (b i ≅ b' i) at hb
  have hexponents : x = x' := funext fun i => (hb i).1
  subst x'
  exact ⟨T.twistedProductInducedIso _ (fun i => (hb i).2.some) x⟩

end PadicField.TopologicalData.TemperedLanglandsDatum

namespace RankinSelberg

open PadicField.TopologicalData

section Normalization

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r t : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
  {P : ℂ[X]}

/-- The p-adic relation inherits the normalization of its integral generator. -/
theorem IsPadicPairLPolynomial.coeff_zero (h : IsPadicPairLPolynomial F ψ ν π σ P) :
    P.coeff 0 = 1 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (GeneralLinear.upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (GeneralLinear.upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  obtain ⟨⟨_, μ, hμ⟩, hP⟩ := h
  exact (hP μ hμ).coeff_zero

/-- Reading the larger rank first preserves the constant-term normalization. -/
theorem IsPadicSymmetricLPolynomial.coeff_zero
    (h : IsPadicSymmetricLPolynomial F ψ ν π σ P) : P.coeff 0 = 1 := by
  unfold IsPadicSymmetricLPolynomial at h
  split_ifs at h
  · exact h.coeff_zero
  · exact h.coeff_zero

end Normalization

section Certified

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r t : ℕ}
  {π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
  {σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}

/-- A nongeneric L-polynomial is normalized because presenting data exist. -/
theorem IsLanglandsPairLPolynomial.coeff_zero {P : ℂ[X]}
    (h : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P) : P.coeff 0 = 1 := by
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, hP⟩ := h
  exact (hP d e hd he).coeff_zero

theorem IsLanglandsPairLPolynomial.ne_zero {P : ℂ[X]}
    (h : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P) : P ≠ 0 := by
  intro hP
  have := h.coeff_zero
  simp [hP] at this

/-- The actual nonzero rational function `1 / P(X)` of a certified nongeneric
L-polynomial. Its spectral convention is `X = q^(-s)`. -/
def langlandsPairLFactor
    (P : {P : ℂ[X] // IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P}) :
    RationalFunctionsˣ :=
  (Units.mk0 (algebraMap ℂ[X] RationalFunctions P.val)
    (RatFunc.algebraMap_ne_zero P.property.ne_zero))⁻¹

theorem coe_langlandsPairLFactor
    (P : {P : ℂ[X] // IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P}) :
    (langlandsPairLFactor P : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P.val)⁻¹ := rfl

/-- The rational unit is independent of the certified polynomial witness. -/
theorem langlandsPairLFactor_eq
    (P Q : {P : ℂ[X] // IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P}) :
    langlandsPairLFactor P = langlandsPairLFactor Q := by
  have h : P = Q := Subtype.ext (P.property.unique Q.property)
  rw [h]

end Certified

section Input

variable (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r t : ℕ}
  (π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
  (σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))

/-- The remaining analytic obligation on standard modules presenting this pair.
This is existence of their published integral-based L-polynomial, with no
asserted agreement between different presentations. -/
def LanglandsStandardLPolynomialExistence : Prop :=
  ∀ (d : TemperedLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1))
    (e : TemperedLanglandsDatum.{uW, uF} F.canonicalTopologicalData (t + 1)),
    d.IsLanglandsQuotient π → e.IsLanglandsQuotient σ →
      ∃ P : ℂ[X], letI := F.canonicalTopologicalData.topology
        IsPadicSymmetricLPolynomial F ψ ν d.standardModule.representation
          e.standardModule.representation P

end Input

/-- The published JPSS standard-module product statement supplies the analytic
input when that statement is proved; no product law is proved here. -/
theorem LanglandsTypeLFactorStatement.standardLPolynomialExistence
    (h : LanglandsTypeLFactorStatement.{uF, uV, uW})
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ}
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)) :
    LanglandsStandardLPolynomialExistence.{uF, uV, uW} F ψ ν.val π σ := by
  intro d e _ _
  obtain ⟨P, _, hP, _, _⟩ := h p F ψ ν r t d e
  exact ⟨P, hP⟩

section Construction

variable (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r t : ℕ}
  (π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
  (σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))

/-- Ordered-data uniqueness makes any two standard modules presenting the same
irreducible representation isomorphic. Classification remains an input. -/
theorem standardModule_iso_of_regular_uniqueness
    (hcl : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (d e : TemperedLanglandsDatum.{max uF uV, uF}
      F.canonicalTopologicalData (r + 1))
    (hd : d.IsLanglandsQuotient π) (he : e.IsLanglandsQuotient π) :
    Nonempty (d.standardModule ≅ e.standardModule) := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨a, h, hb⟩ := hcl p F F.canonicalTopologicalData (r + 1)
    (Nat.succ_pos r) d e π π hd he ⟨Iso.refl π⟩
  exact d.nonempty_standardModule_iso_of_matching e a h hb

/-- Construct a certified polynomial from one standard-module pair. The
classification inputs prove its certificate for every presenting datum pair. -/
def langlandsPairLPolynomialOfData
    (d : TemperedLanglandsDatum.{max uF uV, uF}
      F.canonicalTopologicalData (r + 1))
    (e : TemperedLanglandsDatum.{max uF uW, uF}
      F.canonicalTopologicalData (t + 1))
    (hd : d.IsLanglandsQuotient π) (he : e.IsLanglandsQuotient σ)
    (hclπ : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (hclσ : GLRegularLanglandsDataUniquenessStatement.{uF, uW})
    (hP : ∃ P : ℂ[X], letI := F.canonicalTopologicalData.topology
      IsPadicSymmetricLPolynomial F ψ ν d.standardModule.representation
        e.standardModule.representation P) :
    {P : ℂ[X] // IsLanglandsPairLPolynomial.{uF, max uF uV, max uF uW}
      F ψ ν π σ P} := by
  let := F.canonicalTopologicalData.topology
  refine ⟨hP.choose, ⟨d, hd⟩, ⟨e, he⟩, ?_⟩
  intro d' e' hd' he'
  obtain ⟨a⟩ := standardModule_iso_of_regular_uniqueness F π hclπ d d' hd hd'
  obtain ⟨b⟩ := standardModule_iso_of_regular_uniqueness F σ hclσ e e' he he'
  exact (IsPadicSymmetricLPolynomial.congr_equiv
    (SmoothRep.equivOfIso a) (SmoothRep.equivOfIso b)).mp hP.choose_spec

/-- Construct the nongeneric L-polynomial using explicit exhaustion, ordered
classification and standard-module analytic existence. -/
def langlandsPairLPolynomialOfClassification
    (hπ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible π.representation)
    (hσ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible σ.representation)
    (haπ : letI := F.canonicalTopologicalData.topology; IsAdmissible π.representation)
    (haσ : letI := F.canonicalTopologicalData.topology; IsAdmissible σ.representation)
    (hexπ : GLRegularLanglandsExhaustionStatement.{uF, uV})
    (hexσ : GLRegularLanglandsExhaustionStatement.{uF, uW})
    (hclπ : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (hclσ : GLRegularLanglandsDataUniquenessStatement.{uF, uW})
    (hf : LanglandsStandardLPolynomialExistence.{uF, max uF uV, max uF uW}
      F ψ ν π σ) :
    {P : ℂ[X] // IsLanglandsPairLPolynomial.{uF, max uF uV, max uF uW}
      F ψ ν π σ P} := by
  have hd := hexπ p F F.canonicalTopologicalData (r + 1) (Nat.succ_pos r) π hπ haπ
  have he := hexσ p F F.canonicalTopologicalData (t + 1) (Nat.succ_pos t) σ hσ haσ
  exact langlandsPairLPolynomialOfData F ψ ν π σ hd.choose he.choose
    hd.choose_spec.isLanglandsQuotient he.choose_spec.isLanglandsQuotient hclπ hclσ
    (hf hd.choose he.choose hd.choose_spec.isLanglandsQuotient
      he.choose_spec.isLanglandsQuotient)

end Construction

end RankinSelberg

end Langlands
