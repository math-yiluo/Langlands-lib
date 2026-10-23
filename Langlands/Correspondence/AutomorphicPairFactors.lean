import Langlands.Correspondence.FullFactorCompatibility
import Langlands.Representation.RankinSelberg.LanglandsLFactor
import Langlands.Representation.Classification.SupercuspidalContragredientAux

/-!
# Certified pair factors on automorphic classes

Transport the existing square-integrable quotient certificates across actual
representation equivalences. This gives representative independence and
uniqueness on automorphic classes, without asserting factor totality.
-/

noncomputable section

namespace Langlands

universe uG uV uW uF uA

open PadicField.TopologicalData Polynomial

namespace Classification

/-- Transport an irreducible quotient along an equivalence of its target. -/
theorem IsIrreducibleQuotient.of_target_equiv
    {G : Type uG} [Group G] {V W W' : Type uV}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    {π' : Representation ℂ G W'} (e : π.Equiv π')
    (h : IsIrreducibleQuotient ρ π) : IsIrreducibleQuotient ρ π' := by
  obtain ⟨hπ, q, hq⟩ := h
  refine ⟨(isIrreducible_iff_of_equiv e).mp hπ, e.toIntertwiningMap.comp q, ?_⟩
  exact e.surjective.comp hq

end Classification

namespace PadicField.TopologicalData.SquareIntegrableLanglandsDatum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData} {n : ℕ}

/-- The same square-integrable datum presents either of two equivalent targets. -/
theorem isLanglandsQuotient_iff_of_equiv
    (d : SquareIntegrableLanglandsDatum.{uV, uF} T n)
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (e : letI := T.topology; π.representation.Equiv π'.representation) :
    d.IsLanglandsQuotient π ↔ d.IsLanglandsQuotient π' := by
  let := T.topology
  exact ⟨Classification.IsIrreducibleQuotient.of_target_equiv e,
    Classification.IsIrreducibleQuotient.of_target_equiv e.symm⟩

end PadicField.TopologicalData.SquareIntegrableLanglandsDatum

namespace PadicField.TopologicalData.TemperedLanglandsDatum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData} {n : ℕ}

/-- The same tempered datum presents either of two equivalent targets. -/
theorem isLanglandsQuotient_iff_of_equiv
    (d : TemperedLanglandsDatum.{uV, uF} T n)
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (e : letI := T.topology; π.representation.Equiv π'.representation) :
    d.IsLanglandsQuotient π ↔ d.IsLanglandsQuotient π' := by
  let := T.topology
  exact ⟨Classification.IsIrreducibleQuotient.of_target_equiv e,
    Classification.IsIrreducibleQuotient.of_target_equiv e.symm⟩

end PadicField.TopologicalData.TemperedLanglandsDatum

namespace RankinSelberg

open HarmonicAnalysis MeasureTheory

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance pairFactorTransportFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology

variable {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r t : ℕ}
  {π π' : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
  {σ σ' : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier)}

/-- Equivalence of either representation preserves the epsilon certificate,
with exactly the same two block universes and the same block factors. -/
theorem IsLanglandsPairEpsilonFactor.congr_equiv
    (a : π.representation.Equiv π'.representation)
    (b : σ.representation.Equiv σ'.representation) {e : ℂˣ × ℤ} :
    IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e ↔
      IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π' σ' e := by
  have transport : ∀ {π π' : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
      {σ σ' : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier)},
      π.representation.Equiv π'.representation →
      σ.representation.Equiv σ'.representation →
      IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e →
      IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π' σ' e := by
    intro π π' σ σ' a b h
    obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩, hall⟩ := h
    refine ⟨⟨d, (d.isLanglandsQuotient_iff_of_equiv a).mp hd⟩,
      ⟨d', (d'.isLanglandsQuotient_iff_of_equiv b).mp hd'⟩, ?_⟩
    intro c c' hc hc'
    exact hall c c' ((c.isLanglandsQuotient_iff_of_equiv a).mpr hc)
      ((c'.isLanglandsQuotient_iff_of_equiv b).mpr hc')
  exact ⟨transport a b, transport a.symm b.symm⟩

/-- Equivalence of either representation preserves the L-polynomial certificate,
with exactly the same two block universes and the same standard modules. -/
theorem IsLanglandsPairLPolynomial.congr_equiv
    (a : π.representation.Equiv π'.representation)
    (b : σ.representation.Equiv σ'.representation) {e : ℂ[X]} :
    IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ e ↔
      IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π' σ' e := by
  have transport : ∀ {π π' : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
      {σ σ' : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier)},
      π.representation.Equiv π'.representation →
      σ.representation.Equiv σ'.representation →
      IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ e →
      IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π' σ' e := by
    intro π π' σ σ' a b h
    obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩, hall⟩ := h
    refine ⟨⟨d, (d.isLanglandsQuotient_iff_of_equiv a).mp hd⟩,
      ⟨d', (d'.isLanglandsQuotient_iff_of_equiv b).mp hd'⟩, ?_⟩
    intro c c' hc hc'
    exact hall c c' ((c.isLanglandsQuotient_iff_of_equiv a).mpr hc)
      ((c'.isLanglandsQuotient_iff_of_equiv b).mpr hc')
  exact ⟨transport a b, transport a.symm b.symm⟩

end RankinSelberg

namespace Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance automorphicPairFactorFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance automorphicPairFactorGeneralLinearTopology (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

variable {ψ : NontrivialAdditiveCharacter F} {ν : LocalAdditiveHaarMeasure F}
  {r t : ℕ}

/-- The existential class relation is equivalent to the representation relation
on any supplied representatives and equivalent saturated carriers. -/
theorem isAutomorphicPairEpsilonFactor_iff
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (A' : AutomorphicObject.{uF, uA} F t.succPNat)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (t + 1) F.Carrier))
    (a : J.representation.Equiv A.obj.representation)
    (a' : J'.representation.Equiv A'.obj.representation) {e : ℂˣ × ℤ} :
    IsAutomorphicPairEpsilonFactor F ψ ν (automorphicClassOf F A)
      (automorphicClassOf F A') e ↔
      RankinSelberg.IsLanglandsPairEpsilonFactor.{uF, uA, uA} F ψ ν J J' e := by
  constructor
  · rintro ⟨B, B', K, K', hB, hB', ⟨b⟩, ⟨b'⟩, h⟩
    obtain ⟨c⟩ := (automorphicClassOf_eq_iff F B A).mp hB
    obtain ⟨c'⟩ := (automorphicClassOf_eq_iff F B' A').mp hB'
    exact (RankinSelberg.IsLanglandsPairEpsilonFactor.congr_equiv
      ((b.trans c).trans a.symm) ((b'.trans c').trans a'.symm)).mp h
  · intro h
    exact ⟨A, A', J, J', rfl, rfl, ⟨a⟩, ⟨a'⟩, h⟩

/-- The existential class relation is equivalent to the representation relation
on any supplied representatives and equivalent saturated carriers. -/
theorem isAutomorphicPairLPolynomial_iff
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (A' : AutomorphicObject.{uF, uA} F t.succPNat)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (t + 1) F.Carrier))
    (a : J.representation.Equiv A.obj.representation)
    (a' : J'.representation.Equiv A'.obj.representation) {e : ℂ[X]} :
    IsAutomorphicPairLPolynomial F ψ ν (automorphicClassOf F A)
      (automorphicClassOf F A') e ↔
      RankinSelberg.IsLanglandsPairLPolynomial.{uF, uA, uA} F ψ ν J J' e := by
  constructor
  · rintro ⟨B, B', K, K', hB, hB', ⟨b⟩, ⟨b'⟩, h⟩
    obtain ⟨c⟩ := (automorphicClassOf_eq_iff F B A).mp hB
    obtain ⟨c'⟩ := (automorphicClassOf_eq_iff F B' A').mp hB'
    exact (RankinSelberg.IsLanglandsPairLPolynomial.congr_equiv
      ((b.trans c).trans a.symm) ((b'.trans c').trans a'.symm)).mp h
  · intro h
    exact ⟨A, A', J, J', rfl, rfl, ⟨a⟩, ⟨a'⟩, h⟩

variable {F}

/-- A class pair has at most one certified coefficient/exponent pair. -/
theorem IsAutomorphicPairEpsilonFactor.unique
    {π : AutomorphicClass.{uF, uA} F r.succPNat}
    {π' : AutomorphicClass.{uF, uA} F t.succPNat} {e e' : ℂˣ × ℤ}
    (h : IsAutomorphicPairEpsilonFactor F ψ ν π π' e)
    (h' : IsAutomorphicPairEpsilonFactor F ψ ν π π' e') : e = e' := by
  obtain ⟨A, A', J, J', rfl, rfl, ⟨a⟩, ⟨a'⟩, he⟩ := h
  exact he.unique ((isAutomorphicPairEpsilonFactor_iff F A A' J J' a a').mp h')

/-- A class pair has at most one certified L-polynomial. -/
theorem IsAutomorphicPairLPolynomial.unique
    {π : AutomorphicClass.{uF, uA} F r.succPNat}
    {π' : AutomorphicClass.{uF, uA} F t.succPNat} {e e' : ℂ[X]}
    (h : IsAutomorphicPairLPolynomial F ψ ν π π' e)
    (h' : IsAutomorphicPairLPolynomial F ψ ν π π' e') : e = e' := by
  obtain ⟨A, A', J, J', rfl, rfl, ⟨a⟩, ⟨a'⟩, he⟩ := h
  exact he.unique ((isAutomorphicPairLPolynomial_iff F A A' J J' a a').mp h')


/-- Every certified class L-polynomial has constant coefficient one. -/
theorem IsAutomorphicPairLPolynomial.coeff_zero
    {π : AutomorphicClass.{uF, uA} F r.succPNat}
    {π' : AutomorphicClass.{uF, uA} F t.succPNat} {P : ℂ[X]}
    (h : IsAutomorphicPairLPolynomial F ψ ν π π' P) : P.coeff 0 = 1 := by
  obtain ⟨A, A', J, J', _, _, _, _, hP⟩ := h
  exact hP.coeff_zero

/-- Normalization makes the class L-polynomial nonzero. -/
theorem IsAutomorphicPairLPolynomial.ne_zero
    {π : AutomorphicClass.{uF, uA} F r.succPNat}
    {π' : AutomorphicClass.{uF, uA} F t.succPNat} {P : ℂ[X]}
    (h : IsAutomorphicPairLPolynomial F ψ ν π π' P) : P ≠ 0 := by
  intro hP
  have hc := h.coeff_zero
  simp [hP] at hc

/-- The rational unit `1 / P(X)` attached to a certified class L-polynomial. -/
def automorphicPairLFactor
    {π : AutomorphicClass.{uF, uA} F r.succPNat}
    {π' : AutomorphicClass.{uF, uA} F t.succPNat}
    (P : {P : ℂ[X] // IsAutomorphicPairLPolynomial F ψ ν π π' P}) :
    RankinSelberg.RationalFunctionsˣ :=
  (Units.mk0 (algebraMap ℂ[X] RankinSelberg.RationalFunctions P.val)
    (RatFunc.algebraMap_ne_zero P.property.ne_zero))⁻¹

theorem coe_automorphicPairLFactor
    {π : AutomorphicClass.{uF, uA} F r.succPNat}
    {π' : AutomorphicClass.{uF, uA} F t.succPNat}
    (P : {P : ℂ[X] // IsAutomorphicPairLPolynomial F ψ ν π π' P}) :
    (automorphicPairLFactor P : RankinSelberg.RationalFunctions) =
      (algebraMap ℂ[X] RankinSelberg.RationalFunctions P.val)⁻¹ := rfl

/-- The resulting rational unit is independent of the certificate chosen. -/
theorem automorphicPairLFactor_eq
    {π : AutomorphicClass.{uF, uA} F r.succPNat}
    {π' : AutomorphicClass.{uF, uA} F t.succPNat}
    (P Q : {P : ℂ[X] // IsAutomorphicPairLPolynomial F ψ ν π π' P}) :
    automorphicPairLFactor P = automorphicPairLFactor Q := by
  have h : P = Q := Subtype.ext (P.property.unique Q.property)
  rw [h]

variable (F) (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)

/-- Construct a certified class epsilon factor from representatives with
quotient data, block-factor existence and datum independence. -/
def automorphicPairEpsilonFactor
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (A' : AutomorphicObject.{uF, uA} F t.succPNat)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (t + 1) F.Carrier))
    (a : J.representation.Equiv A.obj.representation)
    (a' : J'.representation.Equiv A'.obj.representation)
    (hJ : ∃ d : SquareIntegrableLanglandsDatum.{uA, uF}
      F.canonicalTopologicalData (r + 1), d.IsLanglandsQuotient J)
    (hJ' : ∃ d : SquareIntegrableLanglandsDatum.{uA, uF}
      F.canonicalTopologicalData (t + 1), d.IsLanglandsQuotient J')
    (hb : RankinSelberg.LanglandsPairEpsilonBlockExistence.{uF, uA, uA} F ψ ν J J')
    (hi : RankinSelberg.LanglandsPairEpsilonDataIndependence.{uF, uA, uA} F ψ ν J J') :
    {e : ℂˣ × ℤ // IsAutomorphicPairEpsilonFactor F ψ ν
      (automorphicClassOf F A) (automorphicClassOf F A') e} := by
  let e := RankinSelberg.langlandsPairEpsilonFactor F ψ ν J J' hJ hJ' hb hi
  exact ⟨e.val, (isAutomorphicPairEpsilonFactor_iff F A A' J J' a a').mpr e.property⟩

end Correspondence
end Langlands
