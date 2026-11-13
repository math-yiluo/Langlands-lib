import Langlands.Representation.RankinSelberg.FieldTransport.Padic
import Langlands.Global.Factors.RelativeIsometryFactorStatement
import Langlands.LocalFactor.Abelian.Transport
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransportLattice

/-!
# Supercuspidal pair-factor relations along an isomorphism of p-adic fields

For an isomorphism `f : F ≃ₐ[ℚ_p] E` of p-adic fields, pullback of supercuspidal
classes from `E` to `F` preserves and reflects the JPSS pair L-polynomial and
epsilon relations on classes, on unitary basis classes, and the virtual pair
L-factor and epsilon relations on the unitary lattices, provided the additive
character and additive Haar measure of `E` are those transported from `F`
along `f`.
-/

noncomputable section

open MeasureTheory Polynomial

universe uF uE uV uW

namespace Langlands.Correspondence

open Langlands.RankinSelberg.FieldTransport

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {E : PadicField.{uE} p}

/-- Pullback of supercuspidal classes of `GL_n(E)` to `GL_n(F)` along an
isomorphism of p-adic fields, for the canonical topologies. -/
def padicClassPullback (f : F.Carrier ≃ₐ[Padic p] E.Carrier) (n : ℕ) :
    (letI := E.canonicalTopologicalData.topology;
      GeneralLinear.SupercuspidalClass.{uV, uE} (F := E.Carrier) (n := n)) →
    (letI := F.canonicalTopologicalData.topology;
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :=
  letI := F.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.topology
  GeneralLinear.SupercuspidalClass.fieldPullback f.toRingEquiv
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv F E f)
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv E F f.symm)

variable {f : F.Carrier ≃ₐ[Padic p] E.Carrier}

/-- **Supercuspidal pair L-polynomials along an isomorphism of p-adic fields.**
For an additive character and an additive Haar measure of `E` related to those
of `F` by `f`, `P` is the pair L-polynomial of the pulled-back classes over `F`
exactly when it is the pair L-polynomial of the classes over `E`. -/
theorem isSupercuspidalPairLPolynomial_padicClassPullback_iff
    {ψ : NontrivialAdditiveCharacter F} {ψ' : NontrivialAdditiveCharacter E}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : LocalAdditiveHaarMeasure F} {ν' : LocalAdditiveHaarMeasure E}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    {r n : ℕ} (π : PadicField.SupercuspidalClass.{uV, uE} E (r + 1) (Nat.succ_pos r))
    (τ : PadicField.SupercuspidalClass.{uW, uE} E (n + 1) (Nat.succ_pos n)) (P : ℂ[X]) :
    IsSupercuspidalPairLPolynomial F ψ ν (padicClassPullback f (r + 1) π)
        (padicClassPullback f (n + 1) τ) P ↔
      IsSupercuspidalPairLPolynomial E ψ' ν' π τ P := by
  induction π, τ using Quotient.inductionOn₂ with
  | h A B =>
    exact (isPadicSymmetricLPolynomial_comp_iff hψ hν _ _ P).symm

/-- **Supercuspidal pair epsilon factors along an isomorphism of p-adic
fields.** For an additive character and an additive Haar measure of `E` related
to those of `F` by `f`, `e` is the pair epsilon factor of the pulled-back
classes over `F` exactly when it is the pair epsilon factor of the classes over
`E`. -/
theorem isSupercuspidalPairEpsilonFactor_padicClassPullback_iff
    {ψ : NontrivialAdditiveCharacter F} {ψ' : NontrivialAdditiveCharacter E}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : LocalAdditiveHaarMeasure F} {ν' : LocalAdditiveHaarMeasure E}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    {r n : ℕ} (π : PadicField.SupercuspidalClass.{uV, uE} E (r + 1) (Nat.succ_pos r))
    (τ : PadicField.SupercuspidalClass.{uW, uE} E (n + 1) (Nat.succ_pos n)) (e : ℂˣ × ℤ) :
    IsSupercuspidalPairEpsilonFactor F ψ ν (padicClassPullback f (r + 1) π)
        (padicClassPullback f (n + 1) τ) e ↔
      IsSupercuspidalPairEpsilonFactor E ψ' ν' π τ e := by
  induction π, τ using Quotient.inductionOn₂ with
  | h A B =>
    exact (isPadicSymmetricEpsilonFactor_comp_iff hψ hν _ _ e).symm

end Langlands.Correspondence

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {E : PadicField.{uE} p}
  {f : F.Carrier ≃ₐ[Padic p] E.Carrier}

/-- The unitary basis bijection keeps the rank and pulls back the class. -/
theorem unitaryBasisEquiv_val (b : UnitaryBasis.{uE, uV} E) :
    (unitaryBasisEquiv F E f b).val = ⟨b.val.1, padicClassPullback f b.val.1 b.val.2⟩ := rfl

theorem unitaryBasisEquiv_mem_support_iff (x : UnitaryLattice.{uE, uV} E)
    (b : UnitaryBasis.{uE, uV} E) :
    unitaryBasisEquiv F E f b ∈ (unitaryLatticeEquiv F E f x).support ↔ b ∈ x.support := by
  rw [unitaryLatticeEquiv_eq_equivMapDomain, Finsupp.mem_support_iff, Finsupp.mem_support_iff,
    Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

/-- The JPSS pair L-polynomial relation on unitary basis classes along an
isomorphism of p-adic fields. -/
theorem isUnitaryBasisPairLPolynomial_unitaryBasisEquiv_iff
    {ψ : NontrivialAdditiveCharacter F} {ψ' : NontrivialAdditiveCharacter E}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : LocalAdditiveHaarMeasure F} {ν' : LocalAdditiveHaarMeasure E}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    (a b : UnitaryBasis.{uE, uV} E) (P : ℂ[X]) :
    IsUnitaryBasisPairLPolynomial F ψ ν (unitaryBasisEquiv F E f a)
        (unitaryBasisEquiv F E f b) P ↔
      IsUnitaryBasisPairLPolynomial E ψ' ν' a b P := by
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  exact isSupercuspidalPairLPolynomial_padicClassPullback_iff hψ hν π τ P

/-- The JPSS pair epsilon relation on unitary basis classes along an
isomorphism of p-adic fields. -/
theorem isUnitaryBasisPairEpsilonFactor_unitaryBasisEquiv_iff
    {ψ : NontrivialAdditiveCharacter F} {ψ' : NontrivialAdditiveCharacter E}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : LocalAdditiveHaarMeasure F} {ν' : LocalAdditiveHaarMeasure E}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    (a b : UnitaryBasis.{uE, uV} E) (e : ℂˣ × ℤ) :
    IsUnitaryBasisPairEpsilonFactor F ψ ν (unitaryBasisEquiv F E f a)
        (unitaryBasisEquiv F E f b) e ↔
      IsUnitaryBasisPairEpsilonFactor E ψ' ν' a b e := by
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  exact isSupercuspidalPairEpsilonFactor_padicClassPullback_iff hψ hν π τ e

/-- **Virtual pair L-factors along an isomorphism of p-adic fields.** For an
additive character and an additive Haar measure of `E` related to those of `F`
by `f`, `L` is the pair L-factor of the pulled-back unitary virtual classes
over `F` exactly when it is the pair L-factor of the classes over `E`. -/
theorem isUnitaryPairLFactor_unitaryLatticeEquiv_iff
    {ψ : NontrivialAdditiveCharacter F} {ψ' : NontrivialAdditiveCharacter E}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : LocalAdditiveHaarMeasure F} {ν' : LocalAdditiveHaarMeasure E}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    (x y : UnitaryLattice.{uE, uV} E) (L : RatFunc ℂ) :
    IsUnitaryPairLFactor F ψ ν (unitaryLatticeEquiv F E f x) (unitaryLatticeEquiv F E f y) L ↔
      IsUnitaryPairLFactor E ψ' ν' x y L := by
  set u := unitaryBasisEquiv F E f with hu
  unfold IsUnitaryPairLFactor
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨fun a b => P (u a) (u b), fun a ha b hb => ?_, ?_⟩
    · exact (isUnitaryBasisPairLPolynomial_unitaryBasisEquiv_iff hψ hν a b _).1
        (hP _ ((unitaryBasisEquiv_mem_support_iff x a).2 ha) _
          ((unitaryBasisEquiv_mem_support_iff y b).2 hb))
    · simp only [unitaryLatticeEquiv_eq_equivMapDomain, Finsupp.prod_equivMapDomain, hu]
  · rintro ⟨P, hP, rfl⟩
    refine ⟨fun a b => P (u.symm a) (u.symm b), fun a ha b hb => ?_, ?_⟩
    · rw [← u.apply_symm_apply a, unitaryBasisEquiv_mem_support_iff] at ha
      rw [← u.apply_symm_apply b, unitaryBasisEquiv_mem_support_iff] at hb
      have h := (isUnitaryBasisPairLPolynomial_unitaryBasisEquiv_iff hψ hν (u.symm a)
        (u.symm b) _).2 (hP _ ha _ hb)
      rwa [u.apply_symm_apply, u.apply_symm_apply] at h
    · simp only [unitaryLatticeEquiv_eq_equivMapDomain, Finsupp.prod_equivMapDomain, hu,
        Equiv.symm_apply_apply]

/-- **Virtual pair epsilon factors along an isomorphism of p-adic fields.** For
an additive character and an additive Haar measure of `E` related to those of
`F` by `f`, `e` is the pair epsilon factor of the pulled-back unitary virtual
classes over `F` exactly when it is the pair epsilon factor of the classes over
`E`. -/
theorem isUnitaryPairEpsilonFactor_unitaryLatticeEquiv_iff
    {ψ : NontrivialAdditiveCharacter F} {ψ' : NontrivialAdditiveCharacter E}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : LocalAdditiveHaarMeasure F} {ν' : LocalAdditiveHaarMeasure E}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    (x y : UnitaryLattice.{uE, uV} E) (e : ℂˣ × ℤ) :
    IsUnitaryPairEpsilonFactor F ψ ν (unitaryLatticeEquiv F E f x)
        (unitaryLatticeEquiv F E f y) e ↔
      IsUnitaryPairEpsilonFactor E ψ' ν' x y e := by
  set u := unitaryBasisEquiv F E f with hu
  unfold IsUnitaryPairEpsilonFactor
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun a b => c (u a) (u b), fun a ha b hb => ?_, ?_⟩
    · exact (isUnitaryBasisPairEpsilonFactor_unitaryBasisEquiv_iff hψ hν a b _).1
        (hc _ ((unitaryBasisEquiv_mem_support_iff x a).2 ha) _
          ((unitaryBasisEquiv_mem_support_iff y b).2 hb))
    · simp only [unitaryLatticeEquiv_eq_equivMapDomain, Finsupp.prod_equivMapDomain,
        Finsupp.sum_equivMapDomain, hu]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun a b => c (u.symm a) (u.symm b), fun a ha b hb => ?_, ?_⟩
    · rw [← u.apply_symm_apply a, unitaryBasisEquiv_mem_support_iff] at ha
      rw [← u.apply_symm_apply b, unitaryBasisEquiv_mem_support_iff] at hb
      have h := (isUnitaryBasisPairEpsilonFactor_unitaryBasisEquiv_iff hψ hν (u.symm a)
        (u.symm b) _).2 (hc _ ha _ hb)
      rwa [u.apply_symm_apply, u.apply_symm_apply] at h
    · simp only [unitaryLatticeEquiv_eq_equivMapDomain, Finsupp.prod_equivMapDomain,
        Finsupp.sum_equivMapDomain, hu, Equiv.symm_apply_apply]

variable (f)

/-- The virtual pair L-factor relation for the pulled-back unitary classes over
`F`, with `ψ` and `ν`, is the relation over `E` for the character and Haar
measure transported along `f`. -/
theorem isUnitaryPairLFactor_unitaryLatticeEquiv_iff_transport
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (x y : UnitaryLattice.{uE, uV} E) (L : RatFunc ℂ) :
    IsUnitaryPairLFactor F ψ ν (unitaryLatticeEquiv F E f x) (unitaryLatticeEquiv F E f y) L ↔
      IsUnitaryPairLFactor E (PadicField.ConductorTransport.additiveCharacter F E f ψ)
        (PadicField.AbelianTransport.haarMeasure F E f ν) x y L :=
  isUnitaryPairLFactor_unitaryLatticeEquiv_iff (fun z => by simp) rfl x y L

/-- The virtual pair epsilon relation for the pulled-back unitary classes over
`F`, with `ψ` and `ν`, is the relation over `E` for the character and Haar
measure transported along `f`. -/
theorem isUnitaryPairEpsilonFactor_unitaryLatticeEquiv_iff_transport
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (x y : UnitaryLattice.{uE, uV} E) (e : ℂˣ × ℤ) :
    IsUnitaryPairEpsilonFactor F ψ ν (unitaryLatticeEquiv F E f x)
        (unitaryLatticeEquiv F E f y) e ↔
      IsUnitaryPairEpsilonFactor E (PadicField.ConductorTransport.additiveCharacter F E f ψ)
        (PadicField.AbelianTransport.haarMeasure F E f ν) x y e :=
  isUnitaryPairEpsilonFactor_unitaryLatticeEquiv_iff (fun z => by simp) rfl x y e

end Langlands.VirtualRepresentation.PadicSupercuspidal
