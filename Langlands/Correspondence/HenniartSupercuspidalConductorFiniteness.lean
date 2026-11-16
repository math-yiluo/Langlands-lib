import Langlands.Representation.Conductor.SupercuspidalPadicGenericConductor
import Langlands.Correspondence.HenniartConductorFinitenessProof
import Langlands.Correspondence.PadicSupercuspidalFinitenessProof

/-!
# Henniart candidate finiteness from the supercuspidal p-adic conductor premise

These are the conductor comparison and candidate-finiteness arguments of Henniart's
route with the conductor premise restricted to supercuspidal p-adic representations.
-/

noncomputable section

namespace Langlands.Henniart.Extension.SupercuspidalConductor

open Langlands.Correspondence StableMap HarmonicAnalysis

universe uK uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartSupercuspidalConductorTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance henniartSupercuspidalConductorValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance henniartSupercuspidalConductorLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- Bushnell–Henniart–Kutzko and JPSS (5.1): if `c q^(-ms)` is the epsilon factor of a
supercuspidal `π` of `GL_(k+1)(K)` against the trivial character of `GL_1(K)`, for
`ψ` and a measure self-dual for `ψ`, then `m - (k+1) n(ψ)` is a natural number `b`
and `b` is the least level with nonzero fixed vectors. -/
theorem exists_newvectorConductor_of_pairEpsilon
    (hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0})
    (hJPSS : Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV})
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν) {k : ℕ}
    (A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := k + 1))
    {c : ℂˣ} {m : ℤ}
    (h : RankinSelberg.IsPadicSymmetricEpsilonFactor K ψ ν A.obj.representation
      (rankOneSupercuspidalObject.{uK, uV} K 1).obj.representation (c, m)) :
    ∃ b : ℕ, (b : ℤ) = m - ((k + 1 : ℕ) : ℤ) * K.canonicalTopologicalData.additiveConductor ψ ∧
      Conductor.IsNewvectorConductor A.obj.representation b := by
  have h' : RankinSelberg.IsPadicPairEpsilonFactor K ψ ν A.obj.representation
      (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) (c, m) :=
    (RankinSelberg.isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le k)).mp
      ((RankinSelberg.IsPadicSymmetricEpsilonFactor.congr_equiv
        (Representation.Equiv.refl _) (trivialRankOneEquiv K)).mp h)
  have hA : Whittaker.IsGeneric (ψ : UnitaryAdditiveCharacter K.Carrier) k
      A.obj.representation :=
    RankinSelberg.SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal K ψ k
      A.obj A.property.1 A.property.2
  obtain ⟨a, hψ₀⟩ := RankinSelberg.UnramifiedUnitary.exists_scale_hasIntegerConductor K ψ
  have hA₀ : Whittaker.IsGeneric ((ψ : UnitaryAdditiveCharacter K.Carrier).scale a) k
      A.obj.representation :=
    RankinSelberg.SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal K _ k
      A.obj A.property.1 A.property.2
  have hψeq := Conductor.genericConductor_eq K ψ A.obj.representation hA ν hν h'
  have hind : Conductor.genericConductor K ψ A.obj.representation hA =
      Conductor.genericConductor K ((ψ : UnitaryAdditiveCharacter K.Carrier).scale a)
        A.obj.representation hA₀ :=
    Conductor.genericPairConductor_eq_of_pairEpsilonExponentStatement K hBHK
      A.obj.representation (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) _ _ hA
      (RankinSelberg.UniformRankOneTwist.isGeneric_rankOneCharacter_one K _) hA₀
      (RankinSelberg.UniformRankOneTwist.isGeneric_rankOneCharacter_one K _)
  obtain ⟨b, hb, hnew, -⟩ :=
    Conductor.genericConductor_isNewvectorConductor_of_supercuspidalPadic K hJPSS
      _ hψ₀ A.obj.representation hA₀ A.property.2
  exact ⟨b, by rw [← hb, ← hind, hψeq], hnew⟩

/-- Henniart (2000), §4.3: the finiteness of the candidate sets, from
Bushnell–Henniart–Kutzko's dependence of the epsilon exponent on `ψ` and JPSS (5.1);
Bernstein–Zelevinsky's bounded-level finiteness over p-adic fields is
`CompactOpenFiniteness.centralLevelStratum_finite`. -/
theorem supercuspidalEpsilonConductorFiniteness_of_pairEpsilon
    (hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0})
    (hJPSS : Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV}) :
    SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV} := by
  intro p _ K ψ ν hν k ω m
  have hbij : Function.Bijective
      (GeneralLinear.scalarToCenter : K.Carrierˣ →*
        Subgroup.center (GeneralLinear (k + 1) K.Carrier)) := by
    constructor
    · intro a b hab
      exact (GeneralLinear.scalarEmbedding (Nat.succ_pos k)).injective
        (congrArg Subtype.val hab)
    · intro z
      have hz := z.property
      simp only [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨a, ha⟩ := hz
      exact ⟨a, Subtype.ext ha⟩
  let e : K.Carrierˣ ≃* Subgroup.center (GeneralLinear (k + 1) K.Carrier) :=
    MulEquiv.ofBijective GeneralLinear.scalarToCenter hbij
  let χ : Subgroup.center (GeneralLinear (k + 1) K.Carrier) →* ℂˣ :=
    ω.comp e.symm.toMonoidHom
  let b : ℕ := (m - ((k + 1 : ℕ) : ℤ) * K.canonicalTopologicalData.additiveConductor ψ).toNat
  refine (CompactOpenFiniteness.centralLevelStratum_finite.{uK, uV} K k χ b).subset ?_
  rintro π ⟨hω, c, hε⟩
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨b', hb', hnew⟩ := exists_newvectorConductor_of_pairEpsilon K hBHK hJPSS ψ ν hν A hε
  have hbb : b = b' := by
    change (m - _).toNat = b'
    rw [← hb']
    exact Int.toNat_natCast b'
  refine ⟨?_, ?_⟩
  · intro z v
    obtain ⟨a, rfl⟩ := e.surjective z
    change A.obj.representation (GeneralLinear.scalar a) v = (ω (e.symm (e a)) : ℂ) • v
    rw [e.symm_apply_apply]
    exact (supercuspidalCentralActsBy_iff K (n := k.succPNat) A a (ω a)).mp (hω a) v
  · change Conductor.firstFixedLevel A.obj.representation ≤ (b : WithTop ℕ)
    rw [Conductor.firstFixedLevel_le_iff, hbb]
    exact hnew.1

end Langlands.Henniart.Extension.SupercuspidalConductor
