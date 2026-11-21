import Langlands.Correspondence.AutomorphicGammaRigidity
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.Classification.UnitaryGenericExhaustionProof
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.RankinSelberg.GroupedLFactorReduction
import Langlands.Representation.RankinSelberg.LanglandsTypeReflectionData
import Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction
import Langlands.Representation.RankinSelberg.SquareIntegrableLFactorProof
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.RankinSelberg.TemperedLFactorProof
import Langlands.Representation.Unitary.ConjugateEquiv

/-! # Supercuspidality from the local Rankin–Selberg self-pair -/

noncomputable section

universe uF uV uW

set_option autoImplicit false

namespace Langlands.RankinSelberg

open Classification GeneralLinear HarmonicAnalysis LocalFactor Polynomial Whittaker
open SupercuspidalLFactorCharacterization (isOfWhittakerType_of_isSupercuspidal)

section Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance selfPairTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance selfPairGroupTopology (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

private theorem isUnitarizable_smoothContragredient {n : ℕ}
    (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier))
    (ha : A.IsAdmissible) (hu : IsUnitarizable A.representation) :
    IsUnitarizable A.contragredient.representation := by
  obtain ⟨b⟩ := hu
  let e := b.smoothDualEquiv (compactOpen_cofinal F F.canonicalTopologicalData n) ha
  exact (isUnitarizable_iff_of_conjugateEquiv
    (ρ := A.representation) (σ := A.contragredient.representation) e
    (b.toSmoothDual_apply_action ha.1)).mp ⟨b⟩

private theorem poleOrder_selfPair_supercuspidal {n : ℕ} (hn : 0 < n)
    (A : SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n)) {P : ℂ[X]}
    (hP : IsPadicRankLPolynomial F ψ ν.val A.obj.representation
      A.obj.contragredient.representation P) :
    lPolynomialPoleOrderAtZero P = 1 := by
  cases n with
  | zero => omega
  | succ r =>
    have hcof := compactOpen_cofinal F F.canonicalTopologicalData (r + 1)
    have hi := (A.obj.isIrreducible_contragredient_iff hcof A.property.2.1).mpr A.property.1
    have hsc := isSupercuspidal_smoothContragredient F F.canonicalTopologicalData
      (r + 1) A.obj A.obj.representation A.property.2
    have hw := isOfWhittakerType_of_isSupercuspidal F ψ r A.obj.contragredient hi hsc
    rw [lPolynomialPoleOrderAtZero_of_supercuspidalEqualRank supercuspidalEqualRankLFactor ν
      A.property.1 A.property.2 hi hw
      ((isPadicSymmetricLPolynomial_of_le le_rfl).mp (isPadicRankLPolynomial_succ.mp hP))]
    have hbij := (smoothAdmissibleDuality (V := A.obj) hcof).2
      A.obj.representation A.property.2.1
    have e : Nonempty (A.obj.representation.Equiv
        (smoothContragredient (smoothContragredient A.obj.representation))) :=
      ⟨(smoothBidual A.property.2.1.1).ofBijective hbij.2⟩
    exact ite_eq_left e

set_option maxHeartbeats 800000 in
/-- Each block contributes a diagonal pole at zero in the self-pair of a
normalized product of unitary supercuspidals. -/
theorem blockLength_le_selfPairPoleOrder_of_unitarySupercuspidalProduct
    {r : ℕ} (B : BlockShape (r + 1)) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V}
    (hprod : IsUnitarySupercuspidalProduct.{uF, uW, uV} F F.canonicalTopologicalData B π)
    {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial F ψ ν.val π (smoothContragredient π) P) :
    B.length ≤ lPolynomialPoleOrderAtZero P := by
  obtain ⟨A, hU, ⟨e⟩⟩ := hprod
  let T := F.canonicalTopologicalData
  let Ad (i : Fin B.length) : SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := B.size i) :=
    ⟨(A i).obj.contragredient,
      ((A i).obj.isIrreducible_contragredient_iff (compactOpen_cofinal F T (B.size i))
        (A i).property.2.1).mpr (A i).property.1,
      isSupercuspidal_smoothContragredient F T (B.size i) (A i).obj
        (A i).obj.representation (A i).property.2⟩
  obtain ⟨Q, D, hQ, hD, hQD⟩ :=
    TemperedLFactorStatement.blockShape F ψ ν temperedLFactor B B
      (fun i => (A i).obj.representation) (fun j => (Ad j).obj.representation)
      (fun i => (A i).property.1)
      (fun i => unitarizableSupercuspidal_isSquareIntegrable F (B.positive i) (A i) (hU i))
      (fun j => (Ad j).property.1) (fun j =>
        unitarizableSupercuspidal_isSquareIntegrable F (B.positive j) (Ad j)
          (isUnitarizable_smoothContragredient F (A j).obj (A j).property.2.1 (hU j)))
  let ed := (smoothContragredientEquiv e).symm.trans
    (T.normalizedProductSmoothDualEquiv B (fun i => (A i).obj.representation)
      (fun i => (A i).property.2.1))
  have hPQ := ((IsPadicSymmetricLPolynomial.congr_equiv e ed).mp hP).unique hQ
  have hdiag (i : Fin B.length) : lPolynomialPoleOrderAtZero (D i i) = 1 :=
    poleOrder_selfPair_supercuspidal F ψ ν (B.positive i) (A i) (hD i i)
  rw [hPQ, hQD, lPolynomialPoleOrderAtZero_prod_prod D (fun i j => (hD i j).coeff_zero)]
  calc
    B.length = ∑ i : Fin B.length, lPolynomialPoleOrderAtZero (D i i) := by simp [hdiag]
    _ ≤ ∑ i, ∑ j, lPolynomialPoleOrderAtZero (D i j) :=
      Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (fun j _ => Nat.zero_le (lPolynomialPoleOrderAtZero (D i j)))
          (Finset.mem_univ i)

end Local

/-- A generic unitarizable action is supercuspidal if its self-pair gamma has
positive real order only at zero and the self-pair L-factor has a simple pole there. -/
def SupercuspidalOfSelfPairStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (r : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (r + 1) F.Carrier)),
      IsGeneric ψ r π.representation → IsUnitarizable π.representation →
      ∀ (G : RatFunc ℂ) (P : ℂ[X]),
        IsPadicSymmetricGammaFactor F ψ ν.val
          π.representation (smoothContragredient π.representation) G →
        IsPadicSymmetricLPolynomial F ψ ν.val
          π.representation (smoothContragredient π.representation) P →
        (∀ t : ℝ, 0 < meromorphicOrderAt
          (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
          t = 0) →
        lPolynomialPoleOrderAtZero P = 1 →
        GeneralLinear.IsSupercuspidal π.representation

set_option maxHeartbeats 800000 in
theorem supercuspidalOfSelfPair : SupercuspidalOfSelfPairStatement.{uF, uV} := by
  intro p _ F ψ ν r
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (r + 1)
  intro π hπ hU G P hG hP hzero hord
  obtain ⟨B, hB⟩ := unitarySupercuspidalProduct_of_generic_smoothDualGamma.{uF, uV, uV}
    F (unitaryGenericExhaustion F T)
    (segmentHeadLFactor_of_squareIntegrable squareIntegrableLFactor squareIntegrableLFactor)
    supercuspidalEqualRankLFactor ψ ν π hπ hU hG hzero
  have hle := blockLength_le_selfPairPoleOrder_of_unitarySupercuspidalProduct F ψ ν B hB hP
  rw [hord] at hle
  have hpos : 0 < B.length := by
    by_contra! h
    have heq : B.length = 0 := by omega
    simpa [heq] using B.sum_eq
  have hlen : B.length = 1 := by omega
  let i := B.singleBlockIndex hlen
  obtain ⟨A, _, ⟨e⟩⟩ := hB
  let e' := T.singleBlockNormalizedProductEquiv B hlen
    (fun j => (A j).obj.representation) (fun j => (A j).obj.isSmooth) i
  have hTransport {n : ℕ} (h : n = r + 1)
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
      (hsc : GeneralLinear.IsSupercuspidal ρ) :
      GeneralLinear.IsSupercuspidal (ρ.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom) := by
    subst n
    rw [GeneralLinear.reindex_finCongr_rfl]
    change GeneralLinear.IsSupercuspidal (ρ.comp (MonoidHom.id _))
    simpa only [MonoidHom.comp_id] using hsc
  exact (GeneralLinear.isSupercuspidal_iff_of_equiv (e.trans e')).mpr
    (hTransport (B.singleBlock_size hlen i) (A i).obj.representation (A i).property.2)

end Langlands.RankinSelberg
