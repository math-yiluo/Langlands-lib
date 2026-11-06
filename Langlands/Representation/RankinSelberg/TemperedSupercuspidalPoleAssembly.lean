import Langlands.Representation.RankinSelberg.SquareIntegrablePairPoleOrder
import Langlands.Representation.RankinSelberg.GroupedLFactorProduct
import Langlands.Representation.RankinSelberg.SingleBlockFactors

/-!
# Assembling a supercuspidal pole from a square-integrable block

These are internal consequences of the existing JPSS proposition targets.
The analytic formulas remain explicit premises throughout.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW uV₂

variable {p : ℕ} [Fact p.Prime]

namespace TemperedSupercuspidalPoleAssembly

/-- A pole at zero represented by a full arbitrary-rank L-polynomial
certificate and a root at one. -/
def HasPadicRankPoleAtZero (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n t : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (GeneralLinear t F.Carrier) W) : Prop :=
  ∃ P : ℂ[X], IsPadicRankLPolynomial F ψ ν.val π σ P ∧ P.IsRoot 1

section EqualRank

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W}

/-- Under (8.1)(ii), contragredience forces a root at one in any certified
equal-rank L-polynomial. The compatible-measure certificate is retained. -/
theorem isRoot_one_of_contragredient
    (H : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    (hiπ : Representation.IsIrreducible π)
    (hsπ : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π)
    (hiσ : Representation.IsIrreducible σ)
    (hwσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) σ)
    (he : letI := F.canonicalTopologicalData.topology;
      haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
      Nonempty (π.Equiv (smoothContragredient σ)))
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν.val π σ P) :
    P.IsRoot 1 := by
  classical
  obtain ⟨A, hA, hPA⟩ := H p F ψ ν r π σ hiπ hsπ hiσ hwσ
  have h1 : (1 : ℂ) ∈ A := (one_mem_iff_of_supercuspidalTwistSet hA).mpr he
  rw [hP.unique hPA]
  exact (isRoot_prod A (fun a => 1 - C a * X) 1).mpr ⟨1, h1, by simp [IsRoot]⟩

/-- The formula (8.1)(ii) supplies both the certificate and its root for an
equal-rank contragredient pair. -/
theorem exists_isRoot_one_of_contragredient
    (H : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    (hiπ : Representation.IsIrreducible π)
    (hsπ : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π)
    (hiσ : Representation.IsIrreducible σ)
    (hwσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) σ)
    (he : letI := F.canonicalTopologicalData.topology;
      haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
      Nonempty (π.Equiv (smoothContragredient σ))) :
    ∃ P : ℂ[X], IsPadicPairLPolynomial F ψ ν.val π σ P ∧ P.IsRoot 1 := by
  obtain ⟨A, -, hP⟩ := H p F ψ ν r π σ hiπ hsπ hiσ hwσ
  exact ⟨_, hP, isRoot_one_of_contragredient ν H hiπ hsπ hiσ hwσ he hP⟩

end EqualRank

section SingleComponent

variable {F : PadicField.{uF} p}

/-- An irreducible representation equivalent to an induction is an
irreducible component of that induction, using its whole subrepresentation. -/
theorem isIrreducibleComponent_of_equiv
    {G : Type*} [Group G]
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ξ : Representation ℂ G X} {π : Representation ℂ G V}
    (e : ξ.Equiv π) (hiπ : Representation.IsIrreducible π) :
    IsIrreducibleComponent ξ π := by
  let f : (⊤ : Subrepresentation ξ).toRepresentation.IntertwiningMap π :=
    { toLinearMap := e.toLinearMap.comp (⊤ : Subrepresentation ξ).toSubmodule.subtype
      isIntertwining' := fun g => by
        ext v
        exact DFunLike.congr_fun (e.isIntertwining' g) (v : X) }
  refine ⟨hiπ, ⊤, f, ?_⟩
  intro v
  exact ⟨⟨e.symm v, trivial⟩, e.apply_symm_apply v⟩

/-- The length-one centered segment has its seed as an irreducible
component, by the published one-block evaluation equivalence. -/
theorem centeredSegment_zero_component
    {a : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear (a + 1) F.Carrier) W)
    (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ)
    (hiσ : Representation.IsIrreducible σ) :
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced
        (succBlockShape (fun _ : Fin 1 => a) (show ∑ _ : Fin 1, (a + 1) = a + 1 by simp))
        (centeredSegmentBlocks F 0 σ)) σ := by
  have hz : centeredSegmentBlocks F 0 σ = fun _ : Fin 1 => σ := by
    funext i
    have hi : (i : ℕ) = 0 := by omega
    simp only [centeredSegmentBlocks, Nat.cast_zero, hi, zero_div, sub_zero,
      realPowerTwist_zero]
  rw [hz]
  exact isIrreducibleComponent_of_equiv
    (succSingleBlockNormalizedProductEquiv F (fun _ => a) (fun _ => σ) (fun _ => hσ)) hiσ

end SingleComponent

section SquareIntegrable

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V : Type uV₂} [AddCommGroup V] [Module ℂ V]

/-- In (8.2), a length-one partner leaves one supercuspidal factor.
Contragredience with the top centered block makes that factor vanish at one.
No unitary or classification assertion is inferred for the supplied partner. -/
theorem exists_squareIntegrable_isRoot_one
    (H82 : SquareIntegrableLFactorStatement.{uF, uV, uW, uV₂, uW})
    (H81 : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    {a m r : ℕ} (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    {π₀ : Representation ℂ (GeneralLinear (a + 1) F.Carrier) V₀}
    {σ : Representation ℂ (GeneralLinear (a + 1) F.Carrier) W}
    {π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V}
    (hiπ₀ : Representation.IsIrreducible π₀)
    (hsπ₀ : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π₀)
    (hiσ : Representation.IsIrreducible σ)
    (hsσ : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal σ)
    (hπ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable π)
    (hcπ : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π)
    (hσ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ)
    (hwσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) σ)
    (he : letI := F.canonicalTopologicalData.topology;
      haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (a + 1)
      Nonempty ((centeredSegmentBlocks F m π₀ 0).Equiv (smoothContragredient σ))) :
    ∃ P : ℂ[X], IsPadicPairLPolynomial F ψ ν.val π σ P ∧ P.IsRoot 1 := by
  have ht : ∑ _j : Fin (0 + 1), (a + 1) = a + 1 := by simp
  have har : a ≤ r := (le_iff_of_centeredSegment_rank hr ht).mpr (Nat.zero_le m)
  obtain ⟨P, Q, hP, hQ, hprod⟩ :=
    H82 p F ψ ν a m r a 0 a hr ht π₀ σ π σ hiπ₀ hsπ₀ hiσ hsσ hπ hcπ hσ
      (centeredSegment_zero_component σ hsσ.1.1 hiσ) har
  have hQ0 : IsPadicPairLPolynomial F ψ ν.val (centeredSegmentBlocks F m π₀ 0) σ (Q 0) := by
    simpa only [centeredSegmentBlocks, Nat.cast_zero, Fin.val_zero, zero_div, sub_zero,
      realPowerTwist_zero] using (isPadicSymmetricLPolynomial_of_le le_rfl).mp (hQ 0)
  have hroot := isRoot_one_of_contragredient ν H81
    (isIrreducible_centeredSegmentBlocks m hiπ₀ 0)
    (isSupercuspidal_centeredSegmentBlocks m hsπ₀ 0) hiσ hwσ he hQ0
  refine ⟨P, hP, ?_⟩
  rw [hprod]
  exact (isRoot_prod Finset.univ Q 1).mpr ⟨0, Finset.mem_univ 0, hroot⟩

end SquareIntegrable

section Product

variable (F : PadicField.{uF} p)

local instance canonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- A certified root in one twisted block pair persists in the full
induction against a twisted square-integrable seed, by (8.4). -/
theorem exists_induced_isRoot_one
    (H84 : TemperedLFactorStatement.{uF, uV, uW})
    {n a : ℕ} (hn : 0 < n) (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hiπ : ∀ i, Representation.IsIrreducible (π i))
    (hsπ : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable (π i))
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear (a + 1) F.Carrier) W)
    (hiσ : Representation.IsIrreducible σ)
    (hsmσ : IsSmooth σ)
    (hsσ : F.canonicalTopologicalData.IsSquareIntegrable σ)
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {τ : Representation ℂ (GeneralLinear n F.Carrier) V₂}
    (e : (F.canonicalNormalizedProductInduced B π).Equiv τ)
    (s z : ℝ) (i : Fin B.length)
    {R : ℂ[X]}
    (hR : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (B.size i)) s (π i))
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) z σ) R)
    (hroot : R.IsRoot 1) :
    HasPadicRankPoleAtZero F ψ ν
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) s τ)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) z σ) := by
  classical
  let C := succBlockShape (fun _ : Fin 1 => a)
    (show ∑ _ : Fin 1, (a + 1) = a + 1 by simp)
  let b := succSingleBlockNormalizedProductEquiv F (fun _ : Fin 1 => a)
    (fun _ => σ) (fun _ => hsmσ)
  obtain ⟨P, Q, hP, hQ, hprod⟩ :=
    H84.commonRealTwistsOfEquiv F ψ ν hn (Nat.succ_pos a) B C π (fun _ => σ)
      hiπ hsπ (fun _ => hiσ) (fun _ => hsσ) e b s z
  have hQi : (Q i 0).IsRoot 1 := by
    rw [(hQ i 0).unique hR]
    exact hroot
  refine ⟨P, hP, ?_⟩
  rw [hprod]
  refine (isRoot_prod Finset.univ (fun j => ∏ k, Q j k) 1).mpr
    ⟨i, Finset.mem_univ i, ?_⟩
  exact (isRoot_prod Finset.univ (Q i) 1).mpr ⟨0, Finset.mem_univ 0, hQi⟩

end Product

end TemperedSupercuspidalPoleAssembly

end Langlands.RankinSelberg
