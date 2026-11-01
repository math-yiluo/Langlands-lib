import Langlands.Representation.Classification.TwoSupercuspidalAdjacentJacquetProof
import Langlands.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof
import Langlands.Representation.Derivative.PartialDerivativeTensorProof
import Langlands.Representation.Jacquet.LocalizationTransport

/-! Middle derivatives of supplied proper adjacent-product subspaces. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification

open GeneralLinear

universe uF uV uG uW uZ

namespace TwoSupercuspidalPartialDerivatives

/-- Tensoring with a one-dimensional vector space with trivial group action
does not change the representation, up to equivalence. -/
theorem nonempty_firstFactor_equiv
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (hW : Module.finrank ℂ W = 1) :
    Nonempty ((BinaryTensor.firstFactor ρ W).Equiv ρ) := by
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hW
  let f : (V ⊗[ℂ] W) ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e.symm).trans (TensorProduct.rid ℂ V)
  refine ⟨Representation.Equiv.mk f fun g => ?_⟩
  apply TensorProduct.ext'
  intro v w
  change f (ρ g v ⊗ₜ w) = ρ g (f (v ⊗ₜ w))
  simp [f]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Rank transport does not change the dimension of the actual carrier. -/
theorem finrank_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      Module.finrank ℂ ((Derivative.generalLinearRankCast T h).obj X) =
        Module.finrank ℂ X := by
  subst h
  intros
  rfl

/-- The published top-derivative dimension formula, including its rank cast,
for an arbitrary positive supercuspidal rank. -/
theorem finrank_topDerivative (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {m : ℕ} (hm : 0 < m) :
    letI := T.topology
    ∀ B : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := m),
      Module.finrank ℂ ((Derivative.topDerivative T ψ m).obj B.obj) = 1 := by
  let := T.topology
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  intro B
  change Module.finrank ℂ ((Derivative.generalLinearRankCast T (Nat.sub_self (n + 1))).obj
    ((Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj B.obj)) = 1
  rw [finrank_rankCast]
  exact SupercuspidalDerivativesProof.finrank_generalLinearDerivative_top T ψ n B.obj
    B.property.1 B.property.2

/-- The finite ordered two-block tensor, transported from its Levi to the
ordinary product group, is the binary exterior tensor. -/
theorem nonempty_twoBlockTensor_equiv (T : F.TopologicalData)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      Nonempty
        (((Derivative.Mirabolic.continuousPullbackFunctor
            (Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm.toMonoidHom
            (Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm.continuous).obj
          (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb A B))).representation.Equiv
        ((Derivative.exteriorTensor T a b).obj (A, B)).representation) := by
  let := T.topology
  intro A B
  refine ⟨Representation.Equiv.mk
    (Shahidi.pairSplit (fun i => (twoBlockFactors ha hb A B i : Type uV))) ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  exact Shahidi.pairSplit_external
    (fun i => (twoBlockFactors ha hb A B i).representation)
    ((Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm g) x

/-- Partial derivatives preserve actual equivalences between carriers in
independent universes. -/
theorem nonempty_partialDerivative_equiv (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uZ} ℂ
        (GeneralLinear a F.Carrier × GeneralLinear b F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear a F.Carrier × GeneralLinear b F.Carrier)),
      Nonempty (A.representation.Equiv B.representation) →
      Nonempty (((Derivative.partialDerivative T ψ a b).obj A).representation.Equiv
        ((Derivative.partialDerivative T ψ a b).obj B).representation) := by
  let := T.topology
  intro A B ⟨e⟩
  let f := Jacquet.Localization.representationEquiv
    (Derivative.Partial.unipotent F.Carrier a b)
    (Derivative.Partial.character ψ.complex a b) e
  refine ⟨Representation.Equiv.mk f fun g => ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := Derivative.Partial.mk_surjective ψ.complex a b A.representation q
  change f (Derivative.Partial.mk ψ.complex a b A.representation
      (A.representation (g, 1) v)) =
    Derivative.Partial.action ψ.complex a b B.representation g
      (f (Derivative.Partial.mk ψ.complex a b A.representation v))
  simp only [f, Jacquet.Localization.representationEquiv_mk,
    Derivative.Partial.action_mk]
  exact congrArg (Derivative.Partial.mk ψ.complex a b B.representation)
    (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (g, 1) v)

/-- A supplied ordered two-block Jacquet equivalence with a supercuspidal
second factor determines the derivative at that factor's rank. -/
theorem derivative_of_twoBlockJacquet (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (Z : SmoothRep.{0, uF, uZ} ℂ (GeneralLinear (a + b) F.Carrier))
      (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (B : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := b)),
      Nonempty
        (((T.normalizedJacquetFunctor (Shahidi.twoBlocks a b ha hb)).obj Z).representation.Equiv
          (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb A B.obj)).representation) →
      Nonempty
        (((Derivative.generalLinearDerivative T ψ (a + b) b (Nat.le_add_left b a) ⋙
          Derivative.generalLinearRankCast T (Nat.add_sub_cancel a b)).obj Z).representation.Equiv
          A.representation) := by
  let := T.topology
  intro Z A B ⟨eJ⟩
  obtain ⟨eT⟩ := nonempty_twoBlockTensor_equiv T ha hb A B.obj
  let eP :
      ((Derivative.positiveTwoBlockNormalizedJacquet T a b ha hb).obj Z).representation.Equiv
        ((Derivative.Mirabolic.continuousPullbackFunctor (R := ℂ)
            (Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm.toMonoidHom
            (Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm.continuous).obj
          (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb A B.obj))).representation :=
    Representation.Equiv.mk eJ.toLinearEquiv
      (fun g => eJ.isIntertwining'
        ((Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm g))
  obtain ⟨eD⟩ := nonempty_partialDerivative_equiv T ψ a b _ _ ⟨eP.trans eT⟩
  obtain ⟨cJ⟩ := Derivative.partialDerivativeJacquetComparison F T ψ a b ha hb
  obtain ⟨cT⟩ := Derivative.partialDerivativeTensor F T ψ a b
  obtain ⟨eF⟩ := nonempty_firstFactor_equiv A.representation
    ((Derivative.topDerivative T ψ b).obj B.obj) (finrank_topDerivative T ψ hb B)
  exact ⟨((SmoothRep.equivOfIso (cJ.app Z)).trans eD).trans
    ((SmoothRep.equivOfIso (cT.app (A, B.obj))).trans eF)⟩

end TwoSupercuspidalPartialDerivatives

variable {p : ℕ} [Fact p.Prime]

/-- Middle derivatives of any supplied nonzero proper adjacent-product
subspace and its quotient. The existence of that subspace is not asserted. -/
def TwoSupercuspidalAdjacentProductMiddleDerivatives
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k : ℕ) (hk : 0 < k)
    (ρ ρ' : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)),
    (ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass ∨
      ρ.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ'.isoClass) →
    let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
      (twoBlockFactors hk hk ρ.obj ρ'.obj)
    let D := Derivative.generalLinearDerivative T ψ (k + k) k (Nat.le_add_left k k) ⋙
      Derivative.generalLinearRankCast T (Nat.add_sub_cancel k k)
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      Nonempty ((D.obj (SmoothRep.subrepresentation P S)).representation.Equiv
        ρ.obj.representation) ∧
      Nonempty ((D.obj (SmoothRep.quotient P S)).representation.Equiv
        ρ'.obj.representation)

set_option maxHeartbeats 800000 in
/-- The actual ordered Jacquet calculation and the two partial-derivative
comparisons prove both middle-derivative formulas. -/
theorem twoSupercuspidalAdjacentProductMiddleDerivatives
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSupercuspidalAdjacentProductMiddleDerivatives.{uF, uV} F T := by
  let := T.topology
  intro ψ k hk ρ ρ' h P D S hS₀ hS₁
  obtain ⟨eS, eQ⟩ :=
    twoSupercuspidalAdjacentProductJacquet F T k hk ρ ρ' h S hS₀ hS₁
  constructor
  · exact TwoSupercuspidalPartialDerivatives.derivative_of_twoBlockJacquet
      T ψ hk hk (SmoothRep.subrepresentation P S) ρ.obj ρ' eS
  · exact TwoSupercuspidalPartialDerivatives.derivative_of_twoBlockJacquet
      T ψ hk hk (SmoothRep.quotient P S) ρ'.obj ρ eQ

end Langlands.Classification
