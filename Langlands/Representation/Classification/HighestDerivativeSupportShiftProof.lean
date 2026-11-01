import Langlands.Representation.Classification.SegmentSocleDerivativesStatement
import Langlands.Representation.Classification.HighestDerivativeSupportShiftBoundary
import Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Classification.SupercuspidalContragredient
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.Classification.TwistedProductOrdinaryDualProof
import Langlands.Representation.Classification.TwistedProductCharacterTwistProof
import Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof
import Langlands.Representation.Smooth.Contragredient.ExactProof

/-! # The positive support shift of an irreducible highest derivative (BZ77 4.7(b)) -/

noncomputable section

namespace Langlands.Classification.HighestDerivativeSupportShiftProof

open CategoryTheory GeneralLinear

universe uF uV

section Bridge

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem restriction_rankCast {a b : ℕ} (h1 : a + 1 = b + 1) (h2 : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (a + 1) F.Carrier),
      (Derivative.generalLinearRestriction T b).obj
          ((Derivative.generalLinearRankCast T h1).obj X) =
        (Derivative.mirabolicRankCast T h2).obj
          ((Derivative.generalLinearRestriction T a).obj X) := by
  subst h2
  intro X
  rfl

/-- At positive order, the `GL` derivative is the mirabolic derivative of the
restriction to `P_(N+1)`. -/
theorem generalLinearDerivative_obj_eq
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N j : ℕ) (hj : j ≤ N + 1) (hj0 : 0 < j) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      (Derivative.generalLinearDerivative T ψ (N + 1) j hj).obj X =
        (Derivative.mirabolicDerivativeOfOrder T ψ N j ⟨hj0, hj⟩).obj
          ((Derivative.generalLinearRestriction T N).obj X) := by
  let := T.topology
  intro X
  cases j with
  | zero => exact absurd hj0 (lt_irrefl 0)
  | succ j =>
    show (Derivative.mirabolicDerivative T ψ (N + 1 - (j + 1)) j).obj
        ((Derivative.generalLinearRestriction T (N + 1 - (j + 1) + j)).obj
          ((Derivative.generalLinearRankCast T (Derivative.rank_eq_of_succ_le hj)).obj X)) =
      (Derivative.mirabolicDerivative T ψ (N + 1 - (j + 1)) j).obj
        ((Derivative.mirabolicRankCast T (show N = N + 1 - (j + 1) + j by omega)).obj
          ((Derivative.generalLinearRestriction T N).obj X))
    rw [restriction_rankCast T (Derivative.rank_eq_of_succ_le hj)
      (show N = N + 1 - (j + 1) + j by omega)]

end Bridge

section Contragredient

variable {R G V W : Type*} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- An equivalence of representations induces the reverse equivalence of smooth
contragredients. -/
def smoothContragredientEquiv (e : ρ.Equiv σ) :
    (smoothContragredient σ).Equiv (smoothContragredient ρ) :=
  (contragredientMap e.toIntertwiningMap).ofBijective
    ⟨fun ℓ ℓ' h => by
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
      exact congrArg (fun m : SmoothDual ρ => m.val v) h,
    fun ℓ => ⟨contragredientMap e.symm.toIntertwiningMap ℓ, by
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      exact congrArg ℓ.val (e.symm_apply_apply v)⟩⟩

end Contragredient

section Data

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The contragredient `ρ̃` of a cuspidal datum. -/
def dualDatum (ρ : T.CuspidalDatum.{uV, uF}) : T.CuspidalDatum.{uV, uF} where
  rank := ρ.rank
  rank_pos := ρ.rank_pos
  cls := T.supercuspidalClassContragredient GeneralLinear.supercuspidalContragredient.{uF, uV}
    ρ.rank ρ.cls

theorem dualDatum_dualDatum (ρ : T.CuspidalDatum.{uV, uF}) : dualDatum (dualDatum ρ) = ρ := by
  obtain ⟨r, hr, a⟩ := ρ
  exact congrArg (PadicField.TopologicalData.CuspidalDatum.mk r hr)
    (T.supercuspidalClassContragredient_involutive _ r a)

theorem classContragredient_twist (r : ℕ) (s : ℝ)
    (a : letI := T.topology
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := r)) :
    T.supercuspidalClassContragredient GeneralLinear.supercuspidalContragredient.{uF, uV} r
        (T.supercuspidalClassRealPowerTwist r s a) =
      T.supercuspidalClassRealPowerTwist r (-s)
        (T.supercuspidalClassContragredient GeneralLinear.supercuspidalContragredient.{uF, uV}
          r a) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup r
  unfold PadicField.TopologicalData.supercuspidalClassContragredient
    PadicField.TopologicalData.supercuspidalClassRealPowerTwist
  rw [GeneralLinear.SupercuspidalClass.contragredient_twist]
  apply GeneralLinear.SupercuspidalClass.twist_congr
  exact (realPowerCharacter_neg _ s).symm

theorem dualDatum_twist (s : ℝ) (ρ : T.CuspidalDatum.{uV, uF}) :
    dualDatum (ρ.twist s) = (dualDatum ρ).twist (-s) := by
  obtain ⟨r, hr, a⟩ := ρ
  exact congrArg (PadicField.TopologicalData.CuspidalDatum.mk r hr)
    (classContragredient_twist r s a)

/-- The class of `ν^t ρ̃`. It is irreducible so that unification never unfolds the
class-level twist and contragredient. -/
@[irreducible]
def twistedDualClass (t : ℝ) (ρ : T.CuspidalDatum.{uV, uF}) :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := ρ.rank) :=
  ((dualDatum ρ).twist t).cls

/-- `ν^t ρ̃` for every member of a family of cuspidal data. -/
def twistedDualData (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF}) :
    Fin r → T.CuspidalDatum.{uV, uF} :=
  fun i => ⟨(ρ i).rank, (ρ i).rank_pos, twistedDualClass t (ρ i)⟩

theorem twistedDualData_apply (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (i : Fin r) : twistedDualData t ρ i = (dualDatum (ρ i)).twist t := by
  unfold twistedDualData twistedDualClass
  rfl

/-- The representatives `ν^t Ã_i` of `ν^t ρ̃_i`. -/
def twistedDualRep (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier)
      (n := (twistedDualData t ρ i).rank) :=
  letI := T.topology
  fun i =>
    letI := T.generalLinearTopologicalGroup (ρ i).rank
    letI := T.generalLinearTopologicalGroup (twistedDualData t ρ i).rank
    SupercuspidalRep.twist (T.determinantPowerCharacter (ρ i).rank t)
      (T.isOpen_ker_determinantPowerCharacter _ t)
      (T.ker_determinant_le_ker_determinantPowerCharacter _ t)
      (SupercuspidalRep.contragredient (GeneralLinear.compactOpen_cofinal F T (ρ i).rank)
        (T.supercuspidalContragredientClosed GeneralLinear.supercuspidalContragredient.{uF, uV}
          (ρ i).rank) (A i))

theorem twistedDualRep_represents (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i)) (i : Fin r) :
    (twistedDualData t ρ i).IsRepresentedBy (twistedDualRep t ρ A i) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (ρ i).rank
  change (twistedDualRep t ρ A i).isoClass = twistedDualClass t (ρ i)
  unfold twistedDualClass
  exact congrArg (SupercuspidalClass.twist _ _ _)
    (congrArg (SupercuspidalClass.contragredient _ _) (hA i))

end Data

section ProductDual

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

theorem segmentFactor_zero {r : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    (T.segmentFactor X 0).representation = X.representation := by
  let := T.topology
  show twist (realPowerCharacter (T.determinantNorm r) 0) X.representation = _
  rw [realPowerCharacter_zero, twist_one]

/-- The character `ν^t = |·|^t` of `F^×`. -/
def unitsPowerCharacter (t : ℝ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ F.Carrierˣ :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ⟨realPowerCharacter T.normalizedAbsUnits t,
    isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits t⟩

theorem unitsPowerCharacter_comp (n : ℕ) (t : ℝ) :
    letI := T.topology
    (unitsPowerCharacter F T t).toMonoidHom.comp
        (determinant : GeneralLinear n F.Carrier →* F.Carrierˣ) =
      T.determinantPowerCharacter n t := by
  let := T.topology
  show (realPowerCharacter T.normalizedAbsUnits t).comp determinant =
    realPowerCharacter (T.normalizedAbsUnits.comp determinant) t
  unfold realPowerCharacter
  exact MonoidHom.comp_assoc _ _ _

/-- The smooth duals `Ã_i`, as blocks of the shape of `A_1 × ⋯ × A_r`. -/
def dualBlocks {n r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((T.cuspidalShape ρ h).size i) F.Carrier) :=
  letI := T.topology
  fun i =>
    letI := T.generalLinearTopologicalGroup (ρ i).rank
    SmoothRep.of (smoothContragredient (A i).obj.representation)
      (isSmooth_smoothContragredient (A i).obj.representation)

/-- The blocks `ν^t Ã_i`, as blocks of the shape of `A_1 × ⋯ × A_r`. -/
def twistedDualBlocks (t : ℝ) {n r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((T.cuspidalShape ρ h).size i) F.Carrier) :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  fun i => (dualBlocks F T ρ h A i).twist
    ((unitsPowerCharacter F T t).toMonoidHom.comp determinant)
    ((unitsPowerCharacter F T t).isOpen_ker.preimage
      (T.generalLinearDeterminant ((T.cuspidalShape ρ h).size i)).continuous)

/-- `A_1 × ⋯ × A_r ≃ i(ν^0 A_1, …, ν^0 A_r)`. -/
def productZeroEquiv {n r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.cuspidalProductInduced ρ h A).representation.Equiv
      (T.twistedProductInduced (T.cuspidalShape ρ h) (fun i => (A i).obj)
        (fun _ => 0)).representation :=
  letI := T.topology
  T.normalizedProductInducedEquiv (T.cuspidalShape ρ h)
    (σ := fun i => (A i).obj.representation)
    (τ := fun i => (T.segmentFactor (A i).obj 0).representation)
    fun i => equivOfRepresentationEq (segmentFactor_zero F T (A i).obj).symm

/-- The smooth dual of `i(ν^0 A_1, …, ν^0 A_r)` is `i(ν^0 Ã_1, …, ν^0 Ã_r)`. -/
def ordinaryDualEquiv {n r : ℕ} (hn : 0 < n) (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (smoothContragredient (T.twistedProductInduced (T.cuspidalShape ρ h) (fun i => (A i).obj)
        (fun _ => 0)).representation).Equiv
      (T.twistedProductInduced (T.cuspidalShape ρ h) (dualBlocks F T ρ h A)
        (fun _ => -0)).representation :=
  letI := T.topology
  (twistedProductOrdinaryDual.{uF, uV} F T n hn (T.cuspidalShape ρ h) (fun i => (A i).obj)
    (fun _ => 0) (fun i => (A i).property.2.1)).some

/-- Twisting `i(ν^0 Ã_1, …, ν^0 Ã_r)` by `ν^t ∘ det` twists every block. -/
def characterTwistEquiv {n r : ℕ} (hn : 0 < n) (t : ℝ) (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (twist ((unitsPowerCharacter F T t).toMonoidHom.comp determinant)
      (T.twistedProductInduced (T.cuspidalShape ρ h) (dualBlocks F T ρ h A)
        (fun _ => -0)).representation).Equiv
      (T.twistedProductInduced (T.cuspidalShape ρ h) (twistedDualBlocks F T t ρ h A)
        (fun _ => -0)).representation :=
  letI := T.topology
  (twistedProductCharacterTwist.{uF, uV} F T n hn (T.cuspidalShape ρ h)
    (unitsPowerCharacter F T t) (dualBlocks F T ρ h A) (fun _ => -0)).some

theorem twistedDualBlocks_representation (t : ℝ) {n r : ℕ}
    (ρ : Fin r → T.CuspidalDatum.{uV, uF}) (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (i : Fin r) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (ρ i).rank
    (twistedDualBlocks F T t ρ h A i).representation =
      twist ((unitsPowerCharacter F T t).toMonoidHom.comp determinant)
        (smoothContragredient (A i).obj.representation) :=
  rfl

theorem twistedDualRep_representation (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (i : Fin r) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (ρ i).rank
    (twistedDualRep t ρ A i).obj.representation =
      twist (T.determinantPowerCharacter (ρ i).rank t)
        (smoothContragredient (A i).obj.representation) :=
  rfl

theorem segmentFactor_neg_zero {m : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)) :
    letI := T.topology
    (T.segmentFactor X (-0)).representation = X.representation := by
  rw [neg_zero]
  exact segmentFactor_zero F T X

theorem twistedDualBlocks_eq (t : ℝ) {n r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (i : Fin r) :
    letI := T.topology
    (twistedDualBlocks F T t ρ h A i).representation =
      (twistedDualRep t ρ A i).obj.representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (ρ i).rank
  (twistedDualBlocks_representation F T t ρ h A i).trans
    ((congrArg (fun χ => twist χ (smoothContragredient (A i).obj.representation))
      (unitsPowerCharacter_comp F T _ t)).trans
        (twistedDualRep_representation F T t ρ A i).symm)

/-- The identification `ν^(-0) X = X`, for an abstract block `X`. -/
def segmentFactorNegZeroEquiv {m : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)) :
    letI := T.topology
    (T.segmentFactor X (-0)).representation.Equiv X.representation :=
  equivOfRepresentationEq (segmentFactor_neg_zero F T X)

/-- `ν^(-0) (ν^t Ã_i) ≃ ν^t Ã_i`, the latter as the published representative. -/
def twistedDualBlockEquiv (t : ℝ) {n r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (i : Fin r) :
    letI := T.topology
    (T.segmentFactor (twistedDualBlocks F T t ρ h A i) (-0)).representation.Equiv
      (twistedDualRep t ρ A i).obj.representation :=
  (segmentFactorNegZeroEquiv F T _).trans
    (equivOfRepresentationEq (twistedDualBlocks_eq F T t ρ h A i))

theorem twistedDualData_sum (t : ℝ) {n r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n) : ∑ i, (twistedDualData t ρ i).rank = n :=
  h

/-- Block equivalences `ν^(s_i) X_i ≃ Y_i` give `i(ν^(s_1) X_1, …) ≃ i(Y_1, …)`, for abstract
blocks (so the kernel never unfolds concrete blocks). -/
def twistedProductBlocksEquiv {n : ℕ} (B : GeneralLinear.BlockShape n)
    (X Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ)
    (e : letI := T.topology
      ∀ i, (T.segmentFactor (X i) (s i)).representation.Equiv (Y i).representation) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.twistedProductInduced B X s).representation.Equiv
      ((T.normalizedProductInductionFunctor B).obj Y).representation :=
  letI := T.topology
  T.normalizedProductInducedEquiv B e

/-- `ν^t Ã_1 × ⋯ × ν^t Ã_r` is the product induced along the shape of `A_1 × ⋯ × A_r`.
Stated as an isomorphism of objects so that no carrier types have to be unified. -/
def twistedDualShapeIso (t : ℝ) {n r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    T.cuspidalProductInduced (twistedDualData t ρ) (twistedDualData_sum F T t ρ h)
        (twistedDualRep t ρ A) ≅
      (T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).obj
        (fun i => (twistedDualRep t ρ A i).obj) :=
  Iso.refl _

/-- `i(ν^(-0) (ν^t Ã_1), …) ≃ ν^t Ã_1 × ⋯ × ν^t Ã_r`. -/
def twistedDualProductEquiv {n r : ℕ} (t : ℝ) (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.twistedProductInduced (T.cuspidalShape ρ h) (twistedDualBlocks F T t ρ h A)
        (fun _ => -0)).representation.Equiv
      (T.cuspidalProductInduced (twistedDualData t ρ) (twistedDualData_sum F T t ρ h)
        (twistedDualRep t ρ A)).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  (twistedProductBlocksEquiv F T (T.cuspidalShape ρ h) (twistedDualBlocks F T t ρ h A)
    (fun i => (twistedDualRep t ρ A i).obj) (fun _ => -0) (twistedDualBlockEquiv F T t ρ h A)).trans
    (SmoothRep.equivOfIso (twistedDualShapeIso F T t ρ h A)).symm

/-- For `Π = A_1 × ⋯ × A_r` of positive rank, `ν^t Ã_1 × ⋯ × ν^t Ã_r` is equivalent to
`ν^t Π̃`. -/
def twistedDualEquiv {n r : ℕ} (hn : 0 < n) (t : ℝ) (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.cuspidalProductInduced (twistedDualData t ρ) (twistedDualData_sum F T t ρ h)
        (twistedDualRep t ρ A)).representation.Equiv
      (twist (T.determinantPowerCharacter n t)
        (smoothContragredient (T.cuspidalProductInduced ρ h A).representation)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  (twistedDualProductEquiv F T t ρ h A).symm.trans
    ((characterTwistEquiv F T hn t ρ h A).symm.trans
      ((twistEquiv _ ((ordinaryDualEquiv F T hn ρ h A).symm.trans
        (smoothContragredientEquiv (productZeroEquiv F T ρ h A)))).trans
        (equivOfRepresentationEq (congrArg
          (fun χ => twist χ (smoothContragredient (T.cuspidalProductInduced ρ h A).representation))
          (unitsPowerCharacter_comp F T n t)))))


end ProductDual

section Quotient

variable {G : Type*} [Group G]
  {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
  {ρ : Representation ℂ G V} {π : Representation ℂ G W} {σ : Representation ℂ G U}

/-- The functional `u ↦ γ (j u) w` on `σ`. -/
def pairingFunctional (γ : InvariantBilinear.forms ρ π (fun _ => (1 : ℂ)))
    (j : σ.IntertwiningMap ρ) (w : W) : Module.Dual ℂ U :=
  (γ.val.flip w).comp j.toLinearMap

theorem pairingFunctional_apply (γ : InvariantBilinear.forms ρ π (fun _ => (1 : ℂ)))
    (j : σ.IntertwiningMap ρ) (w : W) (u : U) :
    pairingFunctional γ j w u = γ.val (j u) w :=
  rfl

/-- `γ (ρ g v) (π g w) = γ v w`. -/
theorem invariant_apply (γ : InvariantBilinear.forms ρ π (fun _ => (1 : ℂ))) (g : G)
    (v : V) (w : W) : γ.val (ρ g v) (π g w) = γ.val v w :=
  (γ.property g v w).trans (one_mul _)

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem pairingFunctional_mem (hπ : IsSmooth π)
    (γ : InvariantBilinear.forms ρ π (fun _ => (1 : ℂ))) (j : σ.IntertwiningMap ρ) (w : W) :
    pairingFunctional γ j w ∈ smoothVectors σ.dual := by
  obtain ⟨K, hK⟩ := hπ w
  refine ⟨K, ?_⟩
  rw [fixedVectors, Representation.mem_invariants]
  intro k
  apply LinearMap.ext
  intro u
  have hw : π ((k : G)⁻¹) w = w := (Representation.mem_invariants _ _).mp hK k⁻¹
  change γ.val (j (σ (k : G)⁻¹ u)) w = γ.val (j u) w
  rw [j.isIntertwining]
  conv_lhs => rw [← hw]
  exact invariant_apply γ _ _ _

/-- The intertwiner `π → σ̃`, `w ↦ (u ↦ γ (j u) w)`. -/
def pairingMap (hπ : IsSmooth π) (γ : InvariantBilinear.forms ρ π (fun _ => (1 : ℂ)))
    (j : σ.IntertwiningMap ρ) : π.IntertwiningMap (smoothContragredient σ) where
  toFun w := ⟨pairingFunctional γ j w, pairingFunctional_mem hπ γ j w⟩
  map_add' w w' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    exact map_add (γ.val (j u)) w w'
  map_smul' c w := by
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    exact map_smul (γ.val (j u)) c w
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    change γ.val (j u) (π g w) = γ.val (j (σ g⁻¹ u)) w
    rw [j.isIntertwining, ← invariant_apply γ g (ρ g⁻¹ (j u)) w, ρ.self_inv_apply]

theorem pairingMap_apply (hπ : IsSmooth π)
    (γ : InvariantBilinear.forms ρ π (fun _ => (1 : ℂ))) (j : σ.IntertwiningMap ρ) (w : W)
    (u : U) : (pairingMap hπ γ j w).val u = γ.val (j u) w :=
  rfl

/-- If `γ` is nondegenerate in `ρ`, `j` is injective and `σ` is irreducible, the map
`π → σ̃` is nonzero. -/
theorem pairingMap_ne_zero (hπ : IsSmooth π)
    (γ : InvariantBilinear.forms ρ π (fun _ => (1 : ℂ)))
    (hγ : ∀ v, (∀ w, γ.val v w = 0) → v = 0)
    (j : σ.IntertwiningMap ρ) (hj : Function.Injective j) (hσ : σ.IsIrreducible) :
    pairingMap hπ γ j ≠ 0 := by
  obtain ⟨u, hu⟩ := Langlands.CuspidalSupport.LeviAdmissibility.exists_ne_zero_of_isIrreducible σ hσ
  have hju : j u ≠ 0 := by
    intro h
    exact hu (hj (h.trans (map_zero j).symm))
  obtain ⟨w, hw⟩ : ∃ w, γ.val (j u) w ≠ 0 := by
    by_contra! h
    exact hju (hγ _ h)
  intro h0
  apply hw
  rw [← pairingMap_apply hπ γ j w u, h0]
  rfl

end Quotient

section Pairing

open scoped NNReal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For `ι : ω ↪ P` and `e : P' ≃ ν P̃`, the form `β v w = (e w) (ι v)` on the mirabolic
restrictions has covariance `|det|` and is nondegenerate in `ω`. -/
theorem exists_restricted_pairing {N : ℕ}
    (ω P P' : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier))
    (ι : letI := T.topology
      ω.representation.IntertwiningMap P.representation) (hι : Function.Injective ι)
    (e : letI := T.topology
      letI := T.generalLinearTopologicalGroup (N + 1)
      P'.representation.Equiv
        (twist (T.determinantPowerCharacter (N + 1) 1) (smoothContragredient P.representation))) :
    letI := T.topology
    ∃ β : InvariantBilinear.forms
        ((Derivative.generalLinearRestriction T N).obj ω).representation
        ((Derivative.generalLinearRestriction T N).obj P').representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
      ∀ v, (∀ w, β.val v w = 0) → v = 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (N + 1)
  let β : ω →ₗ[ℂ] P' →ₗ[ℂ] ℂ :=
    (((smoothDualPairing P.representation).comp e.toIntertwiningMap.toLinearMap).flip).comp
      ι.toLinearMap
  have hcov : ∀ (g : GeneralLinear (N + 1) F.Carrier) (v : ω.obj) (w : P'.obj),
      β (ω.representation g v) (P'.representation g w) =
        ((((T.determinantNorm (N + 1)) g : ℝ≥0) : ℝ) : ℂ) * β v w := by
    intro g v w
    change (e.toIntertwiningMap (P'.representation g w)).val (ι (ω.representation g v)) =
      _ * (e.toIntertwiningMap w).val (ι v)
    rw [e.toIntertwiningMap.isIntertwining, ι.isIntertwining]
    change (T.determinantPowerCharacter (N + 1) 1 g : ℂ) *
        (e.toIntertwiningMap w).val (P.representation g⁻¹ (P.representation g (ι v))) = _
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      coe_realPowerCharacter, Real.rpow_one]
  have hnd : ∀ v : ω.obj, (∀ w : P'.obj, β v w = 0) → v = 0 := by
    intro v hv
    apply hι
    rw [map_zero]
    apply smoothBidual_injective_of_compact_cofinal (GeneralLinear.compactOpen_cofinal F T (N + 1))
      P.representation P.isSmooth
    rw [map_zero]
    apply Subtype.ext
    apply LinearMap.ext
    intro ℓ
    have h := hv (e.symm ℓ)
    change (e.toIntertwiningMap (e.symm ℓ)).val (ι v) = 0 at h
    rw [show e.toIntertwiningMap (e.symm ℓ) = ℓ from e.apply_symm_apply ℓ] at h
    exact h
  exact ⟨⟨β, fun g v w => hcov g.val v w⟩, hnd⟩

end Pairing

section Support

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

open PadicField.TopologicalData

theorem ofFn_twistedDualData (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF}) :
    (List.ofFn (twistedDualData t ρ) : Multiset T.CuspidalDatum.{uV, uF}) =
      (List.ofFn ρ : Multiset T.CuspidalDatum.{uV, uF}).map
        (fun x => (dualDatum x).twist t) := by
  rw [Multiset.map_coe, List.map_ofFn]
  exact congrArg (fun f => ((List.ofFn f : List T.CuspidalDatum.{uV, uF}) :
    Multiset T.CuspidalDatum.{uV, uF})) (funext fun i => twistedDualData_apply t ρ i)

/-- From `supp σ̃ ≤ ν · supp ω̃` to `ν · supp σ ≤ supp ω`. -/
theorem support_shift {s s' : Multiset T.CuspidalDatum.{uV, uF}}
    (h : s'.map (fun x => (dualDatum x).twist 0) ≤ s.map (fun x => (dualDatum x).twist 1)) :
    s'.map (CuspidalDatum.twist 1) ≤ s := by
  have h1 : ∀ x : T.CuspidalDatum.{uV, uF},
      (dualDatum ((dualDatum x).twist 0)).twist 1 = x.twist 1 := by
    intro x
    rw [CuspidalDatum.twist_zero, dualDatum_dualDatum]
  have h2 : ∀ x : T.CuspidalDatum.{uV, uF}, (dualDatum ((dualDatum x).twist 1)).twist 1 = x := by
    intro x
    rw [dualDatum_twist, dualDatum_dualDatum, CuspidalDatum.twist_twist, add_neg_cancel,
      CuspidalDatum.twist_zero]
  calc s'.map (CuspidalDatum.twist 1)
      = (s'.map (fun x => (dualDatum x).twist 0)).map (fun y => (dualDatum y).twist 1) := by
        rw [Multiset.map_map]
        exact Multiset.map_congr rfl fun x _ => (h1 x).symm
    _ ≤ (s.map (fun x => (dualDatum x).twist 1)).map (fun y => (dualDatum y).twist 1) :=
        Multiset.map_le_map h
    _ = s := by
        rw [Multiset.map_map]
        conv_rhs => rw [← Multiset.map_id s]
        exact Multiset.map_congr rfl fun x _ => h2 x

end Support

section DualSupport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

theorem twist_determinantPowerCharacter_zero (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (X : letI := T.topology
      Representation ℂ (GeneralLinear m F.Carrier) V) :
    letI := T.topology
    twist (T.determinantPowerCharacter m 0) X = X := by
  let := T.topology
  show twist (realPowerCharacter (T.determinantNorm m) 0) X = X
  rw [realPowerCharacter_zero, twist_one]

/-- If `σ ↪ ρ_1 × ⋯ × ρ_r` and `σ̃` is irreducible, then `σ̃` is a constituent of
`ρ̃_1 × ⋯ × ρ̃_r`: dualizing the embedding gives a surjection onto `σ̃`. -/
theorem isCuspidalConstituent_contragredient {m : ℕ} (hm : 0 < m) {r : ℕ}
    (ρ : Fin r → T.CuspidalDatum.{uV, uF}) (h : ∑ i, (ρ i).rank = m)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i))
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (j : letI := T.topology
      σ.representation.IntertwiningMap (T.cuspidalProductInduced ρ h A).representation)
    (hj : Function.Injective j)
    (hτ : letI := T.topology
      letI := T.generalLinearTopologicalGroup m
      σ.contragredient.IsIrreducible) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    T.IsCuspidalConstituent (twistedDualData 0 ρ) σ.contragredient := by
  let := T.topology
  let := T.generalLinearTopologicalGroup m
  let e := twistedDualEquiv F T hm 0 ρ h A
  let e₀ := equivOfRepresentationEq (twist_determinantPowerCharacter_zero F T m
    (smoothContragredient (T.cuspidalProductInduced ρ h A).representation))
  let f : (T.cuspidalProductInduced (twistedDualData 0 ρ) (twistedDualData_sum F T 0 ρ h)
      (twistedDualRep 0 ρ A)).representation.IntertwiningMap
      (smoothContragredient σ.representation) :=
    (contragredientMap j).comp (e₀.toIntertwiningMap.comp e.toIntertwiningMap)
  have hf : Function.Surjective f :=
    (contragredientMap_surjective_of_injective_of_compact_cofinal
      (GeneralLinear.compactOpen_cofinal F T m) σ.isSmooth
      (T.cuspidalProductInduced ρ h A).isSmooth j hj).comp
      (e₀.toLinearEquiv.surjective.comp e.toLinearEquiv.surjective)
  exact ⟨twistedDualData_sum F T 0 ρ h, twistedDualRep 0 ρ A, twistedDualRep_represents 0 ρ A hA,
    hτ, SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom f, hf⟩⟩

end DualSupport

section Main

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- BZ77 4.8: the 3.8 pairing between `ω^(k)` and `(ν Π̃)^(k)` gives a nonzero map
`(ν Π̃)^(k) → σ̃` for every irreducible `σ ⊆ ω^(k)`. -/
theorem exists_derivative_map
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {N k : ℕ} (hk : k ≤ N + 1) (hk0 : 0 < k)
    (ω : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1) F.Carrier))
    (hnt : Nontrivial
      ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) k hk).obj ω))
    (hhigh : ∀ (j : ℕ) (hj : j ≤ N + 1), k < j →
      Subsingleton
        ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) j hj).obj ω))
    {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF}) (h : ∑ i, (ρ i).rank = N + 1)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (ι : letI := T.topology
      ω.representation.IntertwiningMap (T.cuspidalProductInduced ρ h A).representation)
    (hι : Function.Injective ι)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1 - k) F.Carrier))
    (hσ : letI := T.topology
      Representation.IsIrreducible σ.representation)
    (j : letI := T.topology
      σ.representation.IntertwiningMap
      ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) k hk).obj
        ω).representation)
    (hj : Function.Injective j) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (N + 1 - k)
    ∃ χ : ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) k hk).obj
        (T.cuspidalProductInduced (twistedDualData 1 ρ) (twistedDualData_sum F T 1 ρ h)
          (twistedDualRep 1 ρ A))).representation.IntertwiningMap
        (smoothContragredient σ.representation), χ ≠ 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (N + 1 - k)
  obtain ⟨β, hβ⟩ := exists_restricted_pairing F T ω (T.cuspidalProductInduced ρ h A)
    (T.cuspidalProductInduced (twistedDualData 1 ρ) (twistedDualData_sum F T 1 ρ h)
      (twistedDualRep 1 ρ A)) ι hι (twistedDualEquiv F T (Nat.succ_pos N) 1 ρ h A)
  rw [generalLinearDerivative_obj_eq T ψ N k hk hk0] at hnt
  have hhigh' : ∀ (i : ℕ) (hi : 0 < i ∧ i ≤ N + 1), k < i →
      Subsingleton ((Derivative.mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ N i hi).obj
        ((Derivative.generalLinearRestriction T N).obj ω)) := by
    intro i hi hki
    have hs := hhigh i hi.2 hki
    rwa [generalLinearDerivative_obj_eq T ψ N i hi.2 hi.1] at hs
  have key := Derivative.mirabolicHighestDerivativePairing.{uF, max uF uV, max uF uV} F T ψ N
    ((Derivative.generalLinearRestriction T N).obj ω)
    ((Derivative.generalLinearRestriction T N).obj
      (T.cuspidalProductInduced (twistedDualData 1 ρ) (twistedDualData_sum F T 1 ρ h)
        (twistedDualRep 1 ρ A))) k ⟨hk0, hk⟩ hnt hhigh' β hβ
  rw [← generalLinearDerivative_obj_eq T ψ N k hk hk0 ω] at key
  obtain ⟨γ, hγ⟩ := key
  rw [generalLinearDerivative_obj_eq T ψ N k hk hk0 (T.cuspidalProductInduced (twistedDualData 1 ρ)
    (twistedDualData_sum F T 1 ρ h) (twistedDualRep 1 ρ A))]
  exact ⟨pairingMap (SmoothRep.isSmooth _) γ j, pairingMap_ne_zero _ γ hγ j hj hσ⟩

end Main

end Langlands.Classification.HighestDerivativeSupportShiftProof

namespace Langlands.Classification

open CategoryTheory HighestDerivativeSupportShiftProof PadicField.TopologicalData

universe uF uV

/-- BZ77 Lemma 4.7(b) (Ze80 4.4(d)): if `k` is the highest order of a nonzero derivative
of an irreducible `ω` and `σ ⊆ ω^(k)` is irreducible, then `ν · supp σ ≤ supp ω`. -/
theorem highestDerivativeSupportShift {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : HighestDerivativeSupportShift.{uF, uV} F T := by
  let := T.topology
  intro ψ n ω k hk hω hnt hhigh σ hσ s s' hs hs'
  obtain hkn | hkn := Nat.lt_or_ge k n
  swap
  · exact hs'.twist_le_of_rank_zero (by omega) s
  have hn : 0 < n := by omega
  have hk0 : 0 < k := Derivative.highestGeneralLinearDerivativeOrder_pos T ψ hn hk ω hnt hhigh
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  obtain ⟨r, ρ, hsub⟩ := glSupercuspidalEmbedding.{uV, uF} p F T (N + 1) hn ω hω
  have hρs : (List.ofFn ρ : Multiset T.CuspidalDatum.{uV, uF}) = s :=
    glSupercuspidalSupportUniqueness.{uV, uF} p F T (N + 1) hn ω hω _ _
      ⟨r, ρ, rfl, hsub.isCuspidalConstituent⟩ hs
  obtain ⟨h, A, hA, -, ι, hι⟩ := hsub
  obtain ⟨hσirr, j, hj⟩ := hσ
  have hm : 0 < N + 1 - k := by omega
  let := T.generalLinearTopologicalGroup (N + 1 - k)
  have hadm := (CuspidalSupport.cuspidalEmbedding.{uF, max uF uV} F T (N + 1 - k) σ hσirr).1
  have hτ : σ.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff
      (GeneralLinear.compactOpen_cofinal F T (N + 1 - k)) σ hadm).mpr hσirr
  obtain ⟨χ, hχ⟩ := exists_derivative_map F T ψ hk hk0 ω hnt hhigh ρ h A ι hι σ hσirr j hj
  obtain ⟨l, ρ'', hρ'', hle⟩ :=
    CuspidalProductDerivativeQuotientSupport.derivative_quotient_support T ψ hk hk0 hkn
      (twistedDualData 1 ρ) (twistedDualData_sum F T 1 ρ h) (twistedDualRep 1 ρ A)
      (twistedDualRep_represents 1 ρ A hA) σ.contragredient hτ χ.toLinearMap
      (fun h0 => hχ (Representation.IntertwiningMap.ext h0)) (fun g v => by
        have hgv := LinearMap.congr_fun (χ.isIntertwining' g) v; exact hgv)
  obtain ⟨rσ, ρσ, hσsub⟩ := glSupercuspidalEmbedding.{uV, uF} p F T (N + 1 - k) hm σ hσirr
  have hρσ : (List.ofFn ρσ : Multiset T.CuspidalDatum.{uV, uF}) = s' :=
    glSupercuspidalSupportUniqueness.{uV, uF} p F T (N + 1 - k) hm σ hσirr _ _
      ⟨rσ, ρσ, rfl, hσsub.isCuspidalConstituent⟩ hs'
  obtain ⟨hσh, Aσ, hAσ, -, jσ, hjσ⟩ := hσsub
  have hτc := isCuspidalConstituent_contragredient F T hm ρσ hσh Aσ hAσ σ jσ hjσ hτ
  have hdual := glSupercuspidalSupportUniqueness.{uV, uF} p F T (N + 1 - k) hm
    σ.contragredient hτ _ _ ⟨l, ρ'', rfl, hρ''⟩ ⟨rσ, _, rfl, hτc⟩
  rw [hdual, ofFn_twistedDualData, ofFn_twistedDualData, hρσ, hρs] at hle
  exact support_shift hle

end Langlands.Classification
