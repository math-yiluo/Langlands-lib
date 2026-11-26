import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.RankinSelberg.DualWhittakerType
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Group.GL.HeadTailBlocks
import Langlands.Representation.Twist.PullbackProof
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Representation.Parabolic.HeadTailProductInduction
import Langlands.AllField.Representation.Induction.InverseTranspose
import Langlands.AllField.Representation.Induction.OppositeProductReversalProof
import Langlands.AllField.Representation.Induction.BlockEquivalence

/-!
# Tempered blocks with real exponents over a nonarchimedean local field

The data of JPSS 1983, (9.4) (printed page 458), with the order of the exponents
relaxed to a non-strict one: an ordered block shape, irreducible tempered
representations `τ_i` of the blocks, each of Whittaker type for every nontrivial
additive character, and real exponents `u_1 ≥ ⋯ ≥ u_r`. The standard module is the
normalized induction `Ind(τ_1 ν^(u_1), …, τ_r ν^(u_r))` from the standard upper block
parabolic, `ν = |det|`. The datum is closed under deleting the first block and under
the reversed inverse transpose `(τ_r^ι, …, τ_1^ι)` with exponents `(-u_r, …, -u_1)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.RankinSelberg (IsOfWhittakerType isOfWhittakerType_inverseTransposePullback
  isOfWhittakerType_twist_iff standardCharacter_scale_neg_one
  inverseStandardCharacter_scale_neg_one)
open scoped NNReal

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]

section Tempered

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Temperedness modulo the center of a representation of `GL_n(F)`, for every Haar
measure on the Borel structure of the central quotient: admissibility, a unitary
central character, and matrix coefficients in `L^(2+ε)` modulo the center for every
`ε > 0`. -/
def IsTemperedRepresentation (ρ : Representation ℂ (GeneralLinear n F) V) : Prop :=
  haveI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
  letI : MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) :=
    borel _
  haveI : BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) := ⟨rfl⟩
  ∀ (μ : MeasureTheory.Measure (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)))
    [MeasureTheory.Measure.IsHaarMeasure μ], IsTemperedModCenter ρ μ

/-- Temperedness is preserved by pullback along a continuous automorphism. -/
theorem IsTemperedRepresentation.comp_continuousMulEquiv
    {ρ : Representation ℂ (GeneralLinear n F) V}
    (e : GeneralLinear n F ≃ₜ* GeneralLinear n F)
    (hρ : IsTemperedRepresentation ρ) : IsTemperedRepresentation (ρ.comp e.toMonoidHom) := by
  have := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
  let : MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) := borel _
  have : BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) := ⟨rfl⟩
  intro μ hμ
  exact isTemperedModCenter_comp_continuousMulEquiv ρ e μ (hρ _)

end Tempered

section Whittaker

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- Whittaker type for the standard character at an arbitrary rank; rank zero is
excluded. -/
def IsOfRankWhittakerType (ψ : UnitaryAdditiveCharacter F) {n : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) : Prop :=
  match n, π with
  | r + 1, π => IsOfWhittakerType r (standardCharacter ψ r) π
  | 0, _ => False

theorem isOfRankWhittakerType_succ (ψ : UnitaryAdditiveCharacter F) {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GeneralLinear (r + 1) F) V) :
    IsOfRankWhittakerType ψ π ↔ IsOfWhittakerType r (standardCharacter ψ r) π :=
  Iff.rfl

theorem IsOfRankWhittakerType.of_equiv {ψ : UnitaryAdditiveCharacter F}
    {n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear n F) W}
    (hπ : IsOfRankWhittakerType ψ π) (e : π.Equiv σ) : IsOfRankWhittakerType ψ σ := by
  cases n with
  | zero => exact hπ.elim
  | succ n => exact Langlands.RankinSelberg.IsOfWhittakerType.of_equiv hπ e

end Whittaker

section Characters

/-- The complex character `g ↦ |det g|^s` of `GL_n(F)`, with the residue-normalized
absolute value. -/
abbrev determinantPowerCharacter (n : ℕ) (s : ℝ) : GeneralLinear n F →* ℂˣ :=
  realPowerCharacter ((⟨⟩ : LocalFieldData F).determinantNorm n) s

theorem isOpen_ker_determinantPowerCharacter (n : ℕ) (s : ℝ) :
    IsOpen ((determinantPowerCharacter (F := F) n s).ker : Set (GeneralLinear n F)) := by
  have := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
  exact isOpen_ker_realPowerCharacter _ ((⟨⟩ : LocalFieldData F).isOpen_ker_determinantNorm n) s

/-- The determinant-power character is trivial on the upper unipotent subgroup. -/
theorem determinantPowerCharacter_upperUnipotent (r : ℕ) (s : ℝ)
    (u : upperUnipotent (r + 1) F) : determinantPowerCharacter (F := F) (r + 1) s u.val = 1 := by
  have hdet : GeneralLinear.determinant (u.val : GeneralLinear (r + 1) F) = 1 := by
    apply Units.ext
    change Matrix.det u.val.val = 1
    rw [Matrix.det_of_isUpperTriangular u.property.1]
    simp only [UpperUnipotent.entry_diag, Finset.prod_const_one]
  have hnorm : (⟨⟩ : LocalFieldData F).determinantNorm (r + 1) u.val = 1 := by
    change (⟨⟩ : LocalFieldData F).normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [hdet, map_one]
  apply Units.ext
  rw [coe_realPowerCharacter, hnorm]
  simp

/-- Inverse transpose negates the real exponent of the determinant-power character. -/
theorem determinantPowerCharacter_inverseTranspose (n : ℕ) (s : ℝ) :
    (determinantPowerCharacter (F := F) n s).comp
        (GeneralLinear.inverseTranspose n F).toMonoidHom =
      determinantPowerCharacter (F := F) n (-s) := by
  apply MonoidHom.ext
  intro g
  change realPowerCharacter ((⟨⟩ : LocalFieldData F).determinantNorm n) s
      (GeneralLinear.inverseTranspose n F g) =
    realPowerCharacter ((⟨⟩ : LocalFieldData F).determinantNorm n) (-s) g
  rw [realPowerCharacter_neg, MonoidHom.inv_apply]
  change (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom s)))
      ((⟨⟩ : LocalFieldData F).determinantNorm n (GeneralLinear.inverseTranspose n F g)) = _
  rw [(⟨⟩ : LocalFieldData F).determinantNorm_inverseTranspose, map_inv]
  rfl

/-- Twisting by a determinant power preserves Whittaker type at every positive rank. -/
theorem isOfRankWhittakerType_twist_iff (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) (s : ℝ) :
    IsOfRankWhittakerType ψ (twist (determinantPowerCharacter (F := F) n s) π) ↔
      IsOfRankWhittakerType ψ π := by
  cases n with
  | zero => exact Iff.rfl
  | succ r =>
    simp only [isOfRankWhittakerType_succ]
    exact isOfWhittakerType_twist_iff (standardCharacter ψ r)
      (determinantPowerCharacter (F := F) (r + 1) s) π
      (isOpen_ker_determinantPowerCharacter (r + 1) s)
      (determinantPowerCharacter_upperUnipotent r s)

/-- Inverse transpose exchanges Whittaker type for `ψ⁻¹` with Whittaker type for `ψ`. -/
theorem isOfRankWhittakerType_inverseTranspose (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V)
    (hπ : IsOfRankWhittakerType (ψ.scale (-1)) π) :
    IsOfRankWhittakerType ψ (π.comp (GeneralLinear.inverseTranspose n F).toMonoidHom) := by
  cases n with
  | zero => exact hπ.elim
  | succ r =>
    have h := isOfWhittakerType_inverseTransposePullback (ψ.scale (-1)) π
      ((isOfRankWhittakerType_succ _ π).mp hπ)
    rw [inverseStandardCharacter_scale_neg_one] at h
    exact (isOfRankWhittakerType_succ ψ _).mpr h

end Characters

/-- Tempered blocks with antitone real exponents on `GL_n(F)`: an ordered block shape
`(n_1, …, n_r)`, irreducible tempered representations `τ_i` of `GL_(n_i)(F)`, each of
Whittaker type for every nontrivial additive character, and real exponents
`u_1 ≥ ⋯ ≥ u_r`. -/
structure TemperedTypeDatum (n : ℕ) where
  /-- The ordered block shape `(n_1, …, n_r)` of `n`. -/
  shape : BlockShape n
  /-- The tempered blocks `τ_i`. -/
  blocks : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (shape.size i) F)
  irreducible : ∀ i, Representation.IsIrreducible (blocks i).representation
  tempered : ∀ i, IsTemperedRepresentation (blocks i).representation
  whittaker : ∀ (ψ : UnitaryAdditiveCharacter F) (i : Fin shape.length),
    IsOfRankWhittakerType ψ (blocks i).representation
  /-- The real exponents `u_i`. -/
  exponent : Fin shape.length → ℝ
  antitone : Antitone exponent

namespace TemperedTypeDatum

variable {n : ℕ} (d : TemperedTypeDatum.{uF, uV} (F := F) n)

/-- The twisted block `τ_i ν^(u_i)`, `ν = |det|`. -/
abbrev twistedBlock (i : Fin d.shape.length) :
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (d.shape.size i) F) :=
  (d.blocks i).twist (determinantPowerCharacter (d.shape.size i) (d.exponent i))
    (isOpen_ker_determinantPowerCharacter (d.shape.size i) (d.exponent i))

/-- The standard module `Ind(τ_1 ν^(u_1), …, τ_r ν^(u_r))`: normalized induction from the
standard upper block parabolic. -/
abbrev standardModule :=
  (⟨⟩ : LocalFieldData F).normalizedProductInduced d.shape
    (fun i => (d.twistedBlock i).representation)

theorem twistedBlock_whittaker (ψ : UnitaryAdditiveCharacter F) (i : Fin d.shape.length) :
    IsOfRankWhittakerType ψ (d.twistedBlock i).representation :=
  (isOfRankWhittakerType_twist_iff ψ _ _).mpr (d.whittaker ψ i)

section Tail

variable {k : ℕ} (h : d.shape.length = k + 2)

/-- Remove the first block, keeping the remaining blocks and exponents in order. -/
def tail : TemperedTypeDatum.{uF, uV} (F := F) (d.shape.tailRank h) where
  shape := d.shape.tailShape h
  blocks j := d.blocks (d.shape.tailIndex h j)
  irreducible j := d.irreducible (d.shape.tailIndex h j)
  tempered j := d.tempered (d.shape.tailIndex h j)
  whittaker ψ j := d.whittaker ψ (d.shape.tailIndex h j)
  exponent j := d.exponent (d.shape.tailIndex h j)
  antitone := d.antitone.comp_monotone (d.shape.tailIndex_strictMono h).monotone

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem tail_length_lt : (d.tail h).shape.length < d.shape.length := by
  change k + 1 < d.shape.length
  omega

/-- The first twisted block, lifted to the carrier universe of the tail standard module,
and the tail standard module. -/
abbrev headTailStandardFactors :
    ∀ i : Fin 2, SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear ((d.shape.headTailShape h).size i) F) :=
  (⟨⟩ : LocalFieldData F).headTailProductFactors d.shape h d.twistedBlock

/-- Split the standard module into its first twisted block and the standard module of
the tail. -/
def headTailStandardModuleEquiv :
    Representation.Equiv d.standardModule
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (d.shape.headTailShape h)
        (fun i => (d.headTailStandardFactors h i).representation)) :=
  (⟨⟩ : LocalFieldData F).headTailProductInductionEquiv d.shape h d.twistedBlock

theorem headTailStandardFactors_one :
    (d.headTailStandardFactors h 1).representation = (d.tail h).standardModule := rfl

end Tail

section InverseTranspose

/-- Reverse the blocks, pull their actions back by inverse transpose, and negate the
exponents. -/
def inverseTranspose : TemperedTypeDatum.{uF, uV} (F := F) n where
  shape := d.shape.reverse
  blocks i := SmoothRep.pullback (GeneralLinear.inverseTransposeContinuous _ F)
    (d.blocks i.rev)
  irreducible i := (isIrreducible_comp_continuousMulEquiv_iff
    (d.blocks i.rev).representation
    (GeneralLinear.inverseTransposeContinuous _ F)).mpr (d.irreducible i.rev)
  tempered i := (d.tempered i.rev).comp_continuousMulEquiv
    (GeneralLinear.inverseTransposeContinuous _ F)
  whittaker ψ i := isOfRankWhittakerType_inverseTranspose ψ _ (d.whittaker (ψ.scale (-1)) i.rev)
  exponent i := -d.exponent i.rev
  antitone := by
    intro i j hij
    exact neg_le_neg (d.antitone (Fin.rev_le_rev.mpr hij))

end InverseTranspose

end TemperedTypeDatum

section ProductInverseTranspose

variable {n : ℕ} (B : BlockShape n) (V : Fin B.length → Type uV)
  [hadd : ∀ i, AddCommGroup (V i)] [hmod : ∀ i, Module ℂ (V i)]

/-- Pulling a normalized upper product back by inverse transpose reverses the block order
and pulls back each block by its own inverse transpose. -/
theorem normalizedProductInverseTranspose
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (hσ : ∀ i, IsSmooth (σ i)) :
    letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
    letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
    Nonempty (Representation.Equiv
      (((⟨⟩ : LocalFieldData F).normalizedProductInduced B σ).comp
        (GeneralLinear.inverseTranspose n F).toMonoidHom)
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced B.reverse (V := fun i => V i.rev)
        (fun i => (σ i.rev).comp
          (GeneralLinear.inverseTranspose (B.size i.rev) F).toMonoidHom))) := by
  let T : LocalFieldData F := ⟨⟩
  let := T.generalLinearTopologicalGroup n
  have hτ (i : Fin B.length) : IsSmooth ((σ i).comp
      (GeneralLinear.inverseTranspose (B.size i) F).toMonoidHom) :=
    isSmooth_comp _ (GeneralLinear.continuous_inverseTranspose _ _) (hσ i)
  obtain ⟨E, _, _⟩ := glOppositeProductReversal F T n B V
    (fun i => (σ i).comp
      (GeneralLinear.inverseTranspose (B.size i) F).toMonoidHom) hτ
  exact ⟨(T.inverseTransposeProductToOppositeEquiv B σ).trans E⟩

end ProductInverseTranspose

namespace TemperedTypeDatum

variable {n : ℕ} (d : TemperedTypeDatum.{uF, uV} (F := F) n)

section InverseTranspose

theorem inverseTranspose_twistedBlock_representation (i : Fin d.shape.reverse.length) :
    (d.inverseTranspose.twistedBlock i).representation =
      (d.twistedBlock i.rev).representation.comp
        (GeneralLinear.inverseTranspose (d.shape.size i.rev) F).toMonoidHom := by
  change twist (determinantPowerCharacter (d.shape.size i.rev) (-d.exponent i.rev))
      ((d.blocks i.rev).representation.comp
        (GeneralLinear.inverseTransposeContinuous _ F).toMonoidHom) =
    (twist (determinantPowerCharacter (d.shape.size i.rev) (d.exponent i.rev))
      (d.blocks i.rev).representation).comp _
  rw [twist_comp, determinantPowerCharacter_inverseTranspose]
  rfl

/-- The block equivalences behind `inverseTransposeStandardModuleEquiv`. -/
def inverseTransposeTwistedBlockEquiv (i : Fin d.shape.reverse.length) :
    Representation.Equiv
      ((d.twistedBlock i.rev).representation.comp
        (GeneralLinear.inverseTranspose (d.shape.size i.rev) F).toMonoidHom)
      (d.inverseTranspose.twistedBlock i).representation :=
  equivOfRepresentationEq (d.inverseTranspose_twistedBlock_representation i).symm

/-- Pulling the standard module back by inverse transpose gives the standard module of
the reversed inverse-transpose datum. -/
def inverseTransposeStandardModuleEquiv :
    Representation.Equiv
      (d.standardModule.comp (GeneralLinear.inverseTranspose n F).toMonoidHom)
      d.inverseTranspose.standardModule :=
  (Classical.choice (normalizedProductInverseTranspose d.shape
    (fun i => ((d.twistedBlock i : SmoothRep.{0, uF, uV} ℂ _) : Type uV))
    (fun i => (d.twistedBlock i).representation)
    (fun i => (d.twistedBlock i).isSmooth))).trans
    ((⟨⟩ : LocalFieldData F).normalizedProductInducedEquiv d.shape.reverse
      d.inverseTransposeTwistedBlockEquiv)

end InverseTranspose

end TemperedTypeDatum

end Langlands.AllField.RankinSelberg
