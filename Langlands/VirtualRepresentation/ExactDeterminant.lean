import Langlands.VirtualRepresentation.Exact
import Mathlib.Algebra.Module.NatInt
import Mathlib.Topology.Algebra.Group.Units
import Langlands.Weil.Representation.Determinant
import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.ExactSequenceProof
import Langlands.Weil.Representation.CharacterNormalizationProof

/-! # Determinant characters of exact virtual complex representations -/

noncomputable section

universe uG uV uA uB uC

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- The published exact-sequence determinant identity, as an equality of characters. -/
theorem determinantCharacter_shortExact
    {A : FiniteRepresentation.{0, uG, uA} ℂ G}
    {B : FiniteRepresentation.{0, uG, uB} ℂ G}
    {C : FiniteRepresentation.{0, uG, uC} ℂ G}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation}
    (h : IsShortExact f g) :
    determinantCharacter B = determinantCharacter A * determinantCharacter C := by
  ext w
  exact (Weil.representationExactSequenceInvariants G A B C
    A.representation B.representation C.representation f g h.1 h.2.1 h.2.2).2 w

/-- Rank zero gives the trivial character, including on nontrivial groups. -/
theorem determinantCharacter_eq_one_of_rank_eq_zero
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (h : A.rank = 0) :
    determinantCharacter A = 1 := by
  ext g
  exact LinearMap.det_eq_one_of_finrank_eq_zero h (A.representation g)

/-- Continuity of the actual determinant character, extracted from the published
normalization theorem with the usual complex topology. -/
theorem continuous_determinantCharacter [TopologicalSpace G]
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hA : A.IsContinuous) :
    Continuous (determinantCharacter A) := by
  obtain ⟨δ, hδ, _⟩ :=
    (Weil.representationCharacterNormalization G A A.representation hA).1
  have he : δ = determinantCharacter A := by
    ext g
    exact hδ.2 g
  simpa only [he] using hδ.1

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G]
variable (P : FiniteRepresentation.{0, uG, uV} ℂ G → Prop)

-- Use the additive monoid inherited from the character group, so its canonical
-- integer-module structure and the quotient universal property share a hierarchy.
local instance : AddCommMonoid (Additive (G →* ℂˣ)) :=
  (inferInstance : AddCommGroup (Additive (G →* ℂˣ))).toAddCommMonoid

/-- The genuine determinant character on classes satisfying the selected predicate,
written additively in the character group. -/
def classDeterminant (c : IsomorphismClassesWith P) : Additive (G →* ℂˣ) :=
  Additive.ofMul (determinantCharacterClass (forgetPropertyClass P c))

/-- Actual determinant multiplicativity kills every actual exact relation. -/
theorem classDeterminant_isExactAdditive : IsExactAdditive P (classDeterminant P) := by
  intro A B C f g h
  change Additive.ofMul (determinantCharacter B.val) =
    Additive.ofMul (determinantCharacter A.val * determinantCharacter C.val)
  exact congrArg Additive.ofMul (determinantCharacter_shortExact h)

/-- The determinant character descended through the exact-relation quotient.
Its additive target notation encodes pointwise multiplication of characters. -/
def determinant : ExactGrothendieckGroup P →ₗ[ℤ] Additive (G →* ℂˣ) :=
  lift P (classDeterminant P) (classDeterminant_isExactAdditive P)

/-- The same determinant in ordinary multiplicative character notation. -/
def determinantCharacter (x : ExactGrothendieckGroup P) : G →* ℂˣ :=
  (determinant P x).toMul

@[simp]
theorem determinant_ofClass (c : IsomorphismClassesWith P) :
    determinant P (ofClass P c) = classDeterminant P c :=
  lift_ofClass P _ _ c

@[simp]
theorem determinantCharacter_ofClass (c : IsomorphismClassesWith P) :
    determinantCharacter P (ofClass P c) =
      FiniteRepresentation.determinantCharacterClass (forgetPropertyClass P c) := by
  change (determinant P (ofClass P c)).toMul = _
  rw [determinant_ofClass]
  rfl

@[simp]
theorem determinantCharacter_ofRepresentation
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) :
    determinantCharacter P (ofRepresentation P A) =
      FiniteRepresentation.determinantCharacter A.val :=
  determinantCharacter_ofClass P (exactClassOf P A)

/-- Actual generator evaluation as a scalar determinant of an action operator. -/
theorem determinantCharacter_ofRepresentation_apply
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) (g : G) :
    (determinantCharacter P (ofRepresentation P A) g : ℂ) =
      LinearMap.det (A.val.representation g) := by
  rw [determinantCharacter_ofRepresentation]
  rfl

@[simp]
theorem determinantCharacter_zero : determinantCharacter P 0 = 1 := by
  simp [determinantCharacter]

@[simp]
theorem determinantCharacter_add (x y : ExactGrothendieckGroup P) :
    determinantCharacter P (x + y) = determinantCharacter P x * determinantCharacter P y := by
  simp [determinantCharacter]

@[simp]
theorem determinantCharacter_neg (x : ExactGrothendieckGroup P) :
    determinantCharacter P (-x) = (determinantCharacter P x)⁻¹ := by
  simp [determinantCharacter]

@[simp]
theorem determinantCharacter_sub (x y : ExactGrothendieckGroup P) :
    determinantCharacter P (x - y) = determinantCharacter P x / determinantCharacter P y := by
  simp [determinantCharacter]

@[simp]
theorem determinantCharacter_zsmul (n : ℤ) (x : ExactGrothendieckGroup P) :
    determinantCharacter P (n • x) = determinantCharacter P x ^ n := by
  simp only [determinantCharacter, map_zsmul, toMul_zsmul]

/-- The determinant as an explicit multiplicative homomorphism on the multiplicative
synonym of the virtual group. -/
def determinantHom : Multiplicative (ExactGrothendieckGroup P) →* (G →* ℂˣ) where
  toFun x := determinantCharacter P x.toAdd
  map_one' := determinantCharacter_zero P
  map_mul' x y := determinantCharacter_add P x.toAdd y.toAdd

@[simp]
theorem determinantCharacter_zero_apply (g : G) : determinantCharacter P 0 g = 1 := by
  rw [determinantCharacter_zero, MonoidHom.one_apply]

@[simp]
theorem determinantCharacter_add_apply (x y : ExactGrothendieckGroup P) (g : G) :
    determinantCharacter P (x + y) g = determinantCharacter P x g * determinantCharacter P y g := by
  rw [determinantCharacter_add, MonoidHom.mul_apply]

@[simp]
theorem determinantCharacter_neg_apply (x : ExactGrothendieckGroup P) (g : G) :
    determinantCharacter P (-x) g = (determinantCharacter P x g)⁻¹ := by
  rw [determinantCharacter_neg, MonoidHom.inv_apply]

@[simp]
theorem determinantCharacter_sub_apply (x y : ExactGrothendieckGroup P) (g : G) :
    determinantCharacter P (x - y) g = determinantCharacter P x g / determinantCharacter P y g := by
  rw [determinantCharacter_sub, MonoidHom.div_apply]

/-- Evaluation of every integral multiple, including negative coefficients. -/
theorem determinantCharacter_zsmul_apply (n : ℤ) (x : ExactGrothendieckGroup P) (g : G) :
    determinantCharacter P (n • x) g = determinantCharacter P x g ^ n := by
  rw [determinantCharacter_zsmul, MonoidHom.zpow_apply]

@[simp]
theorem determinantCharacter_ofRepresentation_rank_zero
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) (h : A.val.rank = 0) :
    determinantCharacter P (ofRepresentation P A) = 1 := by
  rw [determinantCharacter_ofRepresentation]
  exact determinantCharacter_eq_one_of_rank_eq_zero A.val h

/-- Single-coordinate presentations evaluate to integral powers of genuine characters. -/
theorem determinantCharacter_quotientMap_single (c : IsomorphismClassesWith P) (n : ℤ) :
    determinantCharacter P (quotientMap P (Finsupp.single c n)) =
      FiniteRepresentation.determinantCharacterClass (forgetPropertyClass P c) ^ n := by
  have hs : Finsupp.single c n = n • generator c := by simp [generator]
  rw [hs, map_smul, determinantCharacter_zsmul]
  exact congrArg (fun χ : G →* ℂˣ => χ ^ n) (determinantCharacter_ofClass P c)

section Continuity

variable [TopologicalSpace G]

/-- Every virtual determinant in a family of continuous representations is continuous.
Surjectivity of the quotient reduces the proof to a finite integral presentation. -/
theorem continuous_determinantCharacter
    (hP : ∀ A, P A → A.IsContinuous) (x : ExactGrothendieckGroup P) :
    Continuous (determinantCharacter P x) := by
  obtain ⟨v, rfl⟩ := (exactRelations P).mkQ_surjective x
  change Continuous (determinantCharacter P (quotientMap P v))
  induction v using Finsupp.induction_linear with
  | zero =>
      rw [map_zero, determinantCharacter_zero]
      exact continuous_const
  | add v w hv hw =>
      rw [map_add, determinantCharacter_add]
      exact hv.mul hw
  | single c n =>
      rw [determinantCharacter_quotientMap_single]
      induction c using Quotient.inductionOn with
      | h A =>
          change Continuous (fun g : G => FiniteRepresentation.determinantCharacter A.val g ^ n)
          exact (FiniteRepresentation.continuous_determinantCharacter A.val (hP A.val A.property)).zpow n

/-- Determinant on the full family of continuous finite-dimensional complex
representations, with character multiplication encoded additively. -/
def continuousDeterminant :
    ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous) →ₗ[ℤ] Additive (G →* ℂˣ) :=
  determinant _

/-- Each character produced by `continuousDeterminant` is continuous. No topology
on the virtual representation group or space of characters is asserted. -/
theorem continuous_continuousDeterminant
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    Continuous (continuousDeterminant x).toMul :=
  continuous_determinantCharacter _ (fun _ hA => hA) x

end Continuity
end Langlands.VirtualRepresentation.ExactGrothendieckGroup
