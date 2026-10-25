import Langlands.Representation.Whittaker.Iwasawa
import Langlands.LocalField.Uniformizer
import Langlands.Group.GL.SingletonBlocks
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Concrete Cartan cells modulo the center

All cells are subsets of the actual central quotient. The definitions carry no
covering, disjointness, compactness, or measure estimate as an assumption.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.GeneralLinear.CartanQuotient

universe uF

/-- A decreasing integer tuple normalized modulo common shifts. -/
def Normalized {n : ℕ} (lam : Fin n → ℤ) : Prop :=
  Antitone lam ∧ (∀ i, 0 ≤ lam i) ∧ ∃ i, lam i = 0

/-- The actual normalized chamber, with no decomposition data attached. -/
abbrev NormalizedTuple (n : ℕ) := {lam : Fin n → ℤ // Normalized lam}

/-- Common translation of all elementary exponents. -/
def shift {n : ℕ} (lam : Fin n → ℤ) (c : ℤ) : Fin n → ℤ :=
  fun i => lam i + c

/-- Sum of the positive-root differences. -/
def degree {n : ℕ} (lam : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), (lam i - lam j)

/-- A concrete polynomial weight on the integer chamber. -/
def height {n : ℕ} (lam : Fin n → ℤ) : ℝ :=
  1 + ∑ i : Fin n, (|lam i| : ℤ)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The quotient of the actual general linear group by its entire center. -/
abbrev centralQuotient (n : ℕ) :=
  GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)

/-- The actual quotient homomorphism. -/
abbrev quotientMap (n : ℕ) : GeneralLinear n F.Carrier →* centralQuotient F n :=
  QuotientGroup.mk' (Subgroup.center (GeneralLinear n F.Carrier))

variable {F} (T : F.TopologicalData)

/-- The standard integral subgroup, the image of `GL_n(O_F)` in `GL_n(F)`. -/
abbrev maximalCompact (n : ℕ) : Subgroup (GeneralLinear n F.Carrier) :=
  Iwasawa.integralRange T.discreteValuation n

/-- The diagonal representative with entries equal to powers of the specified uniformizer. -/
def representative {n : ℕ} (lam : Fin n → ℤ) : GeneralLinear n F.Carrier :=
  Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit T) lam

/-- The same diagonal data in the actual singleton-block Levi. -/
def representativeLevi {n : ℕ} (lam : Fin n → ℤ) :
    (BlockShape.singletons n).Levi F.Carrier :=
  BlockShape.singletonLevi F.Carrier
    (fun i => LocalFactor.PadicAbelian.uniformizerUnit T ^ lam i)

/-- The singleton-Levi diagonal embedded into the actual upper Borel. -/
def representativeBorel {n : ℕ} (lam : Fin n → ℤ) :
    (BlockShape.singletons n).parabolic F.Carrier :=
  (BlockShape.singletons n).leviInParabolic F.Carrier (representativeLevi T lam)

/-- Quotient images of `H a(lam) H`. The definition also permits subgroups outside `K`. -/
def subgroupCell {n : ℕ} (H : Subgroup (GeneralLinear n F.Carrier))
    (lam : Fin n → ℤ) : Set (centralQuotient F n) :=
  {x | ∃ h₁ ∈ H, ∃ h₂ ∈ H,
    x = quotientMap F n (h₁ * representative T lam * h₂)}

/-- The actual Cartan cell in `GL_n(F)/Z`, defined for every integer tuple. -/
def cell {n : ℕ} (lam : Fin n → ℤ) : Set (centralQuotient F n) :=
  subgroupCell T (maximalCompact T n) lam

/-- The standard integral subgroup's image in the central quotient. -/
def compactImage (n : ℕ) : Subgroup (centralQuotient F n) :=
  (maximalCompact T n).map (quotientMap F n)

/-- The radial upper-Borel modulus formula, with `q` the actual residue cardinality. -/
def delta {n : ℕ} (lam : Fin n → ℤ) : ℝ :=
  (T.residueCardinality : ℝ) ^ (-degree lam)

@[simp] theorem mem_subgroupCell {n : ℕ} (H : Subgroup (GeneralLinear n F.Carrier))
    (lam : Fin n → ℤ) (x : centralQuotient F n) :
    x ∈ subgroupCell T H lam ↔ ∃ h₁ ∈ H, ∃ h₂ ∈ H,
      x = quotientMap F n (h₁ * representative T lam * h₂) := Iff.rfl

@[simp] theorem mem_cell {n : ℕ} (lam : Fin n → ℤ) (x : centralQuotient F n) :
    x ∈ cell T lam ↔ ∃ k₁ ∈ maximalCompact T n, ∃ k₂ ∈ maximalCompact T n,
      x = quotientMap F n (k₁ * representative T lam * k₂) := Iff.rfl

end Langlands.GeneralLinear.CartanQuotient
