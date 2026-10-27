import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Renard B.I: Amitsur's theorem for countable-dimensional complex algebras

Source: Renard, *Représentations des groupes réductifs p-adiques* (French edition
dated 9 July 2026), Appendix B.I "Théorème d'Amitsur", printed pages 271–272 /
PDF pages 277–278. Let `A` be a unital complex algebra of at most countable
dimension over `ℂ`. Then
* a) if `A` is a division algebra, `A = ℂ`;
* b) every element of `A` has nonempty spectrum, and the spectrum of `a` is
  `{0}` if and only if `a` is nilpotent.

The algebras are arbitrary associative unital complex algebras, not necessarily
commutative, with carrier in an arbitrary universe `u`. "Dimension at most
countable" is `Module.rank ℂ A ≤ Cardinal.aleph0`. The spectrum is Mathlib's
`spectrum ℂ a`, defined through `algebraMap ℂ A z - a`; the source uses
`a - z • 1`, and `mem_spectrum_iff_not_isUnit_sub_smul_one` checks that the two
shifts have the same invertibility status. The source identifies the scalar
subalgebra `ℂ 1_A` with `ℂ`, so the general algebra is assumed `Nontrivial`.
Division-algebra scalarity is bijectivity of the actual map `algebraMap ℂ D`;
`amitsurDivisionAlgebraStatement_iff_equivStatement` compares it with the
optional formulation by an algebra isomorphism normalized to that map.

Only propositions are stated here; none of Amitsur's assertions is proved or
assumed.
-/

universe u

namespace Langlands.Renard

/-- Renard B.I, Définition: `z` lies in the spectrum of `a` exactly when the
source's scalar shift `a - z • 1` is not invertible. Mathlib's `spectrum ℂ a` is
defined with the opposite shift `algebraMap ℂ A z - a`, which differs from
`a - z • 1` by negation. -/
theorem mem_spectrum_iff_not_isUnit_sub_smul_one {A : Type u} [Ring A] [Algebra ℂ A]
    (a : A) (z : ℂ) : z ∈ spectrum ℂ a ↔ ¬ IsUnit (a - z • (1 : A)) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub, IsUnit.neg_iff]

/-- Renard B.I, Théorème b), first assertion: in a nontrivial unital complex
algebra of at most countable dimension, every element has nonempty spectrum. -/
@[pp_with_univ]
def AmitsurSpectrumNonemptyStatement (A : Type u) [Ring A] [Algebra ℂ A] [Nontrivial A] :
    Prop :=
  Module.rank ℂ A ≤ Cardinal.aleph0 → ∀ a : A, (spectrum ℂ a).Nonempty

/-- Renard B.I, Théorème b), second assertion: in a nontrivial unital complex
algebra of at most countable dimension, the spectrum of an element is `{0}` if
and only if the element is nilpotent. -/
@[pp_with_univ]
def AmitsurSpectrumSingletonZeroStatement (A : Type u) [Ring A] [Algebra ℂ A]
    [Nontrivial A] : Prop :=
  Module.rank ℂ A ≤ Cardinal.aleph0 →
    ∀ a : A, spectrum ℂ a = ({0} : Set ℂ) ↔ IsNilpotent a

/-- Renard B.I, Théorème a): a complex division algebra of at most countable
dimension is `ℂ`, in the sense that the canonical map `algebraMap ℂ D` is
bijective. -/
@[pp_with_univ]
def AmitsurDivisionAlgebraStatement (D : Type u) [DivisionRing D] [Algebra ℂ D] : Prop :=
  Module.rank ℂ D ≤ Cardinal.aleph0 → Function.Bijective (algebraMap ℂ D)

/-- Renard B.I, Théorème a), as an algebra isomorphism: a complex division
algebra of at most countable dimension admits a complex algebra isomorphism from
`ℂ` that agrees with the canonical map `algebraMap ℂ D`. -/
@[pp_with_univ]
def AmitsurDivisionAlgebraEquivStatement (D : Type u) [DivisionRing D] [Algebra ℂ D] :
    Prop :=
  Module.rank ℂ D ≤ Cardinal.aleph0 →
    ∃ e : ℂ ≃ₐ[ℂ] D, ∀ z : ℂ, e z = algebraMap ℂ D z

/-- The two formulations of Renard B.I, Théorème a) are equivalent: bijectivity of
`algebraMap ℂ D` holds exactly when some complex algebra isomorphism `ℂ ≃ₐ[ℂ] D`
agrees with `algebraMap ℂ D`. This compares the formulations only; it proves
neither of them. -/
theorem amitsurDivisionAlgebraStatement_iff_equivStatement (D : Type u) [DivisionRing D]
    [Algebra ℂ D] :
    AmitsurDivisionAlgebraStatement D ↔ AmitsurDivisionAlgebraEquivStatement D := by
  constructor
  · intro h hr
    exact ⟨AlgEquiv.ofBijective (Algebra.ofId ℂ D) (h hr), fun z => rfl⟩
  · intro h hr
    obtain ⟨e, he⟩ := h hr
    have : ⇑(algebraMap ℂ D) = ⇑e := funext fun z => (he z).symm
    rw [this]
    exact e.bijective

/-- Renard B.I, Théorème, for all carriers in universe `u`: assertion b) for
every nontrivial unital complex algebra and assertion a) for every complex
division algebra, each under the hypothesis of at most countable dimension. -/
@[pp_with_univ]
def AmitsurTheoremStatement : Prop :=
  (∀ (A : Type u) [Ring A] [Algebra ℂ A] [Nontrivial A],
      AmitsurSpectrumNonemptyStatement.{u} A ∧ AmitsurSpectrumSingletonZeroStatement.{u} A) ∧
    ∀ (D : Type u) [DivisionRing D] [Algebra ℂ D], AmitsurDivisionAlgebraStatement.{u} D

end Langlands.Renard
