import Langlands.Cohomology.SiteCech.EquivariantCochainDescent
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Assembling exact equivariant three-term models -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits

universe u v uE vE

variable {D : Type u} [Category.{v} D] [Abelian D]
variable {E : Type uE} [Category.{vE} E] [Abelian E]
variable (V : E ⥤ D) [V.Faithful] [V.PreservesZeroMorphisms]

/-- Three lifted objects and arrows, compared to an ordinary short complex
by isomorphisms and both differential squares. The zero composite and
exactness will be reflected from the ordinary complex. -/
structure EquivariantThreeTermModel (T : ShortComplex D) where
  upper : E
  middle : E
  lower : E
  f : upper ⟶ middle
  g : middle ⟶ lower
  upperIso : V.obj upper ≅ T.X₁
  middleIso : V.obj middle ≅ T.X₂
  lowerIso : V.obj lower ≅ T.X₃
  upper_square : V.map f ≫ middleIso.hom = upperIso.hom ≫ T.f
  lower_square : V.map g ≫ lowerIso.hom = middleIso.hom ≫ T.g

variable {V} {T : ShortComplex D}

/-- Faithfulness reflects the zero composite through the two squares. -/
theorem EquivariantThreeTermModel.zero (M : EquivariantThreeTermModel V T) :
    M.f ≫ M.g = 0 := by
  apply V.map_injective
  apply (cancel_mono M.lowerIso.hom).1
  rw [Functor.map_comp, Category.assoc, M.lower_square, ← Category.assoc,
    M.upper_square, Category.assoc, T.zero, comp_zero, Functor.map_zero, zero_comp]

/-- The actual short complex on the lifted arrows. -/
def EquivariantThreeTermModel.complex (M : EquivariantThreeTermModel V T) :
    ShortComplex E :=
  ShortComplex.mk M.f M.g M.zero

/-- The specified term comparisons identify the restriction of the lifted
short complex with the original ordinary short complex. -/
def EquivariantThreeTermModel.restrictionIso (M : EquivariantThreeTermModel V T) :
    M.complex.map V ≅ T :=
  ShortComplex.isoMk M.upperIso M.middleIso M.lowerIso
    M.upper_square.symm M.lower_square.symm

/-- An exact faithful restriction reflects ordinary exactness of the model. -/
theorem EquivariantThreeTermModel.exact [V.PreservesHomology]
    (M : EquivariantThreeTermModel V T) (hT : T.Exact) : M.complex.Exact := by
  apply (M.complex.exact_map_iff_of_faithful V).1
  exact ShortComplex.exact_of_iso M.restrictionIso.symm hT

/-- An exact ordinary chain segment and a lifted middle cochain produce the
exact equivariant cochain model consumed by primitive descent. -/
def EquivariantThreeTermModel.cochainLift [V.PreservesHomology]
    (P : ChainComplex D ℕ) (n : ℕ)
    (M : EquivariantThreeTermModel V (P.sc' (n + 2) (n + 1) n))
    (hP : P.ExactAt (n + 1)) (I : E) (F : D) (e : V.obj I ≅ F)
    (x : P.X (n + 1) ⟶ F) (lift : M.middle ⟶ I)
    (lift_eq : V.map lift ≫ e.hom = M.middleIso.hom ≫ x) :
    EquivariantCochainLift V P I F e n x where
  complex := M.complex
  exact := M.exact ((HomologicalComplex.exactAt_iff' P (n + 2) (n + 1) n
    (by simp) (by simp)).1 hP)
  lowerIso := M.lowerIso
  middleIso := M.middleIso
  upperMap := M.upperIso.hom
  upper_square := M.upper_square
  lower_square := M.lower_square
  lift := lift
  lift_eq := lift_eq

end Langlands.Cohomology.SiteCech
