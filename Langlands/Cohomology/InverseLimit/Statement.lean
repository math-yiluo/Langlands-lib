import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.CofilteredSystem

/-!
Proposition targets for the algebraic inverse-limit comparison used in
Harris 1999, Section 2. These are statements, not proofs.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe u v

/-- EGA III.0, Proposition 13.2.1: Mittag-Leffler passes to quotients and
is preserved by extensions of towers of modules. -/
def MittagLefflerExactSequenceStatement (R : Type u) [Ring R] : Prop :=
  ∀ (S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v} R)), S.ShortExact →
    (((S.X₂ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler →
      (S.X₃ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler) ∧
    ((S.X₁ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler →
      (S.X₃ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler →
      (S.X₂ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler))

/-- EGA III.0, Proposition 13.2.2 for natural-number towers: an exact
sequence stays exact under inverse limit when its kernel tower is ML. -/
def MittagLefflerShortExactLimitStatement (R : Type u) [Ring R] : Prop :=
  ∀ (S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v} R)), S.ShortExact →
    (S.X₁ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler →
    (S.map (lim : (ℕᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).ShortExact

/-- EGA III.0, Proposition 13.2.3 for a natural-number tower of module
complexes: degreewise Mittag-Leffler gives surjectivity; Mittag-Leffler in
cohomological degree `q - 1` gives invertibility in degree `q`. -/
def DegreewiseInverseLimitCohomologyStatement (R : Type u) [Ring R] : Prop :=
  ∀ (K : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ),
    (∀ q : ℤ,
      (K ⋙ HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) q ⋙
        forget (ModuleCat.{v} R)).IsMittagLeffler) →
    ∀ q : ℤ,
      Function.Surjective (limit.post K
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q)) ∧
      ((K ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ)
          (q - 1) ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler →
        IsIso (limit.post K
          (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q)))

/-- Countable inverse limits commute with cohomology when the degreewise
module systems and cohomology systems satisfy the Mittag-Leffler condition.
The conclusion concerns the canonical map induced by the limit projections.
No invertibility of this map is used to construct it. -/
def InverseLimitCohomologyStatement (R : Type u) [Ring R] : Prop :=
  ∀ (K : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ),
    (∀ q : ℤ,
      (K ⋙ HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) q ⋙
        forget (ModuleCat.{v} R)).IsMittagLeffler) →
    (∀ q : ℤ,
      (K ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q ⋙
        forget (ModuleCat.{v} R)).IsMittagLeffler) →
    ∀ q : ℤ,
      IsIso (limit.post K
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q))

/-- The finite-cohomology, surjective-transition sufficient conditions used
in Harris's passage from torsion coefficient complexes to their inverse limit.
This is the algebraic comparison, without a geometric specialization. -/
def FiniteCohomologyInverseLimitStatement (R : Type u) [Ring R] : Prop :=
  ∀ (K : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ),
    (∀ (i j : ℕᵒᵖ) (f : i ⟶ j) (q : ℤ),
      Function.Surjective ((K.map f).f q)) →
    (∀ (i : ℕᵒᵖ) (q : ℤ), Finite ((K.obj i).homology q)) →
    ∀ q : ℤ,
      IsIso (limit.post K
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q))

/-- The two exactness prerequisites, the degreewise EGA comparison and its
two stated specializations.
This conjunction supplies one coherent statement target; it assumes none of
its constituent propositions. -/
def InverseLimitComparisonStatements (R : Type u) [Ring R] : Prop :=
  MittagLefflerExactSequenceStatement.{u, v} R ∧
  MittagLefflerShortExactLimitStatement.{u, v} R ∧
  DegreewiseInverseLimitCohomologyStatement.{u, v} R ∧
  InverseLimitCohomologyStatement.{u, v} R ∧
  FiniteCohomologyInverseLimitStatement.{u, v} R

end Langlands.Cohomology
