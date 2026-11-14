import Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement
import Langlands.AllField.Representation.Geometric.WeylStatementSupplement
import Langlands.AllField.Representation.Induction.Parabolic
import Langlands.AllField.Representation.Parabolic.ComposedFunctors
/-! Normalization and actual induced functions under ordered refinement coordinates. -/

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding RefinementCoordinatesNormalizationTheorem
open Langlands.AllField.Parabolic

open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

universe uF uV

namespace RefinementCoordinatesNormalization
open Langlands.Parabolic.RefinementCoordinatesNormalization hiding HalfModulusClause InductionClause ModulusClause
open Langlands.AllField.Parabolic.RefinementCoordinatesNormalization
open Langlands.Parabolic hiding RefinementCoordinatesNormalizationTheorem
open Langlands.AllField.Parabolic

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
  (hs : ∀ a, (S a.1).size a.2 = B.size (e a))

/-- The full positive modulus agrees after the concrete Levi coordinate map. -/
def ModulusClause : Prop :=
  ∀ m : B.Levi F,
    T.composedLeviModulus D S (B.leviRefinementEquiv D S e hs F m) =
      T.leviModulus B m

/-- Both the Levi positive half and its parabolic inflation agree under the
published coordinate maps. These are equalities of the canonical halves. -/
def HalfModulusClause
    (hc : ∀ i k x, D.index i ((S i).index k x) =
      B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x)) : Prop :=
  (∀ m : B.Levi F,
    T.composedLeviHalfModulus D S (B.leviRefinementEquiv D S e hs F m) =
      T.leviHalfModulus B m) ∧
  (∀ q : B.parabolic F,
    T.composedParabolicHalfModulus D S
        (B.parabolicRefinementEquiv D S e hs F hc q) =
      T.parabolicHalfModulus B q)

/-- An actual equivariant linear equivalence of the two smooth induced spaces,
retaining the underlying ambient function in both directions. -/
def InductionClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F) V),
    let σL := σ.comp (B.leviRefinementEquiv D S e hs F).symm.toMonoidHom
    ∃ E : Representation.Equiv
        (T.normalizedComposedInduced D S σL)
        (T.normalizedParabolicInduced B σ),
      (∀ f (g : GeneralLinear n F),
        Induction.eval _ _ (E f) g = Induction.eval _ _ f g) ∧
      (∀ f (g : GeneralLinear n F),
        Induction.eval _ _ (E.symm f) g = Induction.eval _ _ f g)

end RefinementCoordinatesNormalization

/-- Full modulus, canonical positive halves and actual induced-function comparison
for every ordered refinement satisfying the exact coordinate identity. -/
def RefinementCoordinatesNormalizationTheorem : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ) (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
    (hs : ∀ a, (S a.1).size a.2 = B.size (e a))
    (hc : ∀ i k x, D.index i ((S i).index k x) =
      B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x)),
    Langlands.AllField.Parabolic.RefinementCoordinatesNormalization.ModulusClause F T B D S e hs ∧
    Langlands.AllField.Parabolic.RefinementCoordinatesNormalization.HalfModulusClause F T B D S e hs hc ∧
    Langlands.AllField.Parabolic.RefinementCoordinatesNormalization.InductionClause.{uF, uV} F T B D S e hs

end Langlands.AllField.Parabolic
