import Langlands.AllFieldBZ.Representation.Geometric.WeylStatement
import Langlands.AllFieldBZ.Representation.Geometric.WeylUniquenessProof
import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.AllFieldBZ.Representation.Parabolic.ComposedFunctors
import Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement

/-!
# All-field port of `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding RefinementCoordinatesNormalizationTheorem
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe uF uV

namespace RefinementCoordinatesNormalization
open Langlands.Parabolic.RefinementCoordinatesNormalization hiding HalfModulusClause InductionClause ModulusClause
variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
  (hs : ∀ a, (S a.1).size a.2 = B.size (e a))

/-- The full positive modulus agrees after the concrete Levi coordinate map. -/
def ModulusClause : Prop :=
  ∀ m : B.Levi F.Carrier,
    T.composedLeviModulus D S (B.leviRefinementEquiv D S e hs F.Carrier m) =
      T.leviModulus B m

/-- Both the Levi positive half and its parabolic inflation agree under the
published coordinate maps. These are equalities of the canonical halves. -/
def HalfModulusClause
    (hc : ∀ i k x, D.index i ((S i).index k x) =
      B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x)) : Prop :=
  (∀ m : B.Levi F.Carrier,
    T.composedLeviHalfModulus D S (B.leviRefinementEquiv D S e hs F.Carrier m) =
      T.leviHalfModulus B m) ∧
  (∀ q : B.parabolic F.Carrier,
    T.composedParabolicHalfModulus D S
        (B.parabolicRefinementEquiv D S e hs F.Carrier hc q) =
      T.parabolicHalfModulus B q)

/-- An actual equivariant linear equivalence of the two smooth induced spaces,
retaining the underlying ambient function in both directions. -/
def InductionClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F.Carrier) V),
    let σL := σ.comp (B.leviRefinementEquiv D S e hs F.Carrier).symm.toMonoidHom
    ∃ E : Representation.Equiv
        (T.normalizedComposedInduced D S σL)
        (T.normalizedParabolicInduced B σ),
      (∀ f (g : GeneralLinear n F.Carrier),
        Induction.eval _ _ (E f) g = Induction.eval _ _ f g) ∧
      (∀ f (g : GeneralLinear n F.Carrier),
        Induction.eval _ _ (E.symm f) g = Induction.eval _ _ f g)

end RefinementCoordinatesNormalization
/-- Full modulus, canonical positive halves and actual induced-function comparison
for every ordered refinement satisfying the exact coordinate identity. -/
def RefinementCoordinatesNormalizationTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    (n : ℕ) (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
    (hs : ∀ a, (S a.1).size a.2 = B.size (e a))
    (hc : ∀ i k x, D.index i ((S i).index k x) =
      B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x)),
    RefinementCoordinatesNormalization.ModulusClause F T B D S e hs ∧
    RefinementCoordinatesNormalization.HalfModulusClause F T B D S e hs hc ∧
    RefinementCoordinatesNormalization.InductionClause.{uF, uV} F T B D S e hs

end Langlands.AllFieldBZ.Parabolic
