import Langlands.GroupScheme.Symplectic.StructureStatement
import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties

/-! # Descent from an actual standard symplectic model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Symplectic

variable {K : Type u} [Field K]

/-- An actual standard symplectic model after an algebraic extension of fields.
This structure supplies data; it asserts no existence for a given group. -/
structure AlgebraicModel
    (G : GroupScheme (Spec (CommRingCat.of K))) (n : ℕ) where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra K extension]
  isAlgebraic : Algebra.IsAlgebraic K extension
  iso : (GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap K extension)))).obj G ≅
      groupScheme extension n

namespace AlgebraicModel

attribute [instance] field algebra

variable {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (M : AlgebraicModel G n)

include M

/-- Simple connectedness descends from the supplied model once the standard
symplectic structural proposition is proved. -/
theorem isSimplyConnected (hstd : StructureStatement.{u}) (hn : 2 ≤ n) :
    IsSimplyConnected G := by
  let := M.isAlgebraic
  apply IsSimplyConnected.of_algebraicExtension (K := M.extension)
  exact (hstd M.extension n hn).1.of_iso M.iso

/-- Absolute almost-simplicity descends from the supplied actual model. -/
theorem isAbsolutelyAlmostSimple (hstd : StructureStatement.{u}) (hn : 2 ≤ n) :
    IsAbsolutelyAlmostSimple G := by
  apply IsAbsolutelyAlmostSimple.of_fieldExtension (K := M.extension)
  exact (hstd M.extension n hn).2.of_iso M.iso

/-- The connected reductivity needed by elementary-subgroup arguments is already
a consequence of the supplied model and the standard structural proposition. -/
theorem isConnectedReductive (hstd : StructureStatement.{u}) (hn : 2 ≤ n) :
    IsConnectedReductive G :=
  (M.isSimplyConnected hstd hn).isSemisimple.isConnectedReductive

/-- The two structural conclusions of the local rank-one target, separated from
the rational split-rank calculation. -/
theorem isSimplyConnected_and_isAlmostSimple
    (hstd : StructureStatement.{u}) (hn : 2 ≤ n) :
    IsSimplyConnected G ∧ IsAlmostSimple G :=
  ⟨M.isSimplyConnected hstd hn, (M.isAbsolutelyAlmostSimple hstd hn).1⟩

end AlgebraicModel

end Langlands.GroupScheme.Symplectic
