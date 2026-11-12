import Langlands.AbelianScheme.FieldAmpleExistenceStatement
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof
import Langlands.AbelianScheme.GroupScheme
import Langlands.AlgebraicGeometry.Picard.AlgebraicExtensionAmpleExistenceSpreadingProof
import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! # Ample line-bundle existence over an arbitrary field

Base change to an algebraic closure, use ample existence there, spread to a
finite intermediate field, and descend ample existence by the finite norm.
-/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

/-- Every commutative smooth proper geometrically connected group scheme over
an arbitrary field admits an actual ample line bundle. -/
theorem fieldAmpleExistence : FieldAmpleExistenceStatement.{u} := by
  have hclosed : AlgebraicallyClosedFieldAmpleExistenceStatement.{u} :=
    @algebraicallyClosedFieldAmpleExistence.{u}
  have hspread : AlgebraicExtensionAmpleExistenceSpreadingStatement.{u} :=
    @algebraicExtensionAmpleExistenceSpreading.{u}
  have hdescent : FiniteFieldExtensionAmpleExistenceDescentStatement.{u} :=
    @finiteFieldExtensionAmpleExistenceDescent.{u}
  intro K _ G _ hs hp hc
  let : Smooth G.X.hom := hs
  let : IsProper G.X.hom := hp
  let : GeometricallyConnected G.X.hom := hc
  let Ω := AlgebraicClosure K
  let b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let GΩ : Grp (Over (Spec (CommRingCat.of Ω))) := (baseChange b).obj G
  let : IsCommMonObj GΩ.X :=
    Functor.isCommMonObj_obj (F := Over.pullback b) (M := G.X)
  have hsΩ : Smooth GΩ.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have hpΩ : IsProper GΩ.X.hom := by
    change IsProper (pullback.snd G.X.hom b)
    infer_instance
  have hcΩ : GeometricallyConnected GΩ.X.hom := by
    change GeometricallyConnected (pullback.snd G.X.hom b)
    infer_instance
  have hΩ : ∃ M : LineBundle (pullback G.X.hom b), M.IsAmple :=
    hclosed Ω GΩ hsΩ hpΩ hcΩ
  obtain ⟨E, hE, hM⟩ := hspread K Ω G.X.left G.X.hom hp hΩ
  let : FiniteDimensional K E := hE
  exact hdescent K E G.X.left G.X.hom hM

end Langlands.GroupScheme
