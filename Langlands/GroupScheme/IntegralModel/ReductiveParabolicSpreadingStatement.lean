import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Absolute.Borel
import Langlands.Global.Adelic
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.Localization.AsSubring

/-! # Simultaneous good reductive and parabolic spreading -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Global

namespace Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading

/-- Actual simultaneous integral models of a supplied homomorphism, with reductive
ambient model, smooth closed subgroup model, and the specified good field fibres. -/
structure ModelData (R F : Type u) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]
    {G P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G) where
  ambient : IntegralModel R F G
  parabolic : IntegralModel R F P
  inclusion : parabolic.Hom ambient p
  closedImmersion : IsClosedImmersion inclusion.hom.hom.hom.left
  reductive : IsReductive ambient.group
  parabolicSmooth : Smooth parabolic.group.X.hom
  fieldReductive : ∀ (k : Type u) [Field k] [Algebra R k],
    IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj ambient.group)
  fieldParabolic : ∀ (k : Type u) [Field k] [Algebra R k],
    IsParabolicSubgroup ((baseChange (Spec.algebraMap R k)).map inclusion.hom)
  fieldConnected : ∀ (k : Type u) [Field k] [Algebra R k],
    ConnectedSpace (((baseChange (Spec.algebraMap R k)).obj parabolic.group).X.left)

/-- A number-field connected reductive group and any supplied parabolic inclusion
admit simultaneous good models over one actual finite S-integer ring. -/
def ExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G),
      IsParabolicSubgroup p →
      ∃ S : Finset (FinitePlace F),
        Nonempty (ModelData ((S : Set (FinitePlace F)).integer F) F p)

end Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading
