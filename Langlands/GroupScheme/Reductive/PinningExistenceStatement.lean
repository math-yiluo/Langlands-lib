import Langlands.GroupScheme.Reductive.Pinning

/-! # Statements: existence of field pinnings -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Any base of a realized root datum for a split maximal torus in a connected
reductive group admits actual simple-root Lie trivializations. -/
def RootPinningExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∀ (J : Type u)
        (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P → ∀ b : P.Base, Nonempty (RootPinning i P b)

/-- A connected reductive field group with a split maximal torus admits a
pinning, including its actual finite reduced root datum and a base. -/
def SplitPinningExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      Nonempty (SplitPinning G)

end Langlands.GroupScheme
