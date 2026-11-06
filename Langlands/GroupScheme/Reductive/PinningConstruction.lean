import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.LinearAlgebra.RootDatumBaseExists

/-! # Constructing actual pinnings from root lines and realized root data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {J : Type u}

namespace RootPinning

/-- Choose trivializations of the simple-root spaces from line witnesses for
the actual root spaces. The supplied root datum and base are retained. -/
def ofRootLines (i : T.toGrp ⟶ G)
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (b : P.Base)
    (hlines : ∀ χ ∈ roots i, Nonempty (k ≃ₗ[k] weightSpace i χ)) :
    RootPinning i P b where
  trivialization a := Classical.choice (hlines (P.root a) (by
    rw [← hP.2.1]
    exact ⟨a, rfl⟩))

end RootPinning

namespace SplitPinning

/-- Assemble a pinning on the given actual torus, choosing a base by the
published finite reduced integral-root-datum theorem. -/
def ofRootDatum (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) [Finite J]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (hred : P.IsReduced)
    (hlines : ∀ χ ∈ roots i, Nonempty (k ≃ₗ[k] weightSpace i χ)) :
    SplitPinning G := by
  letI : P.IsReduced := hred
  let b := Langlands.LinearAlgebra.RootDatumBase.base P
  exact
    { isConnectedReductive := hG
      torus := T
      inclusion := i
      isSplitTorus := hT
      isMaximalTorus := hi
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := b
      pinning := RootPinning.ofRootLines i P hP b hlines }

/-- The global root-datum existence proposition, together with actual local
root-line witnesses, suffices to construct the whole pinning bundle. -/
def ofRootDatumExistence (hroot : RootDatumExistenceStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hlines : ∀ χ ∈ roots i, Nonempty (k ≃ₗ[k] weightSpace i χ)) :
    SplitPinning G :=
  Classical.choice <| by
    obtain ⟨J, hJ, P, hP, hred⟩ := hroot k G hG T hT i hi
    let : Finite J := hJ
    exact ⟨ofRootDatum hG hT i hi P hP hred hlines⟩

end SplitPinning

end Langlands.GroupScheme
