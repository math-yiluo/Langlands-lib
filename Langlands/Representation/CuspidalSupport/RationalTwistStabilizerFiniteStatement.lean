import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.GroupScheme.Reductive.Basic

/-! # Finite unramified twist stabilizers (Renard V.2.7, Lemma)

For an irreducible smooth representation `π` of the rational points of a connected reductive
group over a nonarchimedean local field, the stabilizer `X(G)(π) = {ω ∈ X(G) | π ⊗ ω ≃ π}` of
`π` in the group of unramified characters is finite.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard V.2.7, Lemma: for every connected reductive `G` over a nonarchimedean local field
`F` and every irreducible smooth representation `π` of `G(F)`, the set of unramified
characters `ω` of `G(F)` with `π ⊗ ω ≅ π` is finite. -/
def RationalTwistStabilizerFiniteStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G), A.IsIrreducible →
      {χ : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) |
        Nonempty (rationalUnramifiedTwist G χ A ≅ A)}.Finite

end Langlands.CuspidalSupport
