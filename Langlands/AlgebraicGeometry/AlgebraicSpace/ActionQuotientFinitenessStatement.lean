import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Quasi-separatedness and finite presentation of action quotients over a field

Over a field `k`, let a quasi-compact group scheme `G` act on a scheme `Z` of finite type,
and let `X` be an algebraic space locally of finite type over `k` with an fppf quotient
map `π : Z → X` of the action that is smooth and surjective. Then `X` is quasi-separated
and of finite presentation over `k`. This supplies the finiteness of Conrad's quotient
`V_d/G` in Example 5.5, which he reads with his standing quasi-separatedness convention.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Quasi-separatedness and finite presentation of action quotients over a field: let
`G` be a group scheme quasi-compact over a field `k`, acting by `b` on a scheme `Z`
locally of finite type and quasi-compact over `k`. Let `X` be an algebraic space locally
of finite type over `k` and `π : Z ⟶ X` an fppf quotient map of the action that is
smooth and surjective. Then `X` is quasi-separated and of finite presentation over
`k`. -/
def ActionQuotientFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (Z : Over (Spec (CommRingCat.of k))) (b : SchemeAction G Z),
    QuasiCompact G.X.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      (π : (schemeSheaf _).obj Z ⟶ X.toSheaf),
      IsFppfActionQuotient b π → IsSmooth π.hom → IsSurjective π.hom →
        LocallyOfFiniteTypeOverBase X →
          IsQuasiSeparated X ∧ FinitePresentationOverRing k X

end Langlands.AlgebraicGeometry.AlgebraicSpace
