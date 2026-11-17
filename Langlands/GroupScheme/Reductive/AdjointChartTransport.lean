import Langlands.GroupScheme.Reductive.BasedBorelTransport
import Langlands.GroupScheme.Torus.CharacterProjection

/-! # Simple-root projection under supplied based coordinate comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.BasedCoordinateIso

variable {S : Scheme.{u}} {I I' J J' : Type u}
  [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  {G H : GroupScheme S}
  {i : splitTorus S I ⟶ G} {j : splitTorus S I' ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {b : P.Base} {c : Q.Base}
  (d : BasedCoordinateIso i j P Q b c)

/-- The contravariant bijection on the supplied simple-root sets. -/
def simpleRootEquiv : c.support ≃ b.support :=
  Equiv.subtypeEquiv d.rootEquiv.indexEquiv d.simple_iff

omit [Fintype J] [Fintype J'] in
/-- The supplied based comparison acts on the simple-root quotients by this
coordinate permutation, on arbitrary scheme bases and all their tests. -/
theorem simpleRootProjection_comp :
    d.torusIso.hom ≫ splitTorus.characterProjection S
        (fun a : c.support => Q.root a) =
      splitTorus.characterProjection S (fun a : b.support => P.root a) ≫
        (splitTorus.coordinatePermutationIso S d.simpleRootEquiv).hom := by
  apply splitTorus.characterProjection_comp_reindex S
    d.torusIso.hom d.rootEquiv.weightMap d.characters
  intro a
  exact congrFun d.rootEquiv.root_weightMap a

end Langlands.GroupScheme.BasedCoordinateIso
