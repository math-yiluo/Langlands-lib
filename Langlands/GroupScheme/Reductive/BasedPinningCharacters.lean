import Langlands.GroupScheme.Reductive.BasedBorelTransport
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Actual simple-character data from a based coordinate isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.BasedCoordinateIso

variable {S : Scheme.{u}} {I I' J J' : Type u}
  [Fintype I] [Fintype I']
  {G H : GroupScheme S}
  {i : splitTorus S I ⟶ G} {j : splitTorus S I' ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {b : P.Base} {c : Q.Base}
  (d : BasedCoordinateIso i j P Q b c)

/-- The prescribed actual torus isomorphism in commutative-group notation. -/
def commTorusIso :
    splitTorus.commGroupScheme S I ≅ splitTorus.commGroupScheme S I' :=
  CommGroupScheme.isoOfGroupIso d.torusIso

/-- Changing notation retains the exact specified torus inclusion square. -/
theorem commTorusIso_square :
    i ≫ d.groupIso.hom = CommGroupScheme.groupHom d.commTorusIso.hom ≫ j :=
  d.square

/-- The all-test character formula identifies actual fixed-exponent
characters, not merely their values on a selected coefficient ring. -/
theorem exponentCharacter_pullback (m : I' → ℤ) :
    d.commTorusIso.hom ≫ splitTorus.exponentCharacter S I' m =
      splitTorus.exponentCharacter S I (d.rootEquiv.weightMap m) := by
  apply characterLattice.ext_points
  intro U x
  rw [comp_groupHom_comp, splitTorus.pointsEquiv_exponentCharacter,
    splitTorus.pointsEquiv_exponentCharacter]
  exact d.characters U x m

/-- The based root equivalence restricts to the actual simple supports,
oriented from the source pinning to the target pinning. -/
def simpleEquiv : b.support ≃ c.support :=
  (d.rootEquiv.indexEquiv.subtypeEquiv d.simple_iff).symm

/-- The simple-support correspondence is the inverse root-index map. -/
@[simp] theorem indexEquiv_simpleEquiv (s : b.support) :
    d.rootEquiv.indexEquiv (d.simpleEquiv s) = s := by
  change d.rootEquiv.indexEquiv (d.rootEquiv.indexEquiv.symm s.val) = s.val
  exact d.rootEquiv.indexEquiv.apply_symm_apply s.val

/-- The entire weight map carries each relabelled target simple root to
its prescribed source simple root. -/
theorem simpleRoot_weightMap (s : b.support) :
    d.rootEquiv.weightMap (Q.root (d.simpleEquiv s)) = P.root s := by
  simpa only [Function.comp_apply, indexEquiv_simpleEquiv] using
    congr_fun d.rootEquiv.root_weightMap (d.simpleEquiv s)

/-- The actual torus isomorphism carries the original source simple
characters to the relabelled target simple characters. -/
theorem simpleCharacter_congr (s : b.support) :
    characterLattice.congr d.commTorusIso
        (splitTorus.exponentCharacter S I (P.root s)) =
      splitTorus.exponentCharacter S I' (Q.root (d.simpleEquiv s)) := by
  rw [characterLattice.congr_apply]
  apply (cancel_epi d.commTorusIso.hom).mp
  rw [Iso.hom_inv_id_assoc, d.exponentCharacter_pullback, d.simpleRoot_weightMap]

end Langlands.GroupScheme.BasedCoordinateIso
