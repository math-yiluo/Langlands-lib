import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.HenselianContainingSubgroup
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.RelativeHenselianSplitting
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Residue-maximal relative tori containing a supplied split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.HenselianTorusLifting

variable {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]
  {H : CommGroupScheme (Spec (CommRingCat.of R))}
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- An actual commutative relative torus containing the prescribed integral
source, whose residue inclusion is a maximal torus. -/
structure ContainingMaximalData (s : H.toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of R))
  relativeTorus : RelativeTorus.IsTorus torus.toGrp
  inclusion : torus.toGrp ⟶ G
  closed : IsClosedSubgroup inclusion
  subtorusHom : H.toGrp ⟶ torus.toGrp
  subtorusClosed : IsClosedSubgroup subtorusHom
  contains : subtorusHom ≫ inclusion = s
  residueMaximal : IsMaximalTorus
    (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj torus)
    ((baseChange (Spec.algebraMap R k)).map inclusion)

/-- Choose a residue maximal torus containing the split source and lift that
containment, retaining the actual integral source. -/
theorem nonempty_containingMaximalData
    (hk : Function.Surjective (algebraMap R k))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : H.toGrp ⟶ G) (hH : IsSplitTorus H.toGrp)
    (hs : IsClosedSubgroup s) :
    Nonempty (ContainingMaximalData (k := k) s) := by
  let b := Spec.algebraMap R k
  obtain ⟨T₀, i₀, hmax, j₀, hji⟩ :=
    exists_maximalTorus_extension_of_finiteType ((baseChange b).obj G)
      (T := (CommGroupScheme.baseChange b).obj H)
      ((baseChange b).map s) ((hH.baseChange b).isTorus) (hs.baseChange b)
  have hj₀ : IsClosedSubgroup j₀ :=
    IsClosedSubgroup.of_comp hmax.2.1 (hji ▸ hs.baseChange b)
  let L := containingLiftData hk s hH i₀ hmax.2.1 hmax.1.relativeTorus j₀ hj₀ hji
  refine ⟨{
    torus := L.relativeTorus.commGroupScheme
    relativeTorus := L.relativeTorus
    inclusion := L.inclusion
    closed := L.closed
    subtorusHom := L.subtorusHom
    subtorusClosed := L.subtorusClosed
    contains := L.contains
    residueMaximal := ?_ }⟩
  change IsMaximalTorus
    (T := (CommGroupScheme.baseChange b).obj L.relativeTorus.commGroupScheme)
    ((baseChange b).map L.inclusion)
  rw [L.residue_comm]
  exact IsMaximalTorus.iso_comp
    (T' := (CommGroupScheme.baseChange b).obj L.relativeTorus.commGroupScheme)
    L.residueIso hmax

/-- A chosen containing relative torus with maximal residue fibre. -/
def containingMaximalData
    (hk : Function.Surjective (algebraMap R k))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : H.toGrp ⟶ G) (hH : IsSplitTorus H.toGrp)
    (hs : IsClosedSubgroup s) :
    ContainingMaximalData (k := k) s :=
  Classical.choice (nonempty_containingMaximalData hk s hH hs)

end Langlands.GroupScheme.HenselianTorusLifting
