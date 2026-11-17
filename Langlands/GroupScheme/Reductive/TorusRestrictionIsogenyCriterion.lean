import Langlands.GroupScheme.Reductive.FiniteKernelOfTorusRestriction
import Langlands.GroupScheme.SmoothConnectedFiniteKernel
import Langlands.GroupScheme.FiniteHomDimension
import Langlands.GroupScheme.Reductive.IsogenyRootIndex

/-! # Isogenies from finite torus restrictions and equal root counts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A compatible finite restriction to a maximal torus and equality of actual
Lie dimensions make a homomorphism of connected reductive field groups an
isogeny. -/
theorem isIsogeny_of_finite_torus_restriction_of_finrank_eq
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (q : G ⟶ H)
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H) (t : T ⟶ T')
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    (hit : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (hdim : letI := hG.isAffineHom
      letI := hH.isAffineHom
      Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel H k))) : IsIsogeny q := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : ConnectedSpace H.X.left := hH.connectedSpace
  let : IsFinite (kernel q).X.hom :=
    kernel_isFinite_of_finite_torus_restriction hG q i i' t hi hi' hit
  let : IsFinite q.hom.hom.left := isFinite_hom_of_finite_kernel q
  exact isIsogeny_of_isFinite_of_finrank_eq q hdim

/-- The actual schematic image is the whole target under the finite
maximal-torus restriction and equal-dimension hypotheses. Its forward map
is the canonical schematic-image inclusion. -/
def imageIsoOfFiniteTorusRestrictionFinrankEq
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (q : G ⟶ H)
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H) (t : T ⟶ T')
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    (hit : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (hdim : Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel H k))) :
    SchematicImage.image q ≅ H := by
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : ConnectedSpace H.X.left := hH.connectedSpace
  let : IsFinite q.hom.hom.left :=
    (isIsogeny_of_finite_torus_restriction_of_finrank_eq
      hG hH q i i' t hi hi' hit hdim).1
  exact imageIsoOfFiniteFinrankEq q hdim

@[simp] theorem imageIsoOfFiniteTorusRestrictionFinrankEq_hom
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (q : G ⟶ H)
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H) (t : T ⟶ T')
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    (hit : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (hdim : Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel H k))) :
    (imageIsoOfFiniteTorusRestrictionFinrankEq
      hG hH q i i' t hi hi' hit hdim).hom = SchematicImage.inclusion q := rfl

/-- A homomorphism of split connected reductive field groups is an isogeny if
it restricts to an isogeny of the specified maximal tori and the supplied
actual root data have equally many roots. -/
theorem isIsogeny_of_torus_restriction_of_root_card_eq
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (q : G ⟶ H)
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H) (t : T ⟶ T')
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hit : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    {J J' : Type u} [Finite J] [Finite J']
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    (hP : letI := hG.isAffineHom
      IsRootDatumOf i P)
    (hQ : letI := hH.isAffineHom
      IsRootDatumOf i' Q)
    (hcard : Nat.card J = Nat.card J') : IsIsogeny q := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : IsAffineHom T'.toGrp.X.hom := hT'.isAffineHom
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : Smooth T'.toGrp.X.hom := hT'.smooth
  let : IsFinite (CommGroupScheme.groupHom t).hom.hom.left := ht.1
  apply isIsogeny_of_finite_torus_restriction_of_finrank_eq
    hG hH q i i' t hi hi'.2.1 hit
  rw [hP.finrank_lie_eq_torus_add_card hG hT hi,
    hQ.finrank_lie_eq_torus_add_card hH hT' hi',
    Lie.finrank_kernel_eq_of_isogeny (CommGroupScheme.groupHom t) ht, hcard]

end Langlands.GroupScheme
