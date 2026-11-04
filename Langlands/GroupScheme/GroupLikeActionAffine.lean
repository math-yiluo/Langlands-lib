import Langlands.GroupScheme.GroupLikeActionIntegral
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Rigidity of actions on affine groups with group-like coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

section Transport

variable {S : Scheme.{u}} {H G K : GroupScheme S} (a : AutomorphicAction H G)

/-- Transport the target of an actual automorphic action through a group-scheme
isomorphism, keeping its action morphism over the same base. -/
def transportTarget (e : K ≅ G) : AutomorphicAction H K where
  hom := (H.X ◁ e.hom.hom.hom) ≫ a.hom ≫ e.inv.hom.hom
  one_left g := by
    simpa only [act, Category.assoc, lift_whiskerLeft_assoc, ← Grp.comp_hom_hom,
      e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using
      congrArg (fun z => z ≫ e.inv.hom.hom) (a.act_one_left (g ≫ e.hom.hom.hom))
  mul_left h h' g := by
    simpa only [act, Category.assoc, lift_whiskerLeft_assoc, ← Grp.comp_hom_hom,
      e.inv_hom_id, Grp.id_hom_hom, Category.comp_id] using
      congrArg (fun z => z ≫ e.inv.hom.hom)
        (a.act_mul_left h h' (g ≫ e.hom.hom.hom))
  mul_right h g g' := by
    simpa only [act, Category.assoc, lift_whiskerLeft_assoc, MonObj.mul_comp] using
      congrArg (fun z => z ≫ e.inv.hom.hom)
        (a.act_mul_right h (g ≫ e.hom.hom.hom) (g' ≫ e.hom.hom.hom))

@[simp] theorem transportTarget_act (e : K ≅ G) {T : Over S}
    (h : T ⟶ H.X) (x : T ⟶ K.X) :
    (a.transportTarget e).act h x = a.act h (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom := by
  simp only [act, transportTarget, Category.assoc, lift_whiskerLeft_assoc]

end Transport

variable {k : Type u} [Field k]
    {C : CommHopfAlgCat.{u} (CommRingCat.of k)}
    {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- The Hopf coordinate algebra of an integral affine group is an integral domain. -/
theorem coordinate_isDomain [IsAffine H.X.left] [IsIntegral H.X.left] :
    IsDomain (AffineCoordinates.hopfAlgebra H) := by
  have : IsIso (AffineCoordinates.hopfSpecIso H).inv.hom.hom.left :=
    (Over.forget (Spec (CommRingCat.of k))).map_isIso
      (AffineCoordinates.hopfSpecIso H).inv.hom.hom
  have hi := IsIntegral.of_isIso (AffineCoordinates.hopfSpecIso H).inv.hom.hom.left
  exact (affine_isIntegral_iff (CommRingCat.of (AffineCoordinates.hopfAlgebra H))).mp hi

/-- Any integral affine acting group acts trivially on a Hopf spectrum spanned
by its group-like coordinates, on every scheme test. -/
theorem act_eq_self_of_integral_affine_actor [IsAffine H.X.left] [IsIntegral H.X.left]
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (a : AutomorphicAction H ((hopfSpec (CommRingCat.of k)).obj (op C)))
    {T : Over (Spec (CommRingCat.of k))} (h : T ⟶ H.X)
    (x : T ⟶ ((hopfSpec (CommRingCat.of k)).obj (op C)).X) : a.act h x = x := by
  let e := AffineCoordinates.hopfSpecIso H
  let := coordinate_isDomain (H := H)
  have ht := act_eq_self_of_integral_actor hspan (a.restrict e.hom)
    (h ≫ e.inv.hom.hom) x
  simpa only [restrict_act, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id] using ht

/-- Integral affine actors act trivially on arbitrary affine targets whose
Hopf coordinate algebra is spanned by group-like elements. -/
theorem act_eq_self_of_integral_affine [IsAffine H.X.left] [IsIntegral H.X.left]
    [IsAffine G.X.left]
    (hspan : Submodule.span k
      {c : AffineCoordinates.hopfAlgebra G | IsGroupLikeElem k c} = ⊤)
    (a : AutomorphicAction H G) {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (x : T ⟶ G.X) : a.act h x = x := by
  let e := AffineCoordinates.hopfSpecIso G
  have ht := act_eq_self_of_integral_affine_actor hspan (a.transportTarget e) h
    (x ≫ e.inv.hom.hom)
  have he := congrArg (fun z => z ≫ e.hom.hom.hom) ht
  simpa only [transportTarget_act, Category.assoc, ← Grp.comp_hom_hom,
    e.inv_hom_id, Grp.id_hom_hom, Category.comp_id] using he

/-- Smooth connected affine acting groups act trivially on affine groups with
Hopf coordinate algebra spanned by group-like elements. -/
theorem act_eq_self_of_smooth_connected_affine
    [Smooth H.X.hom] [IsAffine H.X.left] [ConnectedSpace H.X.left]
    [IsAffine G.X.left]
    (hspan : Submodule.span k
      {c : AffineCoordinates.hopfAlgebra G | IsGroupLikeElem k c} = ⊤)
    (a : AutomorphicAction H G) {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (x : T ⟶ G.X) : a.act h x = x := by
  let : GeometricallyIntegral H.X.hom := smoothConnectedAffineGeometry.1 k H
    inferInstance inferInstance inferInstance
  let : IsIntegral H.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton H.X.hom
  exact act_eq_self_of_integral_affine hspan a h x

end Langlands.GroupScheme.AutomorphicAction
