import Langlands.GroupScheme.ChevalleyIntegral.FieldCellFactor

/-! # Flat intersections with the ambient matrix cell -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A closed cell factorization on a schematically dense cell extends to every
flat scheme mapping to the group and compatibly into the ambient cell. -/
theorem exists_factor_of_flat_cell_intersection
    {B : Scheme.{u}} {H T P A V W : Over B}
    (d : T ⟶ H) [IsSchemeTheoreticallyDominant d.left] [QuasiCompact d.left]
    (i : H ⟶ V) (j : P ⟶ A) [IsClosedImmersion j.left]
    (c : A ⟶ V) [Mono c.left]
    (e : T ⟶ P) (hc : e ≫ j ≫ c = d ≫ i)
    (f : W ⟶ H) [Flat f.left] (g : W ⟶ A) (hg : f ≫ i = g ≫ c) :
    ∃ a : W ⟶ P, a ≫ j = g := by
  let Q : Over B := Over.mk (pullback.snd d.left f.left ≫ W.hom)
  let p : Q ⟶ W := Over.homMk (pullback.snd d.left f.left) rfl
  let q : Q ⟶ T := Over.homMk (pullback.fst d.left f.left) (by
    rw [← d.w, ← Category.assoc, pullback.condition, Category.assoc, f.w]
    rfl)
  have hp : IsSchemeTheoreticallyDominant p.left := by
    change IsSchemeTheoreticallyDominant (pullback.snd d.left f.left)
    infer_instance
  have hpq : p ≫ f = q ≫ d := by
    apply Over.OverMorphism.ext
    exact (pullback.condition (f := d.left) (g := f.left)).symm
  have : Mono c := Over.mono_of_mono_left c
  apply exists_over_factor_of_schematic_precomp j p g (q ≫ e)
  apply (cancel_mono c).mp
  simp only [Category.assoc]
  rw [← hg, ← Category.assoc, hpq, Category.assoc, ← hc]

namespace SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  [Fintype J] [DecidableEq J] (R : CommRingCat.{u})

/-- The full positive and opposite-positive parameter product inside the ambient cell. -/
def fullOrderedCellToAmbient :
    D.orderedCellSpace R D.neg.posList D.posList ⟶ D.ambientCellSpace R :=
  D.orderedCellToAmbient R D.neg.posList D.posList
    (fun _ hj => D.neg.ℓ_root_pos (D.neg.mem_posList.mp hj))
    (fun _ hj => D.ℓ_root_pos (D.mem_posList.mp hj))

instance fullOrderedCellToAmbient_closed :
    IsClosedImmersion (D.fullOrderedCellToAmbient R).left :=
  D.isClosedImmersion_orderedCellToAmbient R D.neg.posList D.posList
    D.neg.posList_nodup D.posList_nodup D.neg.posList_sorted D.posList_sorted _ _

@[simp] theorem fullOrderedCellToAmbient_comp :
    D.fullOrderedCellToAmbient R ≫ D.ambientCellMap R =
      D.orderedCellMap R D.neg.posList D.posList :=
  D.orderedCellToAmbient_comp R D.neg.posList D.posList _ _

private theorem affine_tensor_over_affine {B : Scheme.{u}} [IsAffine B]
    (U V : Over B) [IsAffine U.left] [IsAffine V.left] : IsAffine (U ⊗ V).left := by
  have : IsAffineHom V.hom := inferInstance
  exact IsAffine.of_isPullback (IsPullback.of_hasPullback U.hom V.hom)

namespace ChevGroup

variable {D} {k : Type u} [Field k] (G : D.ChevGroup k)

local instance intersectionChevAffineHom : IsAffineHom G.H.X.hom := G.affine
local instance intersectionChevAffine : IsAffine G.H.X.left := isAffine_of_isAffineHom G.H.X.hom

omit [Fintype J] [DecidableEq J] in
/-- The affine intrinsic triple cell has quasi-compact multiplication. -/
theorem intrinsicCellMap_quasiCompact : QuasiCompact G.intrinsicCellMap.left := by
  have : IsClosedImmersion (Dynamic.Affine.unipotentHom G.neg.cochar).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_unipotentHom G.neg.cochar
  have : IsClosedImmersion (Dynamic.Affine.centralizerHom G.cochar).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_centralizerHom G.cochar
  have : IsClosedImmersion (Dynamic.Affine.unipotentHom G.cochar).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_unipotentHom G.cochar
  have : IsAffine (Dynamic.Affine.unipotentScheme G.neg.cochar).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.unipotentHom G.neg.cochar).hom.hom.left
  have : IsAffine (Dynamic.Affine.centralizerScheme G.cochar).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom G.cochar).hom.hom.left
  have : IsAffine (Dynamic.Affine.unipotentScheme G.cochar).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.unipotentHom G.cochar).hom.hom.left
  have : IsAffine ((Dynamic.Affine.centralizerScheme G.cochar).X ⊗
      (Dynamic.Affine.unipotentScheme G.cochar).X).left :=
    affine_tensor_over_affine _ _
  have : IsAffine G.intrinsicCellSpace.left :=
    affine_tensor_over_affine (Dynamic.Affine.unipotentScheme G.neg.cochar).X
      ((Dynamic.Affine.centralizerScheme G.cochar).X ⊗
        (Dynamic.Affine.unipotentScheme G.cochar).X)
  have : IsAffineHom G.intrinsicCellMap.left := inferInstance
  infer_instance

/-- Every flat intersection with the ambient cell factors through the full
ordered root and full-lattice torus parameter product. -/
theorem exists_orderedCellFactor [P.IsReduced] [Module.Finite ℤ X]
    {W : Over (Spec (CommRingCat.of k))} (f : W ⟶ G.H.X) [Flat f.left]
    (g : W ⟶ D.ambientCellSpace (CommRingCat.of k))
    (hg : f ≫ G.i.hom.hom = g ≫ D.ambientCellMap (CommRingCat.of k)) :
    ∃ a : W ⟶ D.orderedCellSpace (CommRingCat.of k) D.neg.posList D.posList,
      a ≫ D.fullOrderedCellToAmbient (CommRingCat.of k) = g := by
  have := G.intrinsicCellMap_schematic
  have := G.intrinsicCellMap_quasiCompact
  have := D.isOpenImmersion_ambientCellMap (CommRingCat.of k)
  exact exists_factor_of_flat_cell_intersection G.intrinsicCellMap G.i.hom.hom
    (D.fullOrderedCellToAmbient (CommRingCat.of k))
    (D.ambientCellMap (CommRingCat.of k)) G.intrinsicCellToOrdered
    (by rw [fullOrderedCellToAmbient_comp, G.intrinsicCellToOrdered_comp])
    f g hg

end ChevGroup
end SplitExistence.ChevalleyData
end Langlands.GroupScheme
