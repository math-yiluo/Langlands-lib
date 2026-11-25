/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ZetaSeries
import WeilConjectures.AlgebraicGeometry.DensePoints
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Extension of the maximal ideal at a rational point

Source: blueprint proposition-cohomology-smooth-affine-curve, affine-case unit quotient paragraph;
Stacks Algebra, Tag 00E6.
(blueprint: lem-sc-rational-point-base-change-maximal-ideal).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem ker_stalkMap_field (F : Type u) [Field F] {Z : Scheme.{u}}
    (i : Spec (.of F) ⟶ Z) (z : Spec (.of F)) :
    RingHom.ker (i.stalkMap z).hom = IsLocalRing.maximalIdeal (Z.presheaf.stalk (i z)) := by
  have hF : IsField ((Spec (.of F)).presheaf.stalk z) := by
    have hz : z = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    rw [hz]
    exact (stalkClosedPointIso (.of F)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField F)
  have hmax := IsLocalRing.maximalIdeal_comap (i.stalkMap z).hom
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hF] at hmax
  exact hmax

set_option backward.isDefEq.respectTransparency false in
/-- At a rational point, scalar extension extends the maximal ideal of the stalk exactly.
Source: blueprint proposition-cohomology-smooth-affine-curve, affine-case unit quotient paragraph;
Stacks Algebra, Tag 00E6
(blueprint: lem-sc-rational-point-base-change-maximal-ideal).

Proof: let x' be the base-changed rational point. The fibre over x is Spec K,
so y = x'. Pullback pasting shows that the square formed by x, x', the projection,
and Spec K to Spec k is cartesian. Since both rational points are closed immersions,
the ideal sheaf of x' is the pullback of the ideal sheaf of x.
Choose an affine neighbourhood U of the image of x and an affine neighbourhood V
of x' inside the inverse image of U. The formula ideal_comap_appLE says that the
ideal on V is the extension of the ideal on U. For either closed immersion,
ker_stalkMap identifies the kernel on stalks with the extension along the germ
map of its affine defining ideal. The stalk of Spec of a field is the field itself;
a local map to a field has kernel equal to the source maximal ideal. Thus both
stalk kernels are precisely the respective maximal ideals. Extending the source
maximal ideal along the projection's stalk map and using Ideal.map_map gives the
same ideal as extending the target affine ideal along its germ map: the equality
of the composite ring maps is germ_stalkMap followed by germ_res.
No smoothness, dimension, properness, or algebraic closure is needed. -/
theorem Scheme.rational_point_base_change_maximalIdeal
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (s : X ⟶ Spec (.of k)) (x : s.fieldPoints k)
    (y : (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k K))) y =
      x.1.base default) :
    Ideal.map
      ((pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk
        (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k K))) y))) =
      IsLocalRing.maximalIdeal
        ((pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk y) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let X' := pullback s g
  let q : X' ⟶ X := pullback.fst s g
  let x' := s.baseChangeFieldPoint K x
  have heq : x'.1.base default = y := s.baseChangeFieldPoint_eq_of_fst_eq K x hy
  rw [← heq]
  have hx : x.1 ≫ s = 𝟙 _ := by
    rw [x.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hx' : x'.1 ≫ pullback.snd s g = 𝟙 _ := pullback.lift_snd _ _ _
  have hsq : IsPullback g x'.1 x.1 q := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback s g)
    · simpa only [hx, hx'] using
        (IsPullback.of_vert_isIso (show CommSq g (𝟙 _) (𝟙 _) g from ⟨by simp⟩))
    · exact (pullback.lift_fst (g ≫ x.1) (𝟙 _) (by simp [hx, g])).symm
  have hker : x.1.ker.comap q = x'.1.ker := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← hsq.flip.isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso]
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := q (x'.1.base default)) trivial
  let Ua : X.affineOpens := ⟨U, hU⟩
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (U := q ⁻¹ᵁ U) (x := x'.1.base default) hxU
  let Va : X'.affineOpens := ⟨V, hV⟩
  have hpoint : q (x'.1.base default) = x.1.base default := by
    change (pullback.fst s g) (x'.1.base default) = x.1.base default
    rw [heq]
    exact hy
  have hsource := x.1.ker_stalkMap Ua default (hpoint ▸ hxU)
  have htarget := x'.1.ker_stalkMap Va default hxV
  rw [ker_stalkMap_field k] at hsource
  rw [ker_stalkMap_field K] at htarget
  have hsource' : IsLocalRing.maximalIdeal (X.presheaf.stalk (q (x'.1.base default))) =
      (x.1.ker.ideal Ua).map
        (X.presheaf.germ U (q (x'.1.base default)) hxU).hom := by
    have H (z : X) (hz : z ∈ U) (he : z = x.1.base default) :
        IsLocalRing.maximalIdeal (X.presheaf.stalk z) =
          (x.1.ker.ideal Ua).map (X.presheaf.germ U z hz).hom := by
      subst z
      exact hsource
    exact H _ hxU hpoint
  rw [hsource', htarget, ← hker,
    Scheme.IdealSheafData.ideal_comap_appLE _ q Ua Va hVU, Ideal.map_map,
    Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  apply congrArg CommRingCat.Hom.hom
  change X.presheaf.germ U (q (x'.1.base default)) hxU ≫ q.stalkMap _ =
    q.appLE U V hVU ≫ X'.presheaf.germ V (x'.1.base default) hxV
  rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res,
    Scheme.Hom.germ_stalkMap]

end AlgebraicGeometry
