/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.OpenClosed.Derived
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The ordinary derived closed-support triangle

Source: blueprint sec-smooth-purity/sk-prop-sf-existence,
lemma-local-cohomology-right-adjoint--2, order 1804; Stacks Project, Tags 0A45 and 0152
(blueprint: lemma-local-cohomology-right-adjoint--2).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- For a complementary closed-open pair and a finite, possibly noncommutative ring,
the closed adjunction counit and open adjunction unit extend to a natural distinguished
triangle on the ordinary unbounded derived category. Module-valued etale sheaves encode
left modules over the sheafification of the constant ring presheaf: a locally represented
constant scalar acts locally, and the resulting sections glue uniquely. This is the same
encoding as the recorded closed-ambient adjoint, without constructibility conditions.

Source: blueprint lemma-local-cohomology-right-adjoint--2, order 1804; Stacks Project,
Tags 0A45 (support triangle), 0152 (boundary), 079P (injective-term replacement),
070K (total derivation), 08FI (restriction of K-injectives), 04CA (closed direct image),
09XQ (sections with support) and 093X (restriction of injective sections)
(blueprint: lemma-local-cohomology-right-adjoint--2).

Proof:
1. Write F = Ri_*, G = Rj_* and J = D(j^*). Both direct images are fully faithful
   on sheaves and preserve K-injectives, so their total right derived functors are
   fully faithful. Use the supplied adjunction of F with its chosen right adjoint.
2. Disjointness gives J(FM) = 0. Since J commutes with shifts, the open adjunction
   gives Hom((FM)[n], GN) = Hom(J((FM)[n]), N) = 0 for every integer n.
3. If JE = 0, the closed inverse/direct-image unit E → Ri_*D(i^*)E becomes invertible
   after J, since both objects vanish, and after D(i^*), by full faithfulness and
   the triangle identity. Derived open-closed conservativity makes the unit invertible.
   Thus E belongs to the essential image of F.
4. Complete the open unit K → GJK to a distinguished triangle K' → K → GJK.
   Full faithfulness of G and the triangle identity make J invert the unit, so JK' = 0.
   Step 3 puts K' in the essential image of F. The orthogonal counit-triangle theorem
   now replaces K' → K with the prescribed counit F(F.rightAdjoint K) → K.
5. Choose a boundary for each K. Given f : K → L, triangle-morphism extension gives
   a triangle map with middle component f. Shift-one orthogonality and Hom exactness
   uniquely determine its first and third components from their adjacent squares.
   Counit and unit naturality identify those components with the specified functor maps;
   its last square is boundary naturality. The resulting natural transformation has
   distinguished components by Step 4. No boundedness or constructibility is used. -/
theorem exists_etale_closedSupportTriangle
    (A : Type (u + 1)) [Ring A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃ δ : D(upperStar (ModuleCat.{u + 1} A) j) ⋙
        R(lowerStar (ModuleCat.{u + 1} A) j) ⟶
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
          R(lowerStar (ModuleCat.{u + 1} A) i)) ⋙
          shiftFunctor (_root_.DerivedCategory
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) (1 : ℤ),
      ∀ K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        Triangle.mk
          ((Adjunction.ofIsLeftAdjoint
            (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K)
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app K)
          (δ.app K) ∈ distTriang _ := by
  classical
  let C := ModuleCat.{u + 1} A
  let F := R(lowerStar C i)
  let G := R(lowerStar C j)
  let J := D(upperStar C j)
  let adj := Adjunction.ofIsLeftAdjoint F
  let adjj := mapDerivedUpperStarLowerStarAdjunction C j
  let adji := mapDerivedUpperStarLowerStarAdjunction C i
  have hd : Disjoint (Set.range j.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  -- Orthogonality of the closed image and the open direct image, in every shift.
  have horth (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C))
      (N : _root_.DerivedCategory (Sheaf U.smallEtaleTopology C)) (n : ℤ) :
      Subsingleton ((F.obj M)⟦n⟧ ⟶ G.obj N) := by
    have hz : IsZero (J.obj ((F.obj M)⟦n⟧)) :=
      ((shiftFunctor _ n).map_isZero
        (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
          C j i hd M)).of_iso ((J.commShiftIso n).app _)
    have : Subsingleton (J.obj ((F.obj M)⟦n⟧) ⟶ N) :=
      ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
    exact (adjj.homEquiv _ _).symm.subsingleton
  -- The unit to the closed image is invertible whenever open restriction vanishes.
  have hess {E : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C)}
      (hE : IsZero (J.obj E)) : F.essImage E := by
    have hη : IsIso (adji.unit.app E) := by
      apply (jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar' C j i hij).isIso_of_pairFunctor
      · exact ⟨⟨0, hE.eq_of_src _ _,
          (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
            C j i hd _).eq_of_src _ _⟩⟩
      · have : IsIso adji.counit := adji.counit_isIso_of_R_fully_faithful
        rw [← IsIso.inv_eq_of_inv_hom_id (adji.left_triangle_components E)]
        infer_instance
    exact ⟨D(upperStar C i).obj E, ⟨(asIso (adji.unit.app E)).symm⟩⟩
  -- Complete the open unit and identify its fibre using the closed adjunction.
  have hex (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C)) :
      ∃ w, Triangle.mk (adj.counit.app K) (adjj.unit.app K) w ∈ distTriang _ := by
    obtain ⟨K', a, w, hT⟩ := distinguished_cocone_triangle₁ (adjj.unit.app K)
    have hK' : IsZero (J.obj K') := by
      have : IsIso adjj.counit := adjj.counit_isIso_of_R_fully_faithful
      have : IsIso (J.map (adjj.unit.app K)) := by
        rw [← IsIso.inv_eq_of_inv_hom_id (adjj.left_triangle_components K)]
        infer_instance
      exact (Triangle.isZero₁_iff_isIso₂ _ (J.map_distinguished _ hT)).2 this
    exact exists_distTriang_counit_of_subsingleton adj
      (Functor.FullyFaithful.ofFullyFaithful F) hT
      (fun M n ↦ horth M _ n) (hess hK')
  -- Orthogonality makes the chosen connecting maps natural on all derived morphisms.
  choose w hw using hex
  refine ⟨{ app := w, naturality := ?_ }, hw⟩
  intro K K' f
  have : Subsingleton
      ((Triangle.mk (adj.counit.app K) (adjj.unit.app K) (w K)).obj₁⟦(1 : ℤ)⟧ ⟶
        (Triangle.mk (adj.counit.app K') (adjj.unit.app K') (w K')).obj₃) :=
    horth _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero (hw K) (hw K') f (by
    rw [← Category.assoc]
    erw [← adj.counit_naturality]
    rw [Category.assoc]
    erw [comp_distTriang_mor_zero₁₂ _ (hw K')]
    rw [comp_zero])
  have h₁ : τ.hom₁ = F.map (F.rightAdjoint.map f) :=
    Triangle.cancel_mor₁_of_subsingleton (hw K') (by
      rw [← τ.comm₁, hτ]
      exact (adj.counit_naturality f).symm)
  have h₃ : τ.hom₃ = G.map (J.map f) :=
    Triangle.cancel_mor₂_of_subsingleton (hw K) (by
      rw [τ.comm₂, hτ]
      exact (adjj.unit_naturality f).symm)
  have h := τ.comm₃
  rw [h₁, h₃] at h
  exact h.symm

end AlgebraicGeometry.Etale
