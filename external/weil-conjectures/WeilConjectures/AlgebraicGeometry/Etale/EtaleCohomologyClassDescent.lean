/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity

/-!
# Descent of an etale cohomology class to a finite stage

Source: the first proof step of blueprint corollary-cohomology-pro-etale-affine;
Stacks Project, Tags 03Q6 and 09YQ.
(blueprint: lem-weil-pbc-etale-cohomology-class-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Every class on the limit is the pullback of a class at a stage mapping to `i`.
This is only the class-descent part of continuity; it asserts no eventual vanishing.

Source: blueprint corollary-cohomology-pro-etale-affine, proof step 1 and
blueprint_sketch proof paragraph beginning "Let alpha"; Stacks Tags 03Q6 and 09YQ.
(blueprint: lem-weil-pbc-etale-cohomology-class-descent)

Proof:
1. Restrict the system to `Over i`. Its forgetful functor is initial, so the
   restricted cone is still a limit. The new stage sheaves are the pullbacks of F.
   The limit is qcqs since the projections of an affine-transition limit are affine.
2. By corollary-cohomology-pro-etale-affine, choose a finite split hypercover and a
   degree-q cocycle representing the given class. Compare the derived-global-sections
   encoding there with Sheaf.H using lem-weil-pbc-ext-via-injective-resolution: global
   sections are Hom from the constant integer sheaf, and their resolution complexes
   therefore agree. The pullback identification is the resolution comparison of
   lem-weil-pbc-cohomology-pullback-derived-unit.
3. Descend the skeleton through degree q+1 by lemma-weil-pbc-finite-hypercover-descent.
   Only finitely many components, structure maps, identities and matching covers occur.
   The descended skeleton extends to a split hypercover by successively choosing finite
   etale covers of the matching objects, as in corollary-cohomology-pro-etale-affine.
4. On the finite degree-q components, proposition-comparison-morphism-inverse-image--3 descends
   the cocycle sections, after a finite refinement if needed. Cofilteredness supplies
   one stage for all components. Apply the equality part of section continuity to the
   finitely many equations saying that the alternating differential is zero. Move to
   one later stage where they all hold.
5. The descended cocycle defines a stage cohomology class by the same hypercover
   comparison. Its pullback is the original cocycle, hence the original class. The
   comparison is natural for pullback, so the resulting equality is precisely the
   displayed cohomologyMap followed by upperStarComp inverse. For q=0 the same argument
   is descent of a section and its degree-one compatibility equations; there is no
   negative-degree cochain. Zero sheaves and empty schemes give the zero class. -/
theorem exists_cohomology_class_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
    [∀ j : J, CompactSpace (D.obj j)] [∀ j : J, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : J)
    (F : Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (_hF : F.IsTorsion) (q : ℕ) :
    (∀ x : Sheaf.H (((c.π.app i)^*[AddCommGrpCat.{u + 1}]).obj F) q,
      ∃ (j : J) (f : j ⟶ i)
        (y : Sheaf.H (((D.map f)^*[AddCommGrpCat.{u + 1}]).obj F) q),
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm).inv.app F) q
          (cohomologyMap (c.π.app j) _ q y) = x) := by
  -- Use the existing fixed-base continuity theorem with explicitly constructed canonical legs.
  let E : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D
  let (a : Over i) : CompactSpace (E.obj a) :=
    inferInstanceAs (CompactSpace (D.obj a.left))
  let (a : Over i) : QuasiSeparatedSpace (E.obj a) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj a.left))
  let {a b : Over i} (g : a ⟶ b) : IsAffineHom (E.map g) :=
    inferInstanceAs (IsAffineHom (D.map g.left))
  let π : E ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app := fun a ↦ D.map a.hom
      naturality := fun a b g ↦ by
        dsimp [E]
        simpa only [Category.comp_id, ← D.map_comp] using congrArg D.map g.w }
  let c' : Cone E := c.whisker (Over.forget i)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv _ c).symm hc
  have hπ {j k : Over i} (f : j ⟶ k) : π.app j = E.map f ≫ π.app k := by
    have h := (π.naturality f).symm
    change π.app j ≫ 𝟙 (D.obj i) = E.map f ≫ π.app k at h
    exact (Category.comp_id _).symm.trans h
  have ht (j : Over i) : c.π.app i = c'.π.app j ≫ π.app j := (c.w j.hom).symm
  have laws := cohomologyTriangleMap_laws (D.obj i) F q
  let H : (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun j ↦ AddCommGrpCat.of
        (Sheaf.H (((π.app j.unop)^*[AddCommGrpCat.{u + 1}]).obj F) q)
      map := fun f ↦ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (E.map f.unop) (π.app _) (π.app _) (hπ f.unop) F q)
      map_id := by
        intro j
        dsimp
        simp only [E.map_id]
        exact (congrArg AddCommGrpCat.ofHom
          (laws.1 (E.obj j.unop) (π.app j.unop))).trans AddCommGrpCat.ofHom_id
      map_comp := by
        intro j k l f g
        dsimp
        simp only [E.map_comp]
        exact (congrArg AddCommGrpCat.ofHom
          (laws.2 (E.obj l.unop) (E.obj k.unop) (E.obj j.unop)
            (E.map g.unop) (E.map f.unop) (π.app j.unop) (π.app k.unop)
            (π.app l.unop) (hπ f.unop) (hπ g.unop))).trans
              (AddCommGrpCat.ofHom_comp _ _) }
  let eH (j : Over i) : H.obj (Opposite.op j) ≅
      AddCommGrpCat.of (Sheaf.H (((π.app j)^*[AddCommGrpCat.{u + 1}]).obj F) q) :=
    Iso.refl _
  let B : Cocone H :=
    { pt := AddCommGrpCat.of
        (Sheaf.H (((c.π.app i)^*[AddCommGrpCat.{u + 1}]).obj F) q)
      ι :=
        { app := fun j ↦ AddCommGrpCat.ofHom
            (cohomologyTriangleMap (c'.π.app j.unop) (π.app j.unop)
              (c.π.app i) (ht j.unop) F q)
          naturality := by
            intro j k f
            dsimp
            simp only [Category.comp_id]
            have h := laws.2 c'.pt (E.obj k.unop) (E.obj j.unop)
              (c'.π.app k.unop) (E.map f.unop) (π.app j.unop) (π.app k.unop)
              (c.π.app i) (hπ f.unop) (ht k.unop)
            simp only [c'.w f.unop] at h
            simpa only [AddCommGrpCat.ofHom_comp] using
              (congrArg AddCommGrpCat.ofHom h).symm } }
  have hH (j k : Over i) (f : j ⟶ k) : H.map f.op =
      (eH k).hom ≫ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (E.map f) (π.app k) (π.app j) (hπ f) F q) ≫
          (eH j).inv := by simp [H, eH]
  have hB (j : Over i) : B.ι.app (Opposite.op j) ≫ (Iso.refl B.pt).hom =
      (eH j).hom ≫ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (c'.π.app j) (π.app j) (c.π.app i) (ht j) F q) := by
    simp [B, eH]
  obtain ⟨hcolimit⟩ := nonempty_isColimit_cofiltered_fixed_base_cohomology
    E π c' hc' (c.π.app i) ht F q H eH hH B (Iso.refl _) hB
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  intro x
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep H hcolimit x
  exact ⟨j.unop.left, j.unop.hom, y, hy⟩

end AlgebraicGeometry.Etale
