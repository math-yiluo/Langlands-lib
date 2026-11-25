/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.RelativeOpenDifferenceDiagram
import all WeilConjectures.AlgebraicGeometry.DerivedOpenGluingObjects

/-! # Extending a two-open derived gluing datum to the ambient scheme

Source: Stacks Project, Tag 08DG.
(blueprint: lem-sc-ambient-open-gluing-object).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- The cone construction elaborates several derived restriction comparisons.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Two derived objects with an overlap identification extend to one ambient derived object.
Only objects and their transition are constructed; there is no assertion about maps.
Source: Stacks Project, Tag 08DG, its direct-image cone construction.
(blueprint: lem-sc-ambient-open-gluing-object).

Proof: Take the direct-image sum M = RjW_* A plus RjV_* B and the overlap image N
of B restricted to W intersect V. The relative difference-diagram theorem gives
d : M to N, projection maps pW, pV and an overlap counit k. Its split local
normal forms say that (pW, JW(d)) and (pV, JV(d)) are isomorphisms, and its
difference identity gives the relation between the overlap projections.
Complete d to a distinguished triangle G to M to N to G[1]. Restrict this
triangle to W. Compare it with the split biproduct triangle A to A plus JW(N)
to JW(N) to A[1]; the isomorphism (pW, JW(d)) on middle terms and the identity
on last terms give an isomorphism on first terms by the two-out-of-three
lemma for morphisms of distinguished triangles. Its first morphism is JW(f)
followed by pW. Thus that composite is invertible; similarly JV(f) followed
by pV is invertible. Use these composites as jW and jV. Precompose the
difference identity by restriction of f to the overlap. Naturality of sW and
sV rewrites its left side as the difference of the two requested transition
composites. Its right side is zero because f followed by d is zero in a
distinguished triangle. The difference-zero equation is the desired transition.
No cover hypothesis is used; empty and disjoint opens satisfy the same
split local normal forms and distinguished-triangle calculation. -/
theorem exists_ambient_open_gluing_object
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory W.toScheme) (B : schemeDerivedCategory V.toScheme) :
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    ∀ (c : SW.obj A ≅ SV.obj B),
      ∃ (G : schemeDerivedCategory X) (jW : JW.obj G ≅ A) (jV : JV.obj G ≅ B),
        sW.inv.app G ≫ SW.map jW.hom ≫ c.hom = sV.inv.app G ≫ SV.map jV.hom := by
  classical
  let U := W
  dsimp only
  intro c
  let rU := (schemeOpenRestriction X U).mapDerivedCategory
  let rV := (schemeOpenRestriction X V).mapDerivedCategory
  let sU := (schemeOpenOverlapRestriction X (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory
  let sV := (schemeOpenOverlapRestriction X (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory
  let rW := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory
  let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U)
  let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V)
  let E := (schemeDerivedDirectImage U.ι).obj A ⊞ (schemeDerivedDirectImage V.ι).obj B
  let D := (schemeDerivedDirectImage (U ⊓ V).ι).obj (sV.obj B)
  obtain ⟨d, pU, pV, k, hU, hV, hdiff⟩ :=
    relative_open_difference_diagram.{u, w} X U V A B c
  obtain ⟨F, f, h, ht⟩ := Pretriangulated.distinguished_cocone_triangle₁
    (C := schemeDerivedCategory X) (Y := E) (Z := D) d
  let T : Pretriangulated.Triangle (schemeDerivedCategory X) := Pretriangulated.Triangle.mk f d h
  have ht' : T ∈ distTriang (schemeDerivedCategory X) := ht
  have hiU : IsIso (rU.map f ≫ pU) :=
    AlgebraicGeometry.isIso_fiber_projection
      (rU.mapTriangle.obj T) (rU.map_distinguished T ht') A pU (by
      dsimp only [Functor.mapTriangle, T, Pretriangulated.Triangle.mk]
      exact hU)
  have hiV : IsIso (rV.map f ≫ pV) :=
    AlgebraicGeometry.isIso_fiber_projection
      (rV.mapTriangle.obj T) (rV.map_distinguished T ht') B pV (by
      dsimp only [Functor.mapTriangle, T, Pretriangulated.Triangle.mk]
      exact hV)
  let _ := hiU
  let _ := hiV
  refine ⟨F, asIso (rU.map f ≫ pU), asIso (rV.map f ≫ pV), ?_⟩
  change eU.inv.app F ≫ sU.map (rU.map f ≫ pU) ≫ c.hom =
    eV.inv.app F ≫ sV.map (rV.map f ≫ pV)
  have hz : f ≫ d = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ T ht'
  change eU.inv.app E ≫ sU.map pU ≫ c.hom - eV.inv.app E ≫ sV.map pV =
    rW.map d ≫ k at hdiff
  exact AlgebraicGeometry.compatible_of_difference rU rV rW sU sV eU eV c f d pU pV k hz hdiff


end AlgebraicGeometry.Scheme
