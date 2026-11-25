/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality

/-! # Coordinate invariance of the stalk comparison

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-coordinate-invariance).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

private theorem stalkComparison_normalized
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c : Coordinates g' K K' φ) (z : X') (i : ℤ) :
    stalkComparison f f' g g' sq c z i ≫
        ((comparisonStalkHomologyIso X' z c.N i).inv ≫
          (comparisonStalkCohomology X' z i).map c.e'.hom) =
      comparisonIntoPullback f f' g g' sq z c.P c.counit_isIso i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map c.e.hom ≫ φ) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  have := c.counit_isIso
  have ht := comparisonStalkHomologyIso_naturality X' z c.t i
  have ht' : HomologicalComplex.homologyMap
      (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).map c.t) i ≫ (comparisonStalkHomologyIso X' z c.N i).inv =
      (comparisonStalkHomologyIso X' z
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).inv ≫
          (comparisonStalkCohomology X' z i).map (DerivedCategory.Q.map c.t) := by
    apply (cancel_epi (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).hom).mp
    rw [← Category.assoc, ← ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht'' := congrArg (fun a => a ≫ (comparisonStalkCohomology X' z i).map c.e'.hom) ht'
  simp only [Category.assoc] at ht''
  simp only [stalkComparison, comparisonIntoPullback, Category.assoc, Functor.map_comp, cast_eq]
  rw [← Functor.map_comp, ← Functor.map_comp, ← c.represents]
  simp only [Functor.map_comp, cast_eq, IsIso.inv_hom_id_assoc]
  rw [ht'']

/-- Invertibility of the canonical stalk comparison is independent of coordinates.

Proof: the isomorphism c.e followed by d.e.inv identifies P_c and P_d in D(O_X).
Exact stalks and restriction to R carry it to D(R). Uniqueness of the universal
left-derived scalar-extension functor, and cohomologyIso_smul, induce an
A-tensor-R-B-linear isomorphism on the source cohomology objects. Extending to C
preserves this isomorphism. The isomorphism c.e' followed by d.e'.inv similarly
induces an isomorphism from H^i(N_c,z) to H^i(N_d,z), because stalks are exact.
K-flatness of the sheaf representatives gives K-flatness of their stalks by
lem-pc-kflat-stalk-criterion, so ordinary A-to-C extension of these representatives
computes derived pullback. The universal pullback counits and tensorStalkIso
identify its cohomology with the coordinate target before the chain map.
The represents equations express both coordinate maps as the same morphism phi.
After applying stalks, derived cohomology, the two model counit equations and
naturality of tensorStalkIso, they give a commuting square with stalkComparison c
and stalkComparison d as horizontal maps and these two isomorphisms as vertical
maps. Conjugating either horizontal map by the vertical isomorphisms gives the
other; composition with isomorphisms preserves and reflects invertibility.
This argument only uses derived isomorphisms; it does not assume a chain map
between the two coordinate complexes, or that ordinary pullback preserves
quasi-isomorphisms.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-coordinate-invariance). -/
theorem isIso_stalkComparison_iff_coordinates
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c d : Coordinates g' K K' φ) (z : X') (i : ℤ) :
    IsIso (stalkComparison f f' g g' sq c z i) ↔
      IsIso (stalkComparison f f' g g' sq d z i) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  let a := c.e ≪≫ d.e.symm
  obtain ⟨e, he, _⟩ := exists_comparisonSourceIso f f' g g' sq z c.P d.P a i
  have hn := comparisonIntoPullback_naturality f f' g g' sq z c.P d.P
    c.isKFlat d.isKFlat c.counit_isIso d.counit_isIso a i e he
  let E := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (TensorProduct (R f g' z) (A g' z) (B f' z)) (C z))
  let H := comparisonStalkCohomology X' z i
  let cTarget := (comparisonStalkHomologyIso X' z c.N i).symm ≪≫ H.mapIso c.e'
  let dTarget := (comparisonStalkHomologyIso X' z d.N i).symm ≪≫ H.mapIso d.e'
  have ha : (derivedPullback g').map a.hom ≫ (derivedPullback g').map d.e.hom =
      (derivedPullback g').map c.e.hom := by
    rw [← Functor.map_comp]
    simp only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hs : stalkComparison f f' g g' sq c z i ≫ cTarget.hom =
      E.map e.hom ≫ stalkComparison f f' g g' sq d z i ≫ dTarget.hom := by
    dsimp only [cTarget, dTarget, H, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [stalkComparison_normalized f f' g g' sq c z i,
      stalkComparison_normalized f f' g g' sq d z i]
    rw [← Category.assoc, ← hn, Category.assoc, ← Functor.map_comp]
    rw [← Category.assoc ((derivedPullback g').map a.hom) _ φ, ha]
  constructor
  · intro hc
    have := hc
    have hcomp : IsIso (E.map e.hom ≫ stalkComparison f f' g g' sq d z i ≫
        dTarget.hom) := by
      rw [← hs]
      infer_instance
    have : IsIso (stalkComparison f f' g g' sq d z i ≫ dTarget.hom) :=
      IsIso.of_isIso_comp_left (E.map e.hom) _
    exact IsIso.of_isIso_comp_right _ dTarget.hom
  · intro hd
    have := hd
    have hcomp : IsIso (stalkComparison f f' g g' sq c z i ≫ cTarget.hom) := by
      rw [hs]
      infer_instance
    exact IsIso.of_isIso_comp_right _ cTarget.hom

end AlgebraicGeometry.SingleComplexBaseChange
