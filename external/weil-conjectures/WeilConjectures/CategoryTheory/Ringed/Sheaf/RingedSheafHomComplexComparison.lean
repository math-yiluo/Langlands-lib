/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Ringed.RingedHomComplexComparison

/-! # The product-total Hom comparison for actual sheaf complexes

Source: Stacks Project, Section 0A8X; the component calculation in the ringed-forgetting
argument (blueprint: lem-sf-ringed-sheaf-hom-complex-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r d vd s
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  {R : Sheaf J CommRingCat.{max c v r}}
  {D : Type d} [Category.{vd} D] {J' : GrothendieckTopology D}
  [J'.HasSheafCompose (forget₂ CommRingCat.{max d vd s} RingCat.{max d vd s})]
  {R' : Sheaf J' CommRingCat.{max d vd s}}
  (U : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{max d vd s}
      ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj R'))
  [U.Additive] [PreservesLimitsOfShape (Discrete ℤ) U]
  (h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) ⋙ U ≅
    (U.op.prod U) ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R')))

attribute [local irreducible] homComplexFunctor homComplexπ

/-- Product preservation and the specified sheaf-Hom comparison induce the normalized
comparison of actual Hom complexes.
Source: Stacks Project, Section 0A8X; steps 4–5 of the ringed-forgetting comparison
(blueprint: lem-sf-ringed-sheaf-hom-complex-comparison).
Proof: specialize the abstract product-total comparison to homComplexFunctor and homComplexπ.
The cones homComplexIsLimit give the products. The equations homComplex_d_π give the standard
differential, and homComplexFunctor_map_f_π gives the map equation after composing the two
homObjMap factors. The resulting comparison has exactly the prescribed projections. -/
theorem sheafHomComplexComparison :
    ∃ chain : Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).op.prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := R')),
      ∀ (K I : CochainComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
        (n p q : ℤ) (hpq : p + n = q),
        (chain.hom.app (op K, I)).f n ≫
            homComplexπ (R := R') ((U.mapHomologicalComplex (.up ℤ)).obj K)
              ((U.mapHomologicalComplex (.up ℤ)).obj I) n p q hpq =
          U.map (homComplexπ (R := R) K I n p q hpq) ≫
            h.hom.app (op (K.X p), I.X q) := by
  exact ringedHomComplexComparison U
    (SheafOfModules.homFunctor (R := R)) (SheafOfModules.homFunctor (R := R'))
    (Functor.uncurry.obj (homComplexFunctor (R := R)))
    (Functor.uncurry.obj (homComplexFunctor (R := R')))
    (homComplexπ (R := R)) (homComplexπ (R := R'))
    (homComplexIsLimit (R := R)) (homComplexIsLimit (R := R'))
    (homComplex_d_π (R := R)) (homComplex_d_π (R := R'))
    (by
      intro K K' I I' f g n p q hpq
      simpa only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj,
        SheafOfModules.homFunctor_obj_obj, Quiver.Hom.unop_op,
        SheafOfModules.homFunctor_map_app, SheafOfModules.homFunctor_obj_map,
        Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
        Category.id_comp, Category.comp_id] using
        homComplexFunctor_map_f_π (R := R) f g n p q hpq)
    (by
      intro K K' I I' f g n p q hpq
      simpa only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj,
        SheafOfModules.homFunctor_obj_obj, Quiver.Hom.unop_op,
        SheafOfModules.homFunctor_map_app, SheafOfModules.homFunctor_obj_map,
        Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
        Category.id_comp, Category.comp_id] using
        homComplexFunctor_map_f_π (R := R') f g n p q hpq) h

end CategoryTheory
