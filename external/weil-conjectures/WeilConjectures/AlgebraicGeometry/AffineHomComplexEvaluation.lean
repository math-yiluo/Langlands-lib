/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.AffineHomComplexEvaluationD
import WeilConjectures.Algebra.Homology.HomComplexUnitIso

/-! # Termwise affine Hom evaluation

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0, and 0AX3.
-/

@[expose] public section
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace AlgebraicGeometry
/-- The affine Hom comparison and evaluation identity hold before localization, on
all unbounded complexes. The unit-Hom comparison is chosen by evaluation at one.

Source: Stacks Project, duality.tex, lemma-compute-sheafhom-affine (0BUZ),
lemma-sheafhom-affine-adjoint (0BV0), and remark-trace-map-finite (0AX3);
the termwise calculation in the proof of lem-sc-affine-hom-kinjective-evaluation.
(blueprint: lem-sc-affine-hom-complex-evaluation).

Proof:
1. In the product defining Hom from a degree-zero sheaf, all factors except
   the zero source degree vanish. Projection to the zero factor is an isomorphism;
   its inverse inserts the given map in that factor and zero in all others.
   The differential formula reduces to postcomposition by the target differential.
2. For the unit source, compose that projection with evaluation at one. Its inverse
   sends x to the linear map r -> r*x. These are inverse sheaf maps and commute
   with differentials and all chain maps. They give the natural isomorphism e.
3. The restriction of the direct-image algebra unit is f_*O_X: both have on an
   open U the module O_X(f^{-1}U), with the scalar action through f.c. Use this
   sectionwise identity, apply iH in every degree, and then invert the projection
   in step 1 for the source f_*O_X[0]. This constructs the chain isomorphism d.
4. Under these projections, precomposition by O_Y -> f_*O_X sends a local linear
   map phi to the map r -> phi(f.c(r)). Evaluation at one is phi(1), since f.c
   preserves one. The hypothesis h_eval identifies this with the counit in each
   degree. Extensionality on opens and sections, followed by chain-map
   extensionality, proves the equality. Zero rings, empty schemes, zero complexes,
   and unbounded complexes are included: no exactness of products is used. -/
theorem affine_hom_complex_evaluation
    {Y X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      [H.Additive]
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor Y.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H)
    (h_eval : ∀ (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (U : Y.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U))) :
    ∃ e : (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
      ∀ I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      ∃ d : (((SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
            (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj I)) ≅
          homComplex (R := Y.toRingedSpace.sheaf)
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                ((Scheme.Modules.pushforward f).obj
                  (SheafOfModules.unit X.ringCatSheaf))) I,
        d.hom ≫ ((homComplexFunctor (R := Y.toRingedSpace.sheaf)).map
          (((CochainComplex.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op)).app I ≫
            e.hom.app I =
              ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app I) := by
  classical
  obtain ⟨e⟩ := CategoryTheory.homComplex_unit_iso
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
  refine ⟨e, ?_⟩
  exact affine_hom_complex_d f H iH adj₀ h_eval e

end AlgebraicGeometry
