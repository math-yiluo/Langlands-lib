/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit

/-! Invertibility of the derived stalk comparison from its K-flat equation.
(blueprint: lem-pc-stalk-derived-extension-comparison-is-iso) -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
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

/-- Any natural comparison satisfying the K-flat equation is invertible.

Proof: on a K-flat representative, the scalar-extension counit is invertible by
K-flatness of its stalk. All the remaining factors in the equation are images
of isomorphisms, including the inverse pullback counit assumed there. Thus the
comparison component is invertible after cancelling the source factor.
For an arbitrary derived object, choose K-flat coordinates for the identity of
its pullback. These give a K-flat representative, an invertible pullback counit,
and an isomorphism from its localization to the object. Naturality transports
invertibility from that representative to the object. Componentwise invertibility
then gives invertibility of the natural transformation.
Source: Stacks Project, perfect.tex, equation-bc before Tag 0DJ8 (Tag 0DJ7);
Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-stalk-derived-extension-comparison-is-iso). -/
theorem stalkDerivedExtensionComparison_isIso (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (C z))
    ∀ (L : DerivedCategory (ModuleCat.{u} (A g' z)) ⥤
      DerivedCategory (ModuleCat.{u} (C z)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars.{u, u, u}
          ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategory
              (.up ℤ) ⋙ DerivedCategory.Qh)
      (_hL : L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} (A g' z)) (.up ℤ)))
      (j : comparisonDerivedStalk X (g' z) ⋙ L ⟶
        derivedPullback g' ⋙ comparisonDerivedStalk X' z)
      (_hj :
      ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (_hP : P.IsKFlatTensor)
        (_hcP : IsIso ((counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))),
        L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
            j.app (DerivedCategory.Q.obj P) =
          L.map ((DerivedCategory.quotientCompQhIso _).inv.app (stalkComplex g' z P)) ≫
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (stalkComplex g' z P)) ≫
            DerivedCategory.Qh.map
              (((ModuleCat.extendScalars.{u, u, u}
                ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
                  (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategoryFactors
                  (.up ℤ)).hom.app
                (stalkComplex g' z P)) ≫
            (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (C z))).hom.app
              (tensorComplex f f' g g' sq z P) ≫
            DerivedCategory.Q.map (tensorStalkIso f f' g g' sq z P).hom ≫
            (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapDerivedCategoryFactors.inv.app
                (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) ≫
            (comparisonDerivedStalk X' z).map
              (cast (by rfl)
                (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))),
      IsIso j := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (C z))
  intro L ε hL j hj
  have hcomp (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (hP : P.IsKFlatTensor)
      (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
      IsIso (j.app (DerivedCategory.Q.obj P)) := by
    have := hcP
    have hstalk := (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace P).mp hP (g' z)
    have := ModuleCat.scalarExtensionCounit_isIso_of_kFlat
      ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
        (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))
      (stalkComplex g' z P) hstalk L ε hL
    have heq := hj P hP hcP
    have : IsIso (L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
        j.app (DerivedCategory.Q.obj P)) := by
      rw [heq]
      simp only [cast_eq]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (g' z)).mapDerivedCategoryFactors.inv.app P)) _
  have hobj (K : schemeDerivedCategory X) : IsIso (j.app K) := by
    obtain ⟨c⟩ := nonempty_coordinates g' K ((derivedPullback g').obj K) (𝟙 _)
    have := hcomp c.P c.isKFlat c.counit_isIso
    have heq := j.naturality c.e.hom
    have : IsIso (((comparisonDerivedStalk X (g' z) ⋙ L).map c.e.hom) ≫ j.app K) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((comparisonDerivedStalk X (g' z) ⋙ L).map c.e.hom) _
  have : ∀ K, IsIso (j.app K) := hobj
  exact NatIso.isIso_of_isIso_app j


end AlgebraicGeometry.SingleComplexBaseChange
