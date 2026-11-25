/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear

/-! # Scalar action on derived global sections

Source: Stacks Project, Tags 01E4 and 01E5.
(blueprint: lem-pc-resolution-scalar-action)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- Derived global sections send multiplication to scalar multiplication.
Source: Stacks Project, Tags 01E4 and 01E5.
(blueprint: lem-pc-resolution-scalar-action)

Proof: Multiplication by the global section termwise on an injective resolution lifts
multiplication on the resolved module, by naturality of multiplication. After global
sections this is scalar multiplication on the complex. Homology preserves this scalar
endomorphism, and naturality of the linear resolution comparison gives the result. -/
theorem moduleCohomology_map_smulHom {X : Scheme.{u}} (M : X.Modules)
    (I : InjectiveResolution M) (p : ℕ) (a : Γ(X, ⊤))
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj M) :
    ((RingedSpace.moduleCohomology X.toRingedSpace p).map (M.smulHom a)).hom x = a • x := by
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
    inferInstanceAs (CommRing Γ(X, ⊤))
  let φ : I.cocomplex ⟶ I.cocomplex :=
    { f := fun n ↦ (I.cocomplex.X n).smulHom a
      comm' := fun n m _ ↦ smulHom_naturality (I.cocomplex.d n m) a }
  have hφ : I.ι.f 0 ≫ φ.f 0 = M.smulHom a ≫ I.ι.f 0 :=
    (smulHom_naturality (I.ι.f 0) a).symm
  have h := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (M.smulHom a) I I φ hφ (RingedSpace.globalSectionsFunctor X.toRingedSpace) p
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have hΓ : (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map φ =
      (show (moduleRings X.toRingedSpace).obj.obj (op ⊤) from a) •
        𝟙 (RingedSpace.globalSectionsComplex I) := by
    ext n y
    exact smulHom_app_top_apply (I.cocomplex.X n) a y
  rw [Functor.comp_map, hΓ] at h
  have hs : (HomologicalComplex.homologyFunctor
      (ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (ComplexShape.up ℕ) p).map
      ((show (moduleRings X.toRingedSpace).obj.obj (op ⊤) from a) •
        𝟙 (RingedSpace.globalSectionsComplex I)) =
      (show (moduleRings X.toRingedSpace).obj.obj (op ⊤) from a) • 𝟙 _ := by
    change ShortComplex.homologyMap _ = _
    have ht : (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
        ((show (moduleRings X.toRingedSpace).obj.obj (op ⊤) from a) •
          𝟙 (RingedSpace.globalSectionsComplex I)) =
        (show (moduleRings X.toRingedSpace).obj.obj (op ⊤) from a) • 𝟙 _ := by
      ext <;> rfl
    rw [ht, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  rw [hs] at h
  let e := I.isoRightDerivedObj Γ p
  apply e.toLinearEquiv.injective
  have hx := ConcreteCategory.congr_hom h x
  change e.hom.hom (((RingedSpace.moduleCohomology X.toRingedSpace p).map
    (M.smulHom a)).hom x) = e.hom.hom (a • x)
  rw [e.hom.hom.map_smul]
  change e.hom.hom (((RingedSpace.moduleCohomology X.toRingedSpace p).map
    (M.smulHom a)).hom x) = a • e.hom.hom x at hx
  exact hx

end AlgebraicGeometry.Scheme.Modules
