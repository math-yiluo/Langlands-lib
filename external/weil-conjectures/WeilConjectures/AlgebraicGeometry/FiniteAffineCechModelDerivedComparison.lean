/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModel
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModelAcyclicResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Derived comparison for the specified finite affine Čech model

Source: Stacks Project, Tags 01XB, 01XD and 01FK.
(blueprint: lem-pc-finite-affine-cech-model-derived-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wT

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified section complex computes derived direct image over an affine base.
Neither properness, finite presentation nor relative flatness is required.
Source: Stacks Project, Tags 01XB, 01XD and 01FK.
(blueprint: lem-pc-finite-affine-cech-model-derived-comparison).

Proof: separatedness over the affine base makes every nonempty finite intersection
of members of V affine. Form the augmented alternating sheaf Čech resolution with
terms the finite products of open pushforwards of the restrictions of F. Inserting
a covering index on each cover member contracts the augmentation, so it is a
quasi-isomorphism. Each intersection map to T is affine, hence its quasi-coherent
module is direct-image acyclic by 01XB. Finite products preserve this acyclicity.
The acyclic resolution comparison identifies its pushed complex with Rf_*F[0].
The ordered comparison 01FK identifies the signed differential with the increasing
order-embedding tuples in alternatingCechComplex. On the canonical affine chart
T -> Spec Gamma(T,O), the tilde-Gamma comparison identifies every pushed term and
every restriction with the associated section module. Restriction of scalars along
GammaSpecIso and pullback of the resulting complex are exactly the operations in
finiteAffineCechModel. These termwise identifications therefore give a chain
isomorphism, whose localization composed with the acyclic-resolution comparison
gives the asserted derived isomorphism. Localization uniqueness transports this
comparison to the two independently supplied localizations. If r=0 the covering
condition forces X empty; the zero resolution and zero section complex give the
same comparison. Empty intersections and zero rings also give zero terms. -/
theorem finiteAffineCechModel_derivedComparison
    {X T : Scheme.{u}} (f : X ⟶ T) [IsAffine T] [IsSeparated f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {r : ℕ} (V : Fin r → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hcover : iSup V = ⊤) :
    Nonempty ((DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
        (finiteAffineCechModel f F V) ≅
      (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) := by
  obtain ⟨D, ε, hε, hD, ⟨c⟩⟩ :=
    exists_finiteAffineCechModel_acyclic_resolution f F V hV hcover
  have : QuasiIso ε := hε
  let G := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    infer_instance
  let K := D.extend ComplexShape.embeddingUpNat
  let L : CochainComplex.Plus (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    ⟨K, 0, inferInstance⟩
  have hL : ∀ n, G.rightAcyclic (L.obj.X n) :=
    HomologicalComplex.prop_extend_X _ ComplexShape.embeddingUpNat hD
  have := G.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L hL
  let H := (HomotopyCategory.Plus.quotient
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))).obj L
  let eu : (DerivedCategory.Plus.ι (C := SheafOfModules.{u}
        (moduleRings T.toRingedSpace))).obj
        (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj H)) ≅
      DerivedCategory.Qh.obj ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj K)) :=
    (DerivedCategory.Plus.ι (C := SheafOfModules.{u}
      (moduleRings T.toRingedSpace))).mapIso
        (asIso (G.rightDerivedFunctorPlusUnith.app H)).symm
  let e : G.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    G.rightDerivedFunctor.mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))).symm.app K) ≪≫
      (G.rightDerivedFunctorPlusCompatibility.app (DerivedCategory.Plus.Qh.obj H)).symm ≪≫
      eu ≪≫ (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings T.toRingedSpace))).app _
  have : QuasiIso (HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff ε ComplexShape.embeddingUpNat).2 inferInstance
  let eF : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F ≅
        DerivedCategory.Q.obj K :=
    (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app F ≪≫
      DerivedCategory.Q.mapIso
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).symm ≪≫
      asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap ε
        ComplexShape.embeddingUpNat))
  exact ⟨(DerivedCategory.Q.mapIso c).symm ≪≫ e.symm ≪≫
    (G.rightDerivedFunctor.mapIso eF).symm⟩

end AlgebraicGeometry.Scheme.Modules
