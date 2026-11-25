/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackKFlatModel
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.InverseImageExactKFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Relative tensor-pullback homology comparison

Source: Stacks Project, Tag 08EV, second displayed equality;
Cohomology, Lemma 20.27.4 (Tag 08DE).
(blueprint: lem-pc-relative-tensor-pullback-homology-comparison)
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

open CategoryTheory.Limits CochainComplex

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

variable {X : TopCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

private theorem kFlat_tensor_right_of_quasiIso
    {E E' K : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : E ⟶ E') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory (R)
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory (R)
  let := (SheafOfModules.tensorClosed (R)).1.some
  have hc := (mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (mappingCone α) hc
  apply (mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (mapBifunctorMappingCone₁Iso α K (curriedTensor _))

private theorem kFlat_tensor_left_of_quasiIso
    {K L L' : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : L ⟶ L') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory (R)
     QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory (R)
  let := SheafOfModules.symmetricCategory (R)
  let := (SheafOfModules.tensorClosed (R)).1.some
  have hc := (mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (mappingCone α) hc
  let F := curriedTensor (SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R)))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((mappingCone α).d p p') (K.X q)).symm)
  have ht' : (mapBifunctor K (mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (mappingCone α) F (.up ℤ))
  apply (mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (mapBifunctorMappingCone₂Iso K α F)



/-- Restricting scalars identifies the homology of tensor with derived pullback
with the homology computed by any K-flat resolution of the restricted complex.
This comparison does not require finite Tor amplitude or any boundedness of K or P.
Source: Stacks Project, Tag 08EV, second displayed equality, and Cohomology,
Lemma 20.27.4 (Tag 08DE).

Proof: Resolve F[0] by a K-flat complex L. Exact inverse image carries L
to a K-flat resolution of the inverse-image module. Resolve K over O_X by
a K-flat complex A. The K-flat derived-pullback counit identifies Lf*(Q(L))
with Q(f*L), so A tensor f*L computes the displayed derived tensor.
After restricting scalars, tensor associativity identifies this complex with
A restricted to f-inverse O_S tensor f-inverse L. Exact restriction of scalars
preserves the quasi-isomorphism A -> K. Since f-inverse L is K-flat, tensoring
it with the zigzag A| -> K| <- P gives quasi-isomorphisms. Since P is K-flat,
tensoring P with the augmentation f-inverse L -> f-inverse F[0] is also a
quasi-isomorphism. The resulting zigzag identifies homology with that of
P tensor f-inverse F[0]. Exact restriction of scalars and the exact forgetful
functor to abelian sheaves commute with homology. Finally, the isomorphism
Q(K) -> E transports the derived tensor and its homology. The construction
uses no chosen arbitrary derived object and works also for zero modules and
empty schemes.
(blueprint: lem-pc-relative-tensor-pullback-homology-comparison) -/
theorem relativeTensorPullback_homology_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing f.base S.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := TopCat.Sheaf.inverseImageRing f.base S.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
    (hq : QuasiIso q)
    (F : SheafOfModules.{u} (moduleRings S.toRingedSpace)) (i : ℤ) :
    Nonempty
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((DerivedCategory.homologyFunctor _ i).obj
            (E ⊗ (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))).obj
          ((CochainComplex.mapBifunctor P
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (TopCat.Sheaf.inverseImageModule f.base S.sheaf F))
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf)))).homology i)) := by
  classical
  let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
  let B := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let U := SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
  let Uc := U.mapHomologicalComplex (ComplexShape.up ℤ)
  let I := TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf
  let Ic := I.mapHomologicalComplex (ComplexShape.up ℤ)
  let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F
  let V := SheafOfModules.toSheaf B
  let := SheafOfModules.monoidalCategory R
  have hV := CategoryTheory.moduleSheaves_colimits_forgetful.{u, u, u, u}
    B
  have : PreservesFiniteLimits V := hV.2.1
  have : PreservesFiniteColimits V := hV.2.2.1
  have hW := CategoryTheory.moduleSheaves_colimits_forgetful.{u, u, u, u}
    (moduleRings X.toRingedSpace)
  have : PreservesFiniteLimits (U ⋙ V) := hW.2.1
  have : PreservesFiniteColimits (U ⋙ V) := hW.2.2.1
  have : PreservesFiniteLimits U := preservesFiniteLimits_of_reflects_of_preserves U V
  have : PreservesFiniteColimits U := preservesFiniteColimits_of_reflects_of_preserves U V
  obtain ⟨A, a, hA, _, ha, _⟩ := CochainComplex.exists_isKFlatResolution K
  obtain ⟨L, l, hL, _, hl, _⟩ := CochainComplex.exists_isKFlatResolution N
  have : QuasiIso a := ha
  have : QuasiIso l := hl
  have : QuasiIso q := hq
  have hIL : CochainComplex.IsKFlatTensor (R := R) (Ic.obj L) := by
    obtain ⟨J, hJ, hJmap, hJadd, _, _, hJres⟩ := exists_inverseImage_exact_kFlat f
    have heq : J = I := by
      exact CategoryTheory.Functor.ext hJ (fun _ _ b ↦ hJmap b)
    subst J
    exact (hJres l ⟨hl, hL⟩).2
  let := (SheafOfModules.tensorClosed R).2.1.some
  let T := (curriedTensor (SheafOfModules.{u} B)).map₂CochainComplex
  have hua : QuasiIso (Uc.map a) := inferInstance
  have hqa := kFlat_tensor_right_of_quasiIso (Uc.map a) hua hIL
  have hqq := kFlat_tensor_right_of_quasiIso q hq hIL
  have hll := kFlat_tensor_left_of_quasiIso (Ic.map l)
    (show QuasiIso (Ic.map l) from inferInstance) hP
  have : QuasiIso ((T.map (Uc.map a)).app (Ic.obj L)) := hqa
  have : QuasiIso ((T.map q).app (Ic.obj L)) := hqq
  have : QuasiIso ((T.obj P).map (Ic.map l)) := hll
  let es := (HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).app F
  let et := ((T.obj P).mapIso es)
  obtain ⟨emodel⟩ := relativeTensorPullback_kFlat_model f A hA L hL i
  let ea : DerivedCategory.Q.obj A ≅ E := asIso (DerivedCategory.Q.map a) ≪≫ eK
  let el : DerivedCategory.Q.obj L ≅ (DerivedCategory.singleFunctor _ 0).obj F :=
    asIso (DerivedCategory.Q.map l)
  let ed := (tensorLeft (DerivedCategory.Q.obj A)).mapIso
    ((derivedPullback f).mapIso el) ≪≫
      (tensorRight ((derivedPullback f).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))).mapIso ea
  let eh := (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapIso
    ((DerivedCategory.homologyFunctor _ i).mapIso ed)
  exact ⟨eh.symm ≪≫ emodel ≪≫ V.mapIso
    (isoOfQuasiIsoAt ((T.map (Uc.map a)).app (Ic.obj L)) i ≪≫
      (isoOfQuasiIsoAt ((T.map q).app (Ic.obj L)) i).symm ≪≫
      isoOfQuasiIsoAt ((T.obj P).map (Ic.map l)) i ≪≫
      (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso et)⟩

end AlgebraicGeometry.Scheme
