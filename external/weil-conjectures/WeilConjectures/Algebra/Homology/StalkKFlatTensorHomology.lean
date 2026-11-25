/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.Algebra.Homology.TensorRestrictExtendScalars
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.StalkTensorComplex
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # K-flat tensor homology at a stalk, with transported scalars

(blueprint: lem-pc-stalk-kflat-tensor-homology).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem stalk_additive (Z : RingedSpace.{u}) (x : Z) :
    (RingedSpace.moduleStalkFunctor Z x).Additive := by
  constructor
  intro M N f g
  ext m
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map (f + g).val) m = _
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map (f.val + g.val)) m = _
  rw [Functor.map_add, Functor.map_add]
  rfl

private theorem stalk_preservesHomology (Z : RingedSpace.{u}) (x : Z) :
    (RingedSpace.moduleStalkFunctor Z x).PreservesHomology := by
  let := stalk_additive Z x
  apply ((RingedSpace.moduleStalkFunctor Z x).exact_tfae.out 2 3).mp
  intro C hC
  exact ((RingedSpace.module_stalk_exact Z C.f).2.2.2.2
    C.X₃ C.f C.g C.zero).mp hC x

-- Specialize the tensor identity of Stacks Tag 06Y1 to an isomorphism. Restriction
-- is fully faithful, so the extension/restriction adjunction counit is invertible.
private theorem ringIso_tensor_complex_iso
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (P L : CochainComplex (ModuleCat.{u} B) ℤ) :
    let T := (ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)
    Nonempty (T.obj (CochainComplex.mapBifunctor P L (curriedTensor _)) ≅
      CochainComplex.mapBifunctor (T.obj P) (T.obj L) (curriedTensor _)) := by
  let T := (ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)
  let adj := ModuleCat.extendRestrictScalarsAdj e.toRingHom
  have : (ModuleCat.extendScalars e.toRingHom).Additive :=
    adj.left_adjoint_additive
  let d := (Functor.mapHomologicalComplexCompIso (asIso adj.counit) (.up ℤ)).app L ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} B) (.up ℤ)).app L
  let b := ((curriedTensor (ModuleCat.{u} B)).map₂CochainComplex.obj P).mapIso d
  obtain ⟨t⟩ := CochainComplex.nonempty_tensorRestrictExtendScalarsIso e.toRingHom P (T.obj L)
  exact ⟨T.mapIso b.symm ≪≫ t⟩


private theorem kFlat_of_acyclic_tensor
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N P (curriedTensor _))).2 (hP N hN)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

private theorem ringIso_kFlat
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (P : CochainComplex (ModuleCat.{u} B) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} B) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj P) := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u} e
  let T := E.functor.mapHomologicalComplex (.up ℤ)
  apply kFlat_of_acyclic_tensor
  intro L hL
  let L' := (E.inverse.mapHomologicalComplex (.up ℤ)).obj L
  have hL' : L'.Acyclic := fun i ↦ (hL i).map E.inverse
  have h : (T.obj (CochainComplex.mapBifunctor L' P (curriedTensor _))).Acyclic :=
    fun i ↦ (hP L' hL' i).map E.functor
  obtain ⟨c⟩ := ringIso_tensor_complex_iso e L' P
  let d := (E.mapHomologicalComplex (.up ℤ)).counitIso.app L
  let t := (((curriedTensor _).map₂CochainComplex).mapIso d).app (T.obj P)
  exact fun i ↦ (h i).of_iso (c ≪≫ t)

/-- A K-flat sheaf complex computes tensor homology after transporting its stalk ring.
Source: Stacks Project, Cohomology of Sheaves, Tags 06YB, 08CG and 09U9;
Modules Tag 01AG.
Proof: the stalk criterion makes the stalk of P K-flat. Restriction along the ring
isomorphism e is an exact tensor equivalence, so it preserves K-flatness. Stalks
commute with the direct sums and tensor differentials in the total complex and
with the degree-zero single complex. Exactness of stalks and scalar restriction
identifies homology with homology of this transported total tensor. The K-flat
comparison for derived tensor identifies Q of that tensor with Q of the transported
stalk of P tensor Q of the single transported stalk of F. The latter Q-single is
the derived single functor. Apply degree-i homology and forget scalars. No replacement
of P or choice of a module is made: the module is the image of F under S.
The argument applies to zero rings, zero modules and unbounded complexes.
(blueprint: lem-pc-stalk-kflat-tensor-homology). -/
theorem stalk_kFlat_tensor_homology_iso
    (Z : RingedSpace.{u}) (x : Z) (A : CommRingCat.{u})
    (e : A ≅ Z.presheaf.stalk x)
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Z.sheaf) P) :
    let S := RingedSpace.moduleStalkFunctor Z x ⋙ ModuleCat.restrictScalars e.hom.hom
    ∀ (F : SheafOfModules.{u} (moduleRings Z)) (i : ℤ),
      Nonempty ((TopCat.Sheaf.forget AddCommGrpCat.{u} Z.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
          ((SheafOfModules.toSheaf _).obj
            ((CochainComplex.mapBifunctor P
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
              (@MonoidalCategory.curriedTensor _ _
                (SheafOfModules.monoidalCategory Z.sheaf))).homology i)) ≅
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            (DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj P) ⊗
              (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (S.obj F)))) := by
  classical
  dsimp only
  let T := RingedSpace.moduleStalkFunctor Z x
  let U := ModuleCat.restrictScalars e.hom.hom
  let S := T ⋙ U
  let TC := T.mapHomologicalComplex (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let SC := S.mapHomologicalComplex (.up ℤ)
  let := stalk_additive Z x
  have hPx := (RingedSpace.isKFlat_iff_stalk_isKFlat Z P).mp hP x
  have hk := ringIso_kFlat e.commRingCatIsoToRingEquiv (TC.obj P) hPx
  intro F i
  let K := CochainComplex.mapBifunctor P
    ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
    (@curriedTensor _ _ (SheafOfModules.monoidalCategory Z.sheaf))
  let L := (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (S.obj F)
  let R := CochainComplex.mapBifunctor (SC.obj P) L (curriedTensor _)
  let := stalk_preservesHomology Z x
  have : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  let := SheafOfModules.monoidalCategory Z.sheaf
  obtain ⟨t, _⟩ := CochainComplex.exists_stalk_tensor_complex_iso Z x
  obtain ⟨r⟩ := ringIso_tensor_complex_iso
    e.commRingCatIsoToRingEquiv (TC.obj P)
      (TC.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj F))
  let s := (HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app F
  let b := ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.obj
    (SC.obj P)).mapIso s
  let a : SC.obj K ≅ R := UC.mapIso (t P _) ≪≫ r ≪≫ b
  let c : S.obj (K.homology i) ≅ R.homology i :=
    ((K.sc i).mapHomologyIso S).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso a
  let d : DerivedCategory.Q.obj (SC.obj P) ⊗
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (S.obj F) ≅
      DerivedCategory.Q.obj R :=
    whiskerLeftIso _ ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (S.obj F)) ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft (SC.obj P) L hk
  exact ⟨(forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapIso
    (c ≪≫ ((DerivedCategory.homologyFunctorFactors _ i).app R).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso d.symm)⟩
