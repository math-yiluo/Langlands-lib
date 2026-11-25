/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.AffineDerivedSectionsTruncationIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Derived sections comparison on complexes of associated sheaves

Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5.
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

private theorem preservesKernel_of_iso_image
    {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (T : C ⥤ D) [T.Full] [T.Faithful] [T.PreservesZeroMorphisms]
    {M N : C} (f : M ⟶ N) [Limits.HasKernel (T.map f)]
    (L : C) (e : T.obj L ≅ Limits.kernel (T.map f)) :
    Limits.PreservesLimit (Limits.parallelPair f 0) T := by
  let t := T.preimage (e.hom ≫ Limits.kernel.ι (T.map f))
  have ht : t ≫ f = 0 := by
    apply T.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
      Category.assoc, Limits.kernel.condition, Limits.comp_zero, t]
  let c := Limits.KernelFork.ofι t ht
  have hc : Limits.IsLimit (c.map T) := by
    apply Limits.IsLimit.ofIsoLimit (Limits.kernelIsKernel (T.map f))
    exact Limits.Fork.ext e.symm (by simp [c, t, Limits.KernelFork.map])
  have hc' : Limits.IsLimit c :=
    Limits.isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
  exact Limits.preservesLimit_of_preserves_limit_cone hc'
    ((c.isLimitMapConeEquiv T).symm hc)

/-- The comparison from termwise sections to derived sections is invertible on
an arbitrary complex of associated sheaves.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5, module calculation.
(blueprint: new-affine-tilde-derived-sections-unit-isIso).

Proof: Write T for associated sheaf and S for affine sections with scalar transport.
Full faithfulness of T lifts the kernel of a map between associated sheaves back to
modules: the kernel is quasi-coherent, so its ordinary counit is invertible. Reflect
this limit fork through T. Thus T preserves kernels, and as an additive left adjoint
it is exact. Affine vanishing shows that quasi-coherent sheaves are S-acyclic: forget
to abelian groups, apply affine vanishing, and use the exact-functor derived comparison
to reflect vanishing back to modules. In particular T sends injective modules to
S-acyclic sheaves. The bounded-below acyclic-complex theorem therefore makes the unit
of the bounded-below derived adjunction invertible. Restrict the unbounded adjunction
along the full inclusions of the bounded-below categories. Compatibility of the two
derived functors and uniqueness of right adjoints transport this invertibility to
the unbounded adjunction on bounded-below objects.
For an arbitrary derived module P and degree n, use P -> truncGE n P. Exact T
commutes with this truncation, and T(P) has quasi-coherent cohomology. The affine
sections truncation theorem makes H^n(RS(T(P -> truncGE n P))) invertible. H^n of the
module truncation projection is also invertible, and the unit on truncGE n P is
invertible by the bounded-below calculation. Naturality of the unit and two-out-of-
three now make H^n of the unit on P invertible. The derived homology criterion gives
invertibility of this unit in every degree. Finally, the derived-adjunction unit
formula on Qh(K) factors this invertible map, followed by the image of the exact
functor comparison, as the ordinary homotopy unit followed by the displayed
right-derived-functor comparison. The ordinary unit is invertible because T is fully
faithful, so cancellation proves the claim. No boundedness is imposed on K. For the
zero ring or zero complex the relevant maps are between zero objects, and all these
arguments still apply. The additive instance is only needed to spell the homotopy
functor and is available because T preserves biproducts. -/
theorem affineTildeDerivedSectionsUnit_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [(tilde.functor (.of A)).Additive]
    (K : HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ)) :
    IsIso ((RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctorUnit.app
        (((tilde.functor (.of A)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) := by
  let X := Spec (.of A)
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom
  let V := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  let SV := S ⋙ V
  let : HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _
  have hacyclic (M : C) (hM : M.IsQuasicoherent) : S.rightAcyclic M := by
    intro q
    have := hM
    have : Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace (q + 1) ⊤).obj M) :=
      subsingleton_openModuleCohomology_of_isAffineOpen X M ⊤ (isAffineOpen_top X) (q + 1)
        (by omega)
    have hz : Limits.IsZero ((SV.rightDerived (q + 1)).obj M) := by
      change Limits.IsZero
        ((RingedSpace.openModuleCohomology X.toRingedSpace (q + 1) ⊤).obj M)
      exact AddCommGrpCat.isZero_of_subsingleton _
    let P := (DerivedCategory.singleFunctor C 0).obj M
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((q + 1 : ℕ) : ℤ)
    let e : SV.rightDerivedFunctor ⋙ H ≅
        S.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) ((q + 1 : ℕ) : ℤ) ⋙ V :=
      Functor.isoWhiskerRight (S.rightDerivedFunctorCompMapDerivedCategoryIso V) H ≪≫
        Functor.isoWhiskerLeft S.rightDerivedFunctor
          (V.mapDerivedCategoryHomologyFunctorIso ((q + 1 : ℕ) : ℤ)).symm
    have hz' := hz.of_iso
      (SV.homologyRightDerivedFunctorObjSingleFunctorIso M (q + 1))
    have hz'' := hz'.of_iso (e.app P).symm
    have hz''' := hz''.of_iso
      (V.mapIso (S.homologyRightDerivedFunctorObjSingleFunctorIso M (q + 1))).symm
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply V.map_injective
    exact hz'''.eq_of_src _ _
  let T : ModuleCat.{u} A ⥤ C := tilde.functor (.of A)
  let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
  let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := .of A)
  let : T.Full := ff.full
  let : T.Faithful := ff.faithful
  let : ∀ {P Q : ModuleCat.{u} A} (f : P ⟶ Q),
      Limits.PreservesLimit (Limits.parallelPair f 0) T := by
    intro P Q f
    have : (T.obj P).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) P).IsQuasicoherent
      infer_instance
    have : (T.obj Q).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) Q).IsQuasicoherent
      infer_instance
    let k := Limits.kernel (T.map f)
    have : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) k) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) k
    exact preservesKernel_of_iso_image T f
      ((moduleSpecΓFunctor (R := .of A)).obj k)
      (asIso (Scheme.Modules.fromTildeΓ (R := .of A) k))
  let : Limits.PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesKernels T
  have : Limits.PreservesFiniteLimits S := by
    dsimp [S, RingedSpace.globalSectionsFunctor]
    infer_instance
  let b : T ⊣ S := tilde.adjunction (R := .of A)
  let a := b.mapDerivedCategoryRightDerivedAdjunction
  have hplus (P : DerivedCategory.Plus (ModuleCat.{u} A)) :
      IsIso (b.derivedPlus.unit.app P) := by
    apply b.isIso_derivedPlus_unit_app_of_rightAcyclic
    · intro I _
      infer_instance
    · intro I _
      apply hacyclic
      change (tilde.{u} (R := .of A) I).IsQuasicoherent
      infer_instance
  let ap := a.restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := ModuleCat.{u} A)))
    (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := C)))
    T.mapDerivedCategoryPlusCompatibility.symm S.rightDerivedFunctorPlusCompatibility.symm
  have hap (P : DerivedCategory.Plus (ModuleCat.{u} A)) : IsIso (ap.unit.app P) := by
    have := hplus P
    rw [← b.derivedPlus.unit_rightAdjointUniq_hom_app ap P]
    infer_instance
  have hbounded (P : DerivedCategory.Plus (ModuleCat.{u} A)) :
      IsIso (a.unit.app P.obj) := by
    have := hap P
    have h := a.map_restrictFullyFaithful_unit_app
      (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := ModuleCat.{u} A)))
      (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := C)))
      T.mapDerivedCategoryPlusCompatibility.symm S.rightDerivedFunctorPlusCompatibility.symm P
    exact IsIso.of_isIso_fac_right h.symm
  have hunit (P : DerivedCategory (ModuleCat.{u} A)) : IsIso (a.unit.app P) := by
    apply (DerivedCategory.isIso_iff _ _).2
    intro n
    let HA := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
    let tA := DerivedCategory.TStructure.t (C := ModuleCat.{u} A)
    let tC := DerivedCategory.TStructure.t (C := C)
    let π := (tA.truncGEπ n).app P
    let Q : DerivedCategory.Plus (ModuleCat.{u} A) :=
      ⟨(tA.truncGE n).obj P, ⟨n, inferInstance⟩⟩
    have := hbounded Q
    have : IsIso (HA.map π) :=
      DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app P n n le_rfl
    have hqc : schemeDerivedQCohProperty X (T.mapDerivedCategory.obj P) := by
      intro i
      let e := (T.mapDerivedCategoryHomologyFunctorIso i).app P
      apply (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso e
      change (tilde.{u} (R := .of A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P)).IsQuasicoherent
      infer_instance
    have htr := affineDerivedSections_truncGE_isIso A ⟨T.mapDerivedCategory.obj P, hqc⟩ n
    let e := (T.mapDerivedCategoryTruncGEIso n).app P
    have : (T.mapDerivedCategory.obj ((tA.truncGE n).obj P)).IsGE n :=
      T.isGE_mapDerivedCategory_obj _ n
    have hfac := tC.π_descTruncGE (T.mapDerivedCategory.map π) n
    change (tC.truncGEπ n).app (T.mapDerivedCategory.obj P) ≫ e.inv =
      T.mapDerivedCategory.map π at hfac
    have hπ : IsIso (HA.map (S.rightDerivedFunctor.map (T.mapDerivedCategory.map π))) := by
      rw [← hfac, Functor.map_comp, Functor.map_comp]
      infer_instance
    have hnat := HA.congr_map (a.unit.naturality π)
    simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hnat
    exact IsIso.of_isIso_fac_right hnat.symm
  have := hunit (DerivedCategory.Qh.obj K)
  have hfac := (b.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    T.mapDerivedCategoryFactorsh.hom S.rightDerivedFunctorUnit K
  change a.unit.app (DerivedCategory.Qh.obj K) ≫
    S.rightDerivedFunctor.map (T.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map ((b.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K) ≫
        S.rightDerivedFunctorUnit.app ((T.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
    at hfac
  exact IsIso.of_isIso_fac_left hfac.symm

end AlgebraicGeometry
