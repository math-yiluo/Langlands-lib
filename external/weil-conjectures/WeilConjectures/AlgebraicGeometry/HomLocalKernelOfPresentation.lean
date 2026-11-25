/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Internal Hom kernel models from a specified local presentation -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.Scheme.Modules

-- Keep the slice-site structures folded during instance synthesis and transport.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A specified presentation on V gives a finite-sum Hom kernel on that same open.
Source: Stacks Project, Modules, Lemmas 01CO (1), 01CQ, and the proof of 01CP;
Sites, Modules, Lemma 0E8H for restriction of internal Hom.
(blueprint: lem-weil-pbc-coherent-hom-local-kernel-from-presentation).

Proof:
On the slice site, let H be internal Hom into F.over V, contravariant in its source.
The symmetric monoidal closed structure identifies H with the contravariant internal
Hom functor, so H preserves equalizers. The opposite of the cokernel cofork of a is
therefore carried to a limiting kernel fork. Its cone point is H(cokernel a), and the
specified isomorphism e identifies this point with Hom(G.over V, F.over V).
Additivity gives H(sum of units) as the sum of the H(unit), and homObjUnitIso
identifies each H(unit) with F.over V. Conjugate H(a.op) by these isomorphisms to
obtain alpha, and use kernel.mapIso to transport its kernel. The isomorphism
overHomObjIso identifies its source with (homObj G F).over V. Finally overEquiv V
preserves kernels and finite biproducts, while overFunctorEquiv identifies the images
of restrictions with scheme restriction. Conjugating the image of alpha gives the
required map between the stated sums of F.restrict V.ι. Compose the kernel and
restriction isomorphisms to obtain the conclusion. These universal properties also
apply to empty sums and the empty open; no coherence hypothesis is used. -/
theorem homObj_locally_kernel_of_local_presentation
    (X : Scheme.{u}) (G F : X.Modules) (V : X.Opens) (m n : ℕ)
    (a : (⨁ fun _ : Fin m ↦ (SheafOfModules.unit X.ringCatSheaf).over V) ⟶
      (⨁ fun _ : Fin n ↦ (SheafOfModules.unit X.ringCatSheaf).over V))
    (e : (cokernel a) ≅ G.over V) :
    ∃ (α : (⨁ fun _ : Fin n ↦ F.restrict V.ι) ⟶
      (⨁ fun _ : Fin m ↦ F.restrict V.ι)),
      Nonempty ((restrictFunctor V.ι).obj
        (SheafOfModules.homObj (R := X.sheaf) G F) ≅ kernel α) := by
  have : HasSheafify ((Opens.grothendieckTopology X).over V)
      AddCommGrpCat.{u} := inferInstance
  have : ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  let R := X.sheaf.over V
  let M : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R) := F.over V
  have : Abelian (SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) := inferInstance
  have : HasFiniteBiproducts (SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) := inferInstance
  let U : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R) :=
    (SheafOfModules.unit X.ringCatSheaf).over V
  let H := (SheafOfModules.homFunctor R).flip.obj M
  have : PreservesLimitsOfShape WalkingParallelPair H := by
    let := SheafOfModules.monoidalCategory (R := R)
    let := SheafOfModules.symmetricCategory (R := R)
    let := SheafOfModules.monoidalClosed (R := R)
    let K : (SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))ᵒᵖ ⥤
        SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R) :=
      MonoidalClosed.internalHom.flip.obj M
    let i : K ≅ H := NatIso.ofComponents
      (fun A ↦ eqToIso (SheafOfModules.ihom_obj (R := R) A.unop M))
      (fun f ↦ by
        change (MonoidalClosed.pre f.unop).app M ≫ 𝟙 _ =
          𝟙 _ ≫ SheafOfModules.homObjMap (R := R) f.unop (𝟙 M)
        simpa only [Category.comp_id, Category.id_comp] using
          (SheafOfModules.pre_app (R := R) f.unop M))
    exact preservesLimitsOfShape_of_natIso i
  let hn : H.obj (Opposite.op
      (⨁ fun _ : Fin n ↦ U)) ≅
      (⨁ fun _ : Fin n ↦ M) := H.opMapBiproductIso
      (fun _ : Fin n ↦ U) ≪≫
    biproduct.mapIso (fun _ ↦ SheafOfModules.homObjUnitIso M)
  let hm : H.obj (Opposite.op
      (⨁ fun _ : Fin m ↦ U)) ≅
      (⨁ fun _ : Fin m ↦ M) := H.opMapBiproductIso
      (fun _ : Fin m ↦ U) ≪≫
    biproduct.mapIso (fun _ ↦ SheafOfModules.homObjUnitIso M)
  let α : (⨁ fun _ : Fin n ↦ M) ⟶ (⨁ fun _ : Fin m ↦ M) :=
    hn.inv ≫ H.map a.op ≫ hm.hom
  have hk := CokernelCofork.IsColimit.ofπOp (cokernel.π a)
    (cokernel.condition a) (cokernelIsCokernel a)
  have hk' := isLimitForkMapOfIsLimit' H _ hk
  let ei₀ : H.obj (Opposite.op (cokernel a)) ≅ kernel (H.map a.op) :=
    IsLimit.conePointUniqueUpToIso hk' (limit.isLimit _)
  let ei : H.obj (Opposite.op (G.over V)) ≅ kernel (H.map a.op) :=
    H.mapIso e.op ≪≫ ei₀
  let ek : kernel (H.map a.op) ≅ kernel α :=
    kernel.mapIso (H.map a.op) α hn hm (by exact (hn.hom_inv_id_assoc _).symm)
  have : HasLimits V.toScheme.Modules := inferInstance
  let T : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R) ⥤ V.toScheme.Modules :=
    (overEquiv V).functor
  have : T.IsEquivalence := inferInstanceAs (overEquiv V).functor.IsEquivalence
  have : PreservesBiproductsOfShape (Fin n) T :=
    preservesBiproductsOfShape_of_preservesProductsOfShape T
  have : PreservesBiproductsOfShape (Fin m) T :=
    preservesBiproductsOfShape_of_preservesProductsOfShape T
  let tn : T.obj (⨁ fun _ : Fin n ↦ M) ≅ (⨁ fun _ : Fin n ↦ F.restrict V.ι) :=
    T.mapBiproduct (fun _ : Fin n ↦ M) ≪≫
    biproduct.mapIso (fun _ ↦ (overFunctorEquiv V).app F)
  let tm : T.obj (⨁ fun _ : Fin m ↦ M) ≅ (⨁ fun _ : Fin m ↦ F.restrict V.ι) :=
    T.mapBiproduct (fun _ : Fin m ↦ M) ≪≫
    biproduct.mapIso (fun _ ↦ (overFunctorEquiv V).app F)
  let β : (⨁ fun _ : Fin n ↦ F.restrict V.ι) ⟶
      (⨁ fun _ : Fin m ↦ F.restrict V.ι) := tn.inv ≫ T.map α ≫ tm.hom
  have : HasLimit (parallelPair (C := V.toScheme.Modules) β 0) :=
    HasLimitsOfShape.has_limit _
  let es : T.obj ((SheafOfModules.homObj (R := X.sheaf) G F).over V) ≅
      T.obj (kernel α) :=
    T.mapIso (SheafOfModules.overHomObjIso G F V ≪≫ ei ≪≫ ek)
  let et : T.obj (kernel α) ≅ kernel (C := V.toScheme.Modules) β :=
    PreservesKernel.iso T α ≪≫
      kernel.mapIso (T.map α) β tn tm (by exact (tn.hom_inv_id_assoc _).symm)
  refine ⟨β, ⟨?_⟩⟩
  exact ((overFunctorEquiv V).app (SheafOfModules.homObj (R := X.sheaf) G F)).symm ≪≫
    es ≪≫ et

end AlgebraicGeometry.Scheme.Modules
