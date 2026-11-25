/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

/-! # Free Yoneda and extension-by-zero module sheaves

Source: Stacks Project, Modules on Sites, Tag 03DI.
(blueprint: lem-pc-scheme-module-free-yoneda-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The sheafification of the free module on the representable of an open agrees
with the sheafification of the explicit extension-by-zero presheaf of its unit.
Source: Stacks Project, Modules on Sites, Tag 03DI, construction of j_U! O_U.
(blueprint: lem-pc-scheme-module-free-yoneda-iso).

Proof: at an open V, both presheaves have the free O_X(V)-module with basis the
set of morphisms V to U. In the explicit extension-by-zero construction the
summand associated to a morphism is the unit of the localized ring, whose value
is O_X(V). Send each basis vector of the free-module encoding to the unit in
that summand of the direct sum; the inverse sends a finitely supported family
of coefficients to its linear combination of basis vectors. These are inverse
linear maps. Restriction along W to V sends the basis indexed by V to U to the
basis indexed by the composite W to U, and restricts the scalar in both
constructions. The linear isomorphisms therefore form a presheaf isomorphism.
Apply module sheafification to this isomorphism. When there is no morphism V
to U both values are zero, so the construction includes the empty open and
empty scheme without exceptions. -/
theorem schemeModule_freeYoneda_iso (U : X.Opens) :
    Nonempty
      (((PresheafOfModules.sheafification (𝟙 (moduleRings X.toRingedSpace).obj)).obj
        ((PresheafOfModules.free (moduleRings X.toRingedSpace).obj).obj
          (yoneda.obj U))) ≅
        ((PresheafOfModules.sheafification (𝟙 (moduleRings X.toRingedSpace).obj)).obj
          ((SheafOfModules.extensionByZeroPresheaf (moduleRings X.toRingedSpace) U).obj
            (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U))))) := by
  classical
  let R := moduleRings X.toRingedSpace
  let e : (PresheafOfModules.free R.obj).obj (yoneda.obj U) ≅
      (SheafOfModules.extensionByZeroPresheaf R U).obj
        (SheafOfModules.unit (R.over U)) :=
    PresheafOfModules.isoMk
      (fun V ↦ (finsuppLequivDFinsupp (ι := V.unop ⟶ U) (R.obj.obj V)).toModuleIso)
      (by
        intro V W a
        apply ModuleCat.free_hom_ext
        intro φ
        dsimp [PresheafOfModules.free, PresheafOfModules.freeObj,
          SheafOfModules.extensionByZeroPresheaf,
          SheafOfModules.extensionByZeroPresheafObj,
          SheafOfModules.extensionByZeroPresheafMap]
        rw [ModuleCat.freeDesc_apply]
        simp only [LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
        change Finsupp.toDFinsupp (ModuleCat.freeMk (R := R.obj.obj W) (a.unop ≫ φ)) =
          SheafOfModules.extensionByZeroPresheafRestrictAdd R U
            (SheafOfModules.unit (R.over U)) a
              (Finsupp.toDFinsupp (ModuleCat.freeMk (R := R.obj.obj V) φ))
        simp only [ModuleCat.freeMk, Finsupp.toDFinsupp_single]
        change DirectSum.of _ (a.unop ≫ φ) (1 : R.obj.obj W) =
          SheafOfModules.extensionByZeroPresheafRestrictAdd R U
            (SheafOfModules.unit (R.over U)) a (DirectSum.of _ φ (1 : R.obj.obj V))
        let : DecidableEq (V.unop ⟶ U) := Classical.decEq _
        let : DecidableEq (W.unop ⟶ U) := Classical.decEq _
        dsimp [SheafOfModules.extensionByZeroPresheafRestrictAdd,
          SheafOfModules.unit, PresheafOfModules.unit]
        erw [DirectSum.toAddMonoid_of]
        erw [AddMonoidHom.comp_apply]
        congr 1
        · congr 1
          exact Subsingleton.elim _ _
        · exact ((R.over U).obj.map
            (Opposite.op (Over.homMk a.unop :
              Over.mk (a.unop ≫ φ) ⟶ Over.mk φ))).hom.map_one.symm)
  exact ⟨(PresheafOfModules.sheafification (𝟙 R.obj)).mapIso e⟩

end AlgebraicGeometry
