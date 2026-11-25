/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
The construction is the mate of the inverse canonical base-change square, using only
the supplied direct-image/right-adjoint adjunctions. No auxiliary pullback adjunction
or derived-pullback counit is chosen by this definition.

# Canonical base-change map for a right adjoint

Source: literature/stacks-project/duality.tex, Tag 0AA8 (Lemma 48.6.2),
equation-base-change-map (blueprint: def-sc-duality-equation-base-change-map).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- The canonical right-adjoint base-change morphism `Lg_X^* a(K) ⟶ a'(Lg^* K)` of a
cartesian square of quasi-compact and quasi-separated schemes `X' = X ×_Y Y'`, with
`g_X = pullback.fst f g : X' ⟶ X` and `f' = pullback.snd f g : X' ⟶ Y'`.

`a` and `a'` are right adjoints (`adjf`, `adjf'`) of the derived direct images
`Rf_*`, `Rf'_*` restricted to the quasi-coherent derived categories
(`schemeDerivedDirectImage_qcqs_hasRightAdjoint` gives the preservation of `D_QCoh`).
`β : Lg^* Rf_* ⟶ Rf'_* Lg_X^*` is the canonical base-change transformation
`schemeDerivedBaseChangeMap` (def-pc-derived-base-change-map) on `D_QCoh(X)`, assumed to
be an isomorphism (`hβ`). The adjunctions `Lg^* ⊣ Rg_*`, `Lg_X^* ⊣ Rg_{X,*}` are the
canonical ones of `exists_schemeDerivedAdjunction` (the ones `β` is built from), restricted
to `D_QCoh` (`derivedPullback_tensor_preserve_QCoh` and
`schemeDerivedDirectImage_qcqs_hasRightAdjoint` give the preservation). The conjugate
`θ : Rg_{X,*} a' ⟶ a Rg_*` of `β` for the composite adjunctions is an isomorphism, and
the map is `Lg_X^* a(η'_K) ≫ Lg_X^* (θ_{Lg^* K})⁻¹ ≫ ε_{a'(Lg^* K)}`.
We compute it directly as the mate of `β⁻¹` under `adjf` and `adjf'`. The iterated
mates identity identifies this with the displayed composite for any auxiliary
pullback/direct-image adjunctions. Thus no such auxiliary choice is part of the data.
Source: Stacks Project, duality.tex, Tag 0AA8, equation-base-change-map
(blueprint: def-sc-duality-equation-base-change-map). -/
noncomputable def dualityEquationBaseChangeMap
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y) :
    ((schemeDerivedQCohProperty (pullback f g)).lift
        ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f g))
        (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1
          E.obj E.property)).obj (a.obj K) ⟶
      a'.obj (((schemeDerivedQCohProperty Y').lift
        ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
        (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)).obj K) :=
  let PX := schemeDerivedQCohProperty X
  let PY := schemeDerivedQCohProperty Y
  let PY' := schemeDerivedQCohProperty Y'
  let PX' := schemeDerivedQCohProperty (pullback f g)
  let Lg := PY'.lift (PY.ι ⋙ derivedPullback g)
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)
  let LgX := PX'.lift (PX.ι ⋙ derivedPullback (pullback.fst f g))
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1 E.obj E.property)
  let Rf := PY.lift (PX.ι ⋙ schemeDerivedDirectImage f)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst E.obj E.property)
  let Rf' := PY'.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.snd f g))
    (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
      (pullback.snd f g) _ _).fst E.obj E.property)
  let β : Rf ⋙ Lg ⟶ LgX ⋙ Rf' :=
    { app := fun E ↦ ObjectProperty.homMk
        (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition E.obj)
      naturality := fun E F φ ↦ by
        ext
        have gen : ∀ (adj' : derivedPullback (pullback.snd f g) ⊣
              schemeDerivedDirectImage (pullback.snd f g))
            (adjF : derivedPullback f ⊣ schemeDerivedDirectImage f)
            (c1 : derivedPullback g ⋙ derivedPullback (pullback.snd f g) ≅
              derivedPullback (pullback.snd f g ≫ g))
            (c2 : derivedPullback f ⋙ derivedPullback (pullback.fst f g) ≅
              derivedPullback (pullback.fst f g ≫ f)),
            (derivedPullback g).map ((schemeDerivedDirectImage f).map φ.hom) ≫
              adj'.homEquiv _ _ (c1.hom.app ((schemeDerivedDirectImage f).obj F.obj) ≫
                eqToHom (congrArg (fun k => (derivedPullback k).obj
                  ((schemeDerivedDirectImage f).obj F.obj)) pullback.condition.symm) ≫
                c2.inv.app ((schemeDerivedDirectImage f).obj F.obj) ≫
                (derivedPullback (pullback.fst f g)).map (adjF.counit.app F.obj)) =
            adj'.homEquiv _ _ (c1.hom.app ((schemeDerivedDirectImage f).obj E.obj) ≫
                eqToHom (congrArg (fun k => (derivedPullback k).obj
                  ((schemeDerivedDirectImage f).obj E.obj)) pullback.condition.symm) ≫
                c2.inv.app ((schemeDerivedDirectImage f).obj E.obj) ≫
                (derivedPullback (pullback.fst f g)).map (adjF.counit.app E.obj)) ≫
              (schemeDerivedDirectImage (pullback.snd f g)).map
                ((derivedPullback (pullback.fst f g)).map φ.hom) := by
          intro adj' adjF c1 c2
          have key : ∀ (k k' : pullback f g ⟶ Y) (e : k = k')
              {A B : schemeDerivedCategory Y} (u : A ⟶ B)
              {Z : schemeDerivedCategory (pullback f g)}
              (r : (derivedPullback k').obj B ⟶ Z),
              (derivedPullback k).map u ≫
                  eqToHom (congrArg (fun k => (derivedPullback k).obj B) e) ≫ r =
                eqToHom (congrArg (fun k => (derivedPullback k).obj A) e) ≫
                  (derivedPullback k').map u ≫ r := by
            rintro k _ rfl A B u Z r; simp
          rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
          congr 1
          simp only [Category.assoc, ← Functor.map_comp]
          rw [Functor.map_comp, ← Functor.comp_map, NatTrans.naturality_assoc,
            key _ _ pullback.condition.symm, c2.inv.naturality_assoc, Functor.comp_map,
            ← Functor.map_comp, ← Functor.map_comp]
          erw [adjF.counit.naturality]
          rfl
        exact gen _ _ _ _ }
  have : ∀ E, IsIso (β.app E) := fun E ↦
    @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _ PY'.fullyFaithfulι _ _ (β.app E) (hβ E)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  -- The only inverse data used here is the inverse of the fixed base-change
  -- transformation; no fresh pullback adjunction or counit is selected.
  (mateEquiv adjf adjf' (inv β)).app K

end AlgebraicGeometry
