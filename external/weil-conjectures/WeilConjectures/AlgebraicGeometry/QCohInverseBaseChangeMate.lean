/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The inverse ordinary base-change square on quasi-coherent derived categories

Source: Stacks Project, Tag 0AA6, equation-base-change-map.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem secondMate_formula
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {Rf : C ⥤ D} {a : D ⥤ C} {Rf' : E ⥤ F} {a' : F ⥤ E}
    {Lx : C ⥤ E} {Rx : E ⥤ C} {Lg : D ⥤ F} {Rg : F ⥤ D}
    (adjf : Rf ⊣ a) (adjf' : Rf' ⊣ a') (adjx : Lx ⊣ Rx) (adjg : Lg ⊣ Rg)
    (β : Rf ⋙ Lg ⟶ Lx ⋙ Rf') [IsIso β] (K : D) :
    Lx.map (a.map (adjg.unit.app K)) ≫
      Lx.map (inv ((conjugateEquiv (adjx.comp adjf') (adjf.comp adjg) β).app
        (Lg.obj K))) ≫ adjx.counit.app (a'.obj (Lg.obj K)) =
      (mateEquiv adjf adjf' (inv β)).app K := by
  have hi : inv (conjugateEquiv (adjx.comp adjf') (adjf.comp adjg) β) =
      conjugateEquiv (adjf.comp adjg) (adjx.comp adjf') (inv β) :=
    IsIso.inv_eq_of_hom_inv_id (conjugateEquiv_comm _ _ (by simp))
  have hm := iterated_mateEquiv_conjugateEquiv adjf adjf' adjx adjg (inv β)
  have h := congrArg (fun τ ↦ ((mateEquiv adjg adjx).symm τ).app K) hm
  rw [Equiv.symm_apply_apply] at h
  rw [← hi] at h
  simpa [mateEquiv] using h.symm

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Derived pullback restricted to quasi-coherent objects. 
(blueprint: lem-sc-duality-base-change-inverse-square-mate)
-/
noncomputable abbrev qcPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (schemeDerivedQCohProperty X).lift
    ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f)
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh f).1 E.obj E.property)

/-- Derived direct image restricted to quasi-coherent objects. 
(blueprint: lem-sc-duality-base-change-inverse-square-mate)
-/
noncomputable abbrev qcDirectImage {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) :=
  (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst E.obj E.property)

/-- The ordinary base-change transformation on the full quasi-coherent subcategories. 
(blueprint: lem-sc-duality-base-change-inverse-square-mate)
-/
noncomputable def qcBaseChange {X Y S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : S ⟶ Y) :
    qcDirectImage f ⋙ qcPullback g ⟶
      qcPullback (pullback.fst f g) ⋙
        @qcDirectImage _ _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _
          (pullback.snd f g) :=
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

/-- The inverse ordinary base-change square. 
(blueprint: lem-sc-duality-base-change-inverse-square-mate)
-/
noncomputable def qcInverseBaseChange {X Y S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : S ⟶ Y)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj)) :
    TwoSquare (qcPullback (pullback.fst f g)) (qcDirectImage f)
      (@qcDirectImage _ _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _
        (pullback.snd f g)) (qcPullback g) := by
  let β := qcBaseChange f g
  have : ∀ E, IsIso (β.app E) := fun E ↦
    @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
      (schemeDerivedQCohProperty S).fullyFaithfulι _ _ (β.app E) (hβ E)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  exact inv β

/-- The fixed second mate is the mate of the inverse ordinary base-change square.
Source: Stacks Project, Tag 0AA6, equation-base-change-map.
(blueprint: lem-sc-duality-base-change-inverse-square-mate)

Proof: Restrict the pinned pullback/direct-image adjunctions to the full
quasi-coherent subcategories. Apply the iterated mates identity to the ordinary
base-change transformation: its iterated mate is its conjugate under the two
composite adjunctions. Conjugation carries the inverse ordinary transformation
to the inverse conjugate. Taking its inverse mate under the two pullback
adjunctions gives pullback of a applied to the base unit, followed by pullback
of the inverse conjugate, followed by the upper counit. This is precisely the
fixed definition. The other order of the same iterated mates correspondence
is the mate of the inverse ordinary square under the direct-image/right-adjoint
adjunctions. Thus their components agree, with no assumption on invertibility
of the second mate. The argument is valid also for zero objects and empty schemes. -/
theorem dualityEquationBaseChangeMap_eq_inverseSquareMate
    {X Y Y' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y' ⟶ Y)
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
    dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K =
      (mateEquiv adjf adjf' (qcInverseBaseChange f g hβ)).app K := by
  classical
  have : ∀ E, IsIso ((qcBaseChange f g).app E) := fun E ↦
    @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
      (schemeDerivedQCohProperty Y').fullyFaithfulι _ _ ((qcBaseChange f g).app E) (hβ E)
  have : IsIso (qcBaseChange f g) := NatIso.isIso_of_isIso_app _
  unfold dualityEquationBaseChangeMap
  rfl

end AlgebraicGeometry
