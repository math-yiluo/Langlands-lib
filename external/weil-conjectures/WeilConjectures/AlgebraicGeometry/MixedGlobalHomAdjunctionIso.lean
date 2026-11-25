/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.MixedHomDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.QCqsSheafRHomAdjunction
import WeilConjectures.AlgebraicGeometry.DQCoheratorAdjunction
import WeilConjectures.AlgebraicGeometry.DQCoheratorDerivedGlobalSections

/-! # Global Hom adjunction with independent localization universes

Source: Stacks Project, Tag 0B6I, lemma-iso-global-hom.
(blueprint: lem-sc-mixed-global-hom-adjunction-isIso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- The evaluation-mate internal Hom comparison using the normalized mixed tensorator.
Its defining mate equation uniquely determines the natural transformation.
Source: Stacks Project, Tags 08I3 and 0B6I. -/
def mixedHomDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedInternalHom (Opens.grothendieckTopology X) X.sheaf ⋙
        schemeDerivedDirectImage f ⟶
      (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
        derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf :=
  Classical.choose (exists_schemeHomDirectImageComparison f)

/-- The canonical global direct-image Hom comparison: Leray followed by the
internal-Hom comparison defined by the evaluation mate equation.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def mixedGlobalHomDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : schemeDerivedCategory X) :
    (schemeGlobalScalarRestriction f).obj ((schemeGlobalDerivedHom X).obj (op P, Q)) ⟶
      (schemeGlobalDerivedHom Y).obj
        (op ((schemeDerivedDirectImage f).obj P), (schemeDerivedDirectImage f).obj Q) :=
  (mixedGlobalSectionsDirectImageIso f).inv.app
      ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op P, Q)) ≫
    (schemeDerivedGlobalSections Y).map
      ((mixedHomDirectImageComparison f).app (op P, Q))

/-- The global Hom adjunction map is induced by the counit, not an arbitrary iso.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def mixedGlobalHomAdjunctionMap {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (P : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y) :
    (schemeGlobalScalarRestriction f).obj
      ((schemeGlobalDerivedHom X).obj (op P.obj, (a.obj K).obj)) ⟶
      (schemeGlobalDerivedHom Y).obj (op ((schemeDerivedDirectImage f).obj P.obj), K.obj) :=
  mixedGlobalHomDirectImageMap f P.obj (a.obj K).obj ≫
    (schemeGlobalDerivedHom Y).map ((𝟙 _).op, (adj.counit.app K).hom)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical counit-induced global Hom adjunction is invertible with independent
sheaf and global-ring localization universes.
Source: Stacks Project, Tag 0B6I, lemma-iso-global-hom.
(blueprint: lem-sc-mixed-global-hom-adjunction-isIso).

Proof: the evaluation-mate internal Hom comparison followed by Hom of the counit
becomes invertible after the quasi-coherator, by qcqsSheafRHomAdjunction. The coherator
comparison is detected by derived global sections. Apply that result in the chosen
module localization universe and precompose with normalized Leray; this gives exactly
the displayed canonical map. No perfectness or boundedness hypothesis is used. -/
theorem mixedGlobalHomAdjunctionMap_isIso {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (P : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y) :
    IsIso (mixedGlobalHomAdjunctionMap f a adj P K) := by
  let Hx := derivedInternalHom (Opens.grothendieckTopology X) X.sheaf
  let Hy := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
  let R := schemeDerivedDirectImage f
  let G := schemeDerivedGlobalSections Y
  let c := mixedHomDirectImageComparison f
  let bx (L : schemeDerivedCategory X) := Adjunction.mkOfHomEquiv
    (@tensorAdjunctionCore (schemeDerivedCategory X) inferInstance
      (schemeDerivedTensorMonoidal X) Hx (schemeDerivedTensorHomEquiv X)
      (schemeHomTensorHom_naturality X) L)
  let by' (L : schemeDerivedCategory Y) := Adjunction.mkOfHomEquiv
    (@tensorAdjunctionCore (schemeDerivedCategory Y) inferInstance
      (schemeDerivedTensorMonoidal Y) Hy (schemeDerivedTensorHomEquiv Y)
      (schemeHomTensorHom_naturality Y) L)
  obtain ⟨DQ, ⟨coh⟩⟩ := exists_dqCoheratorAdjunction Y
  have hc : ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
      (α : A ⟶ R.obj (Hx.obj (op L, M))),
      ((by' (R.obj L)).homEquiv A (R.obj M)).symm (α ≫ c.app (op L, M)) =
        (schemeHomPullbackAdjunction f).homEquiv _ M
          ((mixedHomTensorPullbackIso f).hom.app (A, R.obj L) ≫
            (𝟙 _ ⊗ₘ (schemeHomPullbackAdjunction f).counit.app L) ≫
            ((bx L).homEquiv _ M).symm
              (((schemeHomPullbackAdjunction f).homEquiv A
                (Hx.obj (op L, M))).symm α)) := by
    intro L M A α
    simp only [bx, by', Adjunction.mkOfHomEquiv_homEquiv,
      tensorAdjunctionCore, Equiv.symm_symm, Hx, R, c, Functor.prod_obj, tensorRight,
      Functor.flip_obj_obj, curriedTensor_obj_obj, tensor]
    exact (Classical.choose_spec (exists_schemeHomDirectImageComparison f)) L M A α
  have h := qcqsSheafRHomAdjunction X Y f
    (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst a adj DQ coh
    (schemeHomPullbackAdjunction f) bx by' (mixedHomTensorPullbackIso f) c hc
  have hPK := h.2 P K
  change IsIso (DQ.map (c.app (op P.obj, (a.obj K).obj) ≫
    Hy.map (X := (op (R.obj P.obj), R.obj (a.obj K).obj))
      (Y := (op (R.obj P.obj), K.obj)) ((𝟙 _).op, (adj.counit.app K).hom))) at hPK
  have := dqCoherator_isIso_derivedGlobalSections Y DQ coh
    (c.app (op P.obj, (a.obj K).obj) ≫
      Hy.map (X := (op (R.obj P.obj), R.obj (a.obj K).obj))
        (Y := (op (R.obj P.obj), K.obj)) ((𝟙 _).op, (adj.counit.app K).hom))
  dsimp only [mixedGlobalHomAdjunctionMap, mixedGlobalHomDirectImageMap,
    schemeGlobalDerivedHom, Functor.comp_map]
  simp only [Category.assoc]
  change IsIso ((mixedGlobalSectionsDirectImageIso f).inv.app _ ≫
    G.map (c.app (op P.obj, (a.obj K).obj)) ≫
      G.map (Hy.map (X := (op (R.obj P.obj), R.obj (a.obj K).obj))
        (Y := (op (R.obj P.obj), K.obj)) ((𝟙 _).op, (adj.counit.app K).hom)))
  rw [← CategoryTheory.Functor.map_comp]
  infer_instance

end AlgebraicGeometry
