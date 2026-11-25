/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import WeilConjectures.AlgebraicGeometry.AffineSheafificationScalar

/-! # Scalar compatibility of affine realization

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
(blueprint: lem-sc-affine-open-realization-scalar).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem scalar_iso_conjugate {S : Type*} [Ring S] {C : Type*}
    [Category C] [Preadditive C] [Linear S C] {V W : C} (r : S) (d : V ≅ W) :
    r • 𝟙 W = d.inv ≫ (r • 𝟙 V) ≫ d.hom := by
  simp

private theorem scalar_commute {S : Type*} [Ring S] {C : Type*}
    [Category C] [Preadditive C] [Linear S C] {V W : C} (r : S) (f : V ⟶ W) :
    (r • 𝟙 V) ≫ f = f ≫ (r • 𝟙 W) := by
  simp

private theorem scalar_map_of_factorization
    {A B : Type*} [Ring A] [Ring B]
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']
    [Linear A C] [Linear A D] [Linear B C'] [Linear B D']
    (Q : C ⥤ D) (Q' : C' ⥤ D') [Q.Linear A] [Q'.Linear B]
    (T : C ⥤ C') (F : D ⥤ D') (c : Q ⋙ F ≅ T ⋙ Q')
    (a : A) (b : B) (K : C) (h : T.map (a • 𝟙 K) = b • 𝟙 (T.obj K)) :
    F.map (a • 𝟙 (Q.obj K)) = b • 𝟙 (F.obj (Q.obj K)) := by
  apply (cancel_mono (c.hom.app K)).mp
  have hc := c.hom.naturality (a • 𝟙 K)
  dsimp only [Functor.comp_map] at hc
  rw [Q.map_smul, Q.map_id, h, Q'.map_smul, Q'.map_id] at hc
  exact hc.trans (scalar_commute b (c.hom.app K)).symm

private theorem scalar_map_of_iso
    {A B : Type*} [Ring A] [Ring B]
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear A C] [Linear B D] (F : C ⥤ D) (a : A) (b : B)
    {V W : C} (d : V ≅ W) (h : F.map (a • 𝟙 V) = b • 𝟙 (F.obj V)) :
    F.map (a • 𝟙 W) = b • 𝟙 (F.obj W) := by
  rw [scalar_iso_conjugate a d, F.map_comp, F.map_comp, h]
  exact (scalar_iso_conjugate b (F.mapIso d)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- The scalar action is transported through the derived localization.
private theorem restriction_scalar (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (a : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    let B := (Over.forget U).op ⋙ X.sheaf.obj
    letI : Linear (RingCat.sectionsSubring (B ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
      SheafOfModules.homLinear B ((moduleRings X.toRingedSpace).over U).property
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    R.map (schemeDerivedScalar X a (𝟙 E)) =
      PresheafOfModules.overSections (R := X.sheaf.obj) U (a.val (op U)) • 𝟙 (R.obj E) := by
  intro B R
  let : Linear (RingCat.sectionsSubring (B ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.homLinear B ((moduleRings X.toRingedSpace).over U).property
  let b := PresheafOfModules.overSections (R := X.sheaf.obj) U (a.val (op U))
  let : Linear
      (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
  let T := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  have hbase (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
      T.map (a • 𝟙 M) = b • 𝟙 (T.obj M) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    change a.val (op V.unop.left) • x =
      X.sheaf.obj.map V.unop.hom.op (a.val (op U)) • x
    exact congrArg (fun r ↦ r • x) (a.property V.unop.hom.op).symm
  have hcomplex (L : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
      (T.mapHomologicalComplex (.up ℤ)).map (a • 𝟙 L) =
        b • 𝟙 ((T.mapHomologicalComplex (.up ℤ)).obj L) := by
    apply HomologicalComplex.hom_ext
    intro n
    exact hbase (L.X n)
  have hQ (L : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
      R.map (a • 𝟙 (DerivedCategory.Q.obj L)) =
        b • 𝟙 (R.obj (DerivedCategory.Q.obj L)) := by
    exact scalar_map_of_factorization DerivedCategory.Q DerivedCategory.Q
      (T.mapHomologicalComplex (.up ℤ)) R T.mapDerivedCategoryFactors a b L (hcomplex L)
  change R.map (a • 𝟙 E) = _
  exact scalar_map_of_iso R a b (DerivedCategory.Q.objObjPreimageIso E)
    (hQ (DerivedCategory.Q.objPreimage E))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- Sectionwise scalar actions require unfolding transported module structures.
/-- Scalar identities commute with every affine realization comparison isomorphism.
This requires neither perfectness nor a cohomology support condition.
Source: Stacks Project, Tag 06Z0, termwise associated-sheaf construction, and
Tag 08EJ, identification of the affine scalar action.
(blueprint: lem-sc-affine-open-realization-scalar).

Proof: Give the localized-site sheaf category the action of global sections of X
by restricting each compatible family of scalars to objects over U. The overFunctor
is linear for this action. Give A-modules the same action via evaluation at U.
Compatibility of sections says that affinePerfectSheafification sends a|U times
any module map to multiplication by the corresponding restricted global scalar.
Indeed tilde applies the scalar in each local module localization, scheme-isomorphism
restriction transports it through the structure-sheaf ring map, and the over-site
inverse equivalence only reindexes the sections. These identities pass termwise to
complexes and then through Q, which is linear. Naturality of the given comparison at
K identifies F(a|U id_Q(K)) with the scalar identity on F(Q(K)). Centrality of scalar
multiplication in the target derived category allows this scalar identity to commute
with the arbitrary comparison e. Linearity of derived restriction identifies the
scalar identity on R(E) with R(schemeDerivedScalar X a id_E). Compose the resulting
equality with e.hom. For zero scalars and empty U the same equations hold, and no
choice of e or perfect model is needed. -/
theorem affine_open_realization_scalar
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) →
      ∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (E : schemeDerivedCategory X)
        (e : F.obj (DerivedCategory.Q.obj K) ≅ R.obj E)
        (a : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})),
        F.map ((show A from a.val (op U)) • 𝟙 (DerivedCategory.Q.obj K)) ≫ e.hom =
          e.hom ≫ R.map (schemeDerivedScalar X a (𝟙 E)) := by
  intro A R F hF K E e a
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  let B := (Over.forget U).op ⋙ X.sheaf.obj
  let : Linear
      (RingCat.sectionsSubring (B ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.homLinear B ((moduleRings X.toRingedSpace).over U).property
  let b := PresheafOfModules.overSections (R := X.sheaf.obj) U (a.val (op U))
  have he : (b • 𝟙 (F.obj (DerivedCategory.Q.obj K))) ≫ e.hom =
      e.hom ≫ (b • 𝟙 (R.obj E)) := scalar_commute b e.hom
  have hR : R.map (schemeDerivedScalar X a (𝟙 E)) = b • 𝟙 (R.obj E) :=
    restriction_scalar X U E a
  let S := affinePerfectSheafification X U hU
  have hS : (S.mapHomologicalComplex (.up ℤ)).map ((show A from a.val (op U)) • 𝟙 K) =
      b • 𝟙 ((S.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply HomologicalComplex.hom_ext
    intro n
    exact affine_perfect_sheafification_scalar X U hU (K.X n) (a.val (op U))
  obtain ⟨c⟩ := hF
  have hFscalar : F.map ((show A from a.val (op U)) • 𝟙 (DerivedCategory.Q.obj K)) =
      b • 𝟙 (F.obj (DerivedCategory.Q.obj K)) := by
    refine scalar_map_of_factorization (DerivedCategory.Q (C := ModuleCat.{u} A)) DerivedCategory.Q
      (S.mapHomologicalComplex (.up ℤ)) F c (show A from a.val (op U)) b K ?_
    exact hS
  rw [hFscalar, hR]
  exact he

end AlgebraicGeometry.Scheme
