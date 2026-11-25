/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineKoszulSectionColimit
import WeilConjectures.Algebra.Homology.KFlatResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Limits.Types.Colimits
import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Koszul representatives of sections on an affine open

Source: Stacks Project, Tags 08DC, 08DD and 08EH.
(blueprint: lem-sc-affine-koszul-section-roof).
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Realize a derived augmentation by a chain map after a K-flat replacement.
Source: Stacks Project, Tag 06YS, and calculus of fractions in the derived category. -/
private theorem kflat_augmentation_realization
    (X : Scheme.{uX})
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    (P : schemeDerivedCategory X)
    (T : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (a : P ⟶ DerivedCategory.Q.obj T) :
    ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧
      ∃ (c : DerivedCategory.Q.obj J ≅ P) (u : J ⟶ T),
        DerivedCategory.Q.map u = c.hom ≫ a := by
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  let Q := DerivedCategory.Q (C := C)
  let P₀ := Q.objPreimage P
  let c₀ : Q.obj P₀ ≅ P := Q.objObjPreimageIso P
  obtain ⟨K, t, ht, b, hb⟩ := DerivedCategory.right_fac (c₀.hom ≫ a)
  let := ht
  obtain ⟨J, q, hJ, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) K
  let : QuasiIso q := hq
  let c : Q.obj J ≅ P := asIso (Q.map q) ≪≫ asIso (Q.map t) ≪≫ c₀
  refine ⟨J, hJ, c, q ≫ b, ?_⟩
  dsimp only [c, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Category.assoc, hb]
  dsimp only [Q]
  simp only [Functor.map_comp, IsIso.hom_inv_id_assoc]

/-- Transport a section along an isomorphic realization of an augmentation. -/
private theorem map_section_of_realization
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {P T E J : C} (a : P ⟶ T) (v : R.obj T ⟶ R.obj P)
    (hav : R.map a ≫ v = 𝟙 _) (hva : v ≫ R.map a = 𝟙 _)
    (s : R.obj T ⟶ R.obj E) (ξ : P ⟶ E) (hs : v ≫ R.map ξ = s)
    (c : J ≅ P) (u : J ⟶ T) (hu : u = c.hom ≫ a) :
    IsIso (R.map u) ∧ R.map u ≫ s = R.map (c.hom ≫ ξ) := by
  let j : R.obj P ≅ R.obj T := ⟨R.map a, v, hav, hva⟩
  constructor
  · rw [hu, Functor.map_comp]
    exact (R.mapIso c ≪≫ j).isIso_hom
  · rw [hu, Functor.map_comp, Functor.map_comp, ← hs]
    rw [Category.assoc, ← Category.assoc (R.map a), hav, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- A section of an arbitrary quasi-coherent derived object on a compact open of an affine scheme
is represented by a map from a K-flat perfect complex with a chain augmentation.
There is no perfect source, tensor product, or lifted morphism in this statement.

Source: Stacks Project, perfect.tex, Tags 08DC and 08DD, and the first paragraph of
Tag 08EH; cohomology.tex, Tag 06YD.
(blueprint: lem-sc-affine-koszul-section-roof).

Proof:
1. The transported Hom-colimit comparison `affine_koszul_section_colimit` supplies
   perfect derived objects P_n, augmentations a_n to Q(T), and a colimit whose legs
   are restriction followed by the inverse restricted augmentation.
2. `Types.jointly_surjective` gives a finite index n and ξ : P_n → E representing s.
3. Represent P_n by a complex and apply `DerivedCategory.right_fac` to its augmentation.
   This gives K → T and a quasi-isomorphism K → P_n's representative. Apply
   `exists_isKFlatResolution` to K and compose chain maps to obtain u : J → T,
   an isomorphism c : Q(J) ≅ P_n, and Q(u) = c.hom followed by a_n.
4. Transport each strictly perfect local model along c to prove Q(J) perfect.
   Restriction of Q(u) is the composite of restriction of c.hom and a_n, so is
   invertible. Multiply the cocone formula by the restricted augmentation and
   cancel its inverse. Functoriality yields R(Q(u)) followed by s = R(c.hom followed by ξ).
5. Empty U, zero E and the zero ring use the same colimit and realization arguments.
   No boundedness or nonempty assumption is introduced. -/
theorem affine_koszul_section_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    ∀ s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj E.obj,
      ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
        CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
        ∃ (u : J ⟶ T) (ξ : DerivedCategory.Q.obj J ⟶ E.obj),
          IsIso (R.map (DerivedCategory.Q.map u)) ∧
          R.map (DerivedCategory.Q.map u) ≫ s = R.map ξ := by
  classical
  -- Reuse the sheaf abelian structures throughout the restriction comparisons.
  let _ : Abelian (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) := inferInstance
  let _ (V : X.Opens) :
      Abelian (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V)) := inferInstance
  let _ : Abelian (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace)) :=
    inferInstance
  have _ (V : X.Opens) :
      (SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) V).Additive :=
    Functor.additive_of_preserves_binary_products _
  let := SheafOfModules.monoidalCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  let T := HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)
  let LX := SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U
  let EX : SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  let R := (LX ⋙ EX.functor).mapDerivedCategory
  change ∀ s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj E.obj, _
  intro s
  have hcol := affine_koszul_section_colimit X U hU E
  dsimp only at hcol
  obtain ⟨P, a, hP, v, hav, hva, D, hD, ι, hι, ⟨hc⟩⟩ := hcol
  obtain ⟨n, z, hz⟩ := Types.jointly_surjective D hc s
  let ξ : P n ⟶ E.obj := cast (hD n) z
  have hξ : ι.app n (cast (hD n).symm ξ) = s := by
    simpa only [ξ, cast_cast, cast_eq] using hz
  obtain ⟨J, hJ, c, u, hu⟩ := kflat_augmentation_realization X (P n) T (a n)
  have hp : IsPerfect X (DerivedCategory.Q.obj J) := by
    intro x
    obtain ⟨V, hx, K, hK, ⟨eK⟩⟩ := hP n x
    exact ⟨V, hx, K, hK,
      ⟨(SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) V).mapDerivedCategory.mapIso
        c ≪≫ eK⟩⟩
  have hs : v n ≫ R.map ξ = s := (hι n ξ).symm.trans hξ
  obtain ⟨hiu, hsection⟩ := map_section_of_realization R (a n) (v n) (hav n) (hva n)
    s ξ hs c (DerivedCategory.Q.map u) hu
  exact ⟨J, hJ, hp, u, c.hom ≫ ξ, hiu, hsection⟩

end AlgebraicGeometry.Scheme
