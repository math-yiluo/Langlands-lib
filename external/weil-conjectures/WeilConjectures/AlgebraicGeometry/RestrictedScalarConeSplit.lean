/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar

/-! # A scalar cone splits after restriction

Source: Stacks Project, Tags 08EK, 05QR, 05QS, and 05QT
(blueprint: lem-sc-restricted-scalar-cone-split).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
private theorem derived_map_scalar_identity
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {R S : Type*} [Ring R] [Ring S] [Linear R C] [Linear S D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (r : R) (s : S)
    (hL : ∀ A : C, L.map (r • 𝟙 A) = s • 𝟙 (L.obj A))
    (E : DerivedCategory C) :
    L.mapDerivedCategory.map (r • 𝟙 E) = s • 𝟙 (L.mapDerivedCategory.obj E) := by
  have hc (K : CochainComplex C ℤ) :
      (L.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 K) =
        s • 𝟙 ((L.mapHomologicalComplex (.up ℤ)).obj K) := by
    ext n
    change L.map (r • 𝟙 (K.X n)) = s • 𝟙 (L.obj (K.X n))
    exact hL (K.X n)
  have hQ (K : CochainComplex C ℤ) :
      L.mapDerivedCategory.map (r • 𝟙 (DerivedCategory.Q.obj K)) =
        s • 𝟙 (L.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := by
    let e := L.mapDerivedCategoryFactors.app K
    rw [← cancel_mono e.hom]
    rw [← DerivedCategory.Q.map_id K, ← Functor.map_smul]
    dsimp [e]
    rw [L.mapDerivedCategoryFactors_hom_naturality, hc, Functor.map_smul,
      CategoryTheory.Functor.map_id]
    dsimp only [CategoryTheory.Functor.comp_obj]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
  let e := DerivedCategory.Q.objObjPreimageIso E
  rw [← cancel_epi (L.mapDerivedCategory.map e.hom)]
  calc
    L.mapDerivedCategory.map e.hom ≫ L.mapDerivedCategory.map (r • 𝟙 E) =
        L.mapDerivedCategory.map (r • 𝟙 _) ≫ L.mapDerivedCategory.map e.hom := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
    _ = L.mapDerivedCategory.map e.hom ≫ (s • 𝟙 _) := by
      rw [hQ]
      simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem sheaf_restriction_scalar_identity (X : Scheme.{u}) (U : X.Opens)
    (g : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (g' : RingCat.sectionsSubring
      (U.toScheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (hg : g'.val (op ⊤) = U.ι.appTop.hom (g.val (op ⊤)))
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    letI : Linear
        (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
    letI : Linear
        (RingCat.sectionsSubring (U.toScheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
      SheafOfModules.homLinear U.toScheme.sheaf.obj
        (moduleRings U.toScheme.toRingedSpace).property
    let L := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    L.map (g • 𝟙 M) = g' • 𝟙 (L.obj M) := by
  dsimp only
  ext V x
  change g.val (op (U.ι ''ᵁ V.unop)) • x = g'.val V • x
  congr 1
  have hx := g.property (homOfLE (show U.ι ''ᵁ V.unop ≤ ⊤ from le_top)).op
  have hu := g'.property (homOfLE (show V.unop ≤ ⊤ from le_top)).op
  rw [← hu, hg]
  rw [← hx]
  change X.presheaf.map _ (g.val (op ⊤)) =
    X.presheaf.map _ (X.presheaf.map _ (g.val (op ⊤)))
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

private theorem scalar_zero_of_iso_biproduct_shifts (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (g : RingCat.sectionsSubring (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (F A : schemeDerivedCategory Y) (hzero : schemeDerivedScalar Y g (𝟙 F) = 0)
    (J : Type) [Finite J] (a : J → ℤ)
    (e : A ≅ biproduct (fun j : J ↦ F⟦a j⟧)) :
    schemeDerivedScalar Y g (𝟙 A) = 0 := by
  let : Linear
      (RingCat.sectionsSubring (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    SheafOfModules.homLinear Y.sheaf.obj (moduleRings Y.toRingedSpace).property
  change g • 𝟙 F = 0 at hzero
  change g • 𝟙 A = 0
  have hshift (j : J) : g • 𝟙 (F⟦a j⟧) = 0 := by
    rw [← (shiftFunctor (schemeDerivedCategory Y) (a j)).map_id F,
      ← Functor.map_smul, hzero, Functor.map_zero]
  have hsum : g • 𝟙 (biproduct (fun j : J ↦ F⟦a j⟧)) = 0 := by
    apply biproduct.hom_ext
    intro j
    calc
      (g • 𝟙 _) ≫ biproduct.π _ j = biproduct.π _ j ≫ (g • 𝟙 _) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
      _ = 0 ≫ biproduct.π _ j := by rw [hshift j, comp_zero, zero_comp]
  rw [← cancel_mono e.hom]
  calc
    (g • 𝟙 A) ≫ e.hom = e.hom ≫ (g • 𝟙 _) := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
    _ = 0 ≫ e.hom := by rw [hsum, comp_zero, zero_comp]

/-- If a scalar kills F, a cone of that scalar on an object whose restriction is a
finite sum of shifts of F restricts to the sum of its input and its shifted input.
Source: Stacks Project, Tag 08EK, cone construction, and Tags 05QR, 05QS, 05QT
(blueprint: lem-sc-restricted-scalar-cone-split).

Proof: The restriction functor is exact and its derived functor is triangulated.
Sectionwise multiplication commutes with restriction and the over-site equivalence.
The equality of top sections identifies the restricted scalar with g'; compatibility
of each family then gives equality on every smaller open. Derived scalar
multiplication is natural, commutes with shifts, and acts componentwise on finite
biproducts. Transporting along the given decomposition therefore makes the scalar
on the restricted input zero. The restricted triangle is a cone triangle of zero.
Rotate the restricted triangle once. Its objects are input, cone, input[1],
and its last map is minus the shift of the zero scalar map, hence zero. Apply
Tag 05QT (Mathlib's `exists_iso_binaryBiproduct_of_distTriang`) and invert the
resulting isomorphism to identify the cone with input plus input[1]. This includes
an empty family, where the input and its cone are zero. -/
theorem restricted_scalar_cone_split (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (g : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (g' : RingCat.sectionsSubring
      (U.toScheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (hg : g'.val (op ⊤) = U.ι.appTop.hom (g.val (op ⊤)))
    (E K : schemeDerivedCategory X) (b : E ⟶ K) (d : K ⟶ E⟦(1 : ℤ)⟧)
    (hcone : Triangle.mk (schemeDerivedScalar X g (𝟙 E)) b d ∈
      distTriang (schemeDerivedCategory X))
    (F : schemeDerivedCategory U.toScheme)
    (hzero : schemeDerivedScalar U.toScheme g' (𝟙 F) = 0)
    (J : Type) [Finite J] (a : J → ℤ)
    (hE : Nonempty (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E ≅ biproduct (fun j : J ↦ F⟦a j⟧))) :
    Nonempty (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj K ≅
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E ⊞
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E)⟦(1 : ℤ)⟧) := by
  classical
  let L := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)
  let R := L.mapDerivedCategory
  have hscalar : R.map (schemeDerivedScalar X g (𝟙 E)) =
      schemeDerivedScalar U.toScheme g' (𝟙 (R.obj E)) := by
    let : Linear
        (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
    let : Linear
        (RingCat.sectionsSubring
          (U.toScheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
      SheafOfModules.homLinear U.toScheme.sheaf.obj
        (moduleRings U.toScheme.toRingedSpace).property
    exact derived_map_scalar_identity L g g' (sheaf_restriction_scalar_identity X U g g' hg) E
  obtain ⟨eE⟩ := hE
  have hfirst : R.map (schemeDerivedScalar X g (𝟙 E)) = 0 := by
    rw [hscalar]
    exact scalar_zero_of_iso_biproduct_shifts U.toScheme g' F (R.obj E) hzero J a eE
  let T := R.mapTriangle.obj (Triangle.mk (schemeDerivedScalar X g (𝟙 E)) b d)
  have hT : T ∈ distTriang (schemeDerivedCategory U.toScheme) :=
    R.map_distinguished _ hcone
  obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang T.rotate
    (rot_of_distTriang _ hT) (by
      change -(R.map (schemeDerivedScalar X g (𝟙 E)))⟦(1 : ℤ)⟧' = 0
      rw [hfirst, Functor.map_zero, neg_zero])
  exact ⟨e⟩

end AlgebraicGeometry.Scheme
