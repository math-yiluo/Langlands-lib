/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import WeilConjectures.AlgebraicGeometry.AffinePerfectPlusLocallyFree
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine perfect extension after adjoining a shift

Source: literature/stacks-project/perfect.tex, Tag 08EI (Lemma 36.13.8)
(blueprint: lem-sc-affine-perfect-plus-shift).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Cone cancellation for the projection onto the first summand.
private theorem cone_projection_iso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (M F : C) (T : Pretriangulated.Triangle C)
    (hT : T ∈ Pretriangulated.distinguishedTriangles (C := C))
    (e₁ : T.obj₁ ≅ M ⊞ F) (e₂ : T.obj₂ ≅ M ⊞ F)
    (h : T.mor₁ ≫ e₂.hom = e₁.hom ≫ biprod.fst ≫ biprod.inl) :
    Nonempty (T.obj₃ ≅ F ⊞ F⟦(1 : ℤ)⟧) := by
  classical
  let : Zero C := HasZeroObject.zero' C
  -- Adjoin F to the source, then to the target of the identity triangle on M.
  have h₀ := Pretriangulated.mk_fst_comp_distinguished (𝟙 M) (0 : M ⟶ (0 : C))
    (0 : (0 : C) ⟶ M⟦(1 : ℤ)⟧) (Pretriangulated.contractible_distinguished M) F
  have h₁ := Pretriangulated.mk_comp_inl_distinguished _ _ _ h₀ F
  let S := Pretriangulated.Triangle.mk
    ((biprod.fst ≫ 𝟙 M) ≫ (biprod.inl : M ⟶ M ⊞ F))
    (biprod.map ((0 : M ⟶ (0 : C)) ≫ biprod.inl) (𝟙 F))
    (biprod.fst ≫ biprod.desc
      ((0 : (0 : C) ⟶ M⟦(1 : ℤ)⟧) ≫
        (biprod.inl : M ⟶ M ⊞ F)⟦(1 : ℤ)⟧')
      ((biprod.inr : F ⟶ M ⊞ F)⟦(1 : ℤ)⟧'))
  have hS : S ∈ Pretriangulated.distinguishedTriangles (C := C) := h₁
  -- The resulting cone is (0 ⊞ F[1]) ⊞ F; compare the first two terms.
  let e := Pretriangulated.isoTriangleOfIso₁₂ T S hT hS e₁ e₂ (by simpa [S] using h)
  exact ⟨Pretriangulated.Triangle.π₃.mapIso e ≪≫
    biprod.mapIso (isoZeroBiprod (isZero_zero C)).symm (Iso.refl F) ≪≫
    biprod.braiding _ _⟩

/-- If `X` is affine and `U` is a quasi-compact open, every perfect complex on `U`
becomes the restriction of a perfect complex on `X` after adjoining its shift by one.
Source: Stacks Project, Tag 08EI (Lemma 36.13.8)
(blueprint: lem-sc-affine-perfect-plus-shift).

Proof: use `lem-sc-affine-perfect-plus-locally-free` to extend
`𝓕[-r] ⊕ F`; lift the projection onto the first summand by
`lem-sc-affine-perfect-map-lift`; the cone of the lifted map is perfect by
`lem-pc-perfect-two-out-of-three`, and its restriction is `F ⊕ F[1]` by the
cone computation in the source proof. -/
theorem exists_perfect_restrict_iso_directSum_shift
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme)
    (hF : Scheme.IsPerfect U.toScheme F) :
    ∃ E : schemeDerivedCategory X,
      Scheme.IsPerfect X E ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E ≅
          F ⊞ F⟦(1 : ℤ)⟧) := by
  classical
  obtain ⟨r, M, _, P, hP, ⟨eP⟩⟩ :=
    Scheme.exists_perfect_lift_plus_finiteLocallyFree X U hU F hF
  let R := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
  let L := ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj M)⟦-r⟧
  let α : R.obj P ⟶ R.obj P := eP.hom ≫ biprod.fst ≫ biprod.inl ≫ eP.inv
  let PQ : schemeDerivedQCohCategory X :=
    ⟨P, schemeDerivedQCohProperty_of_isPerfect X P hP⟩
  obtain ⟨A, _, _, γ, hA, _, _, ⟨bU, _, hα⟩, _⟩ :=
    Scheme.exists_perfect_map_lift_of_isAffine X U hU PQ P hP α
  obtain ⟨E, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle γ
  let T := Pretriangulated.Triangle.mk γ g h
  have hperfect : Scheme.IsPerfect X E :=
    (Scheme.isPerfect_two_out_of_three X T hT).1 hA hP
  refine ⟨E, hperfect, ?_⟩
  apply cone_projection_iso L F (R.mapTriangle.obj T) (R.map_distinguished T hT)
    (bU ≪≫ eP) eP
  change R.map γ ≫ eP.hom = (bU.hom ≫ eP.hom) ≫ biprod.fst ≫ biprod.inl
  have hγ : R.map γ = bU.hom ≫ α := by
    rw [hα]
    simp [R]
  rw [hγ]
  simp [α, Category.assoc]
end AlgebraicGeometry
