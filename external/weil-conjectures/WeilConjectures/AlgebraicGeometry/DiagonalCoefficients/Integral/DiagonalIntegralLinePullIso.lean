/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement

/-! # Inverse image of the bottom integral Tate line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] spIntegralTwist spIntegralComparison integralMap
  CategoryTheory.Sheaf.monoidalCategory Mod.extendScalarsObj Mod.extendScalarsIsoComapInv
  CondensedRing.pullIso

private theorem restrict_semilinear
    {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal]
    {R S : C} [MonObj R] [MonObj S] {R' S' : D} [MonObj R'] [MonObj S']
    (r : R ⟶ S) [IsMonHom r] (s : R' ⟶ S') [IsMonHom s]
    (a : F.obj R ⟶ R') [IsMonHom a] (b : F.obj S ⟶ S') [IsMonHom b]
    (h : F.map r ≫ b = a ≫ s) (M : Mod C S) (N : Mod D S')
    (c : (F.mapMod S).obj M ⟶ (Mod.comap b).obj N) :
    ∃ c' : (F.mapMod R).obj ((Mod.comap r).obj M) ⟶
        (Mod.comap a).obj ((Mod.comap s).obj N), c'.hom = c.hom := by
  let c' := (F.mapModComapIso r).hom.app M ≫
    (Mod.comap (F.map r)).map c ≫
    (Mod.comapComp (F.map r) b).inv.app N ≫
    (Mod.comapCongr h).hom.app N ≫
    (Mod.comapComp a s).hom.app N
  refine ⟨c', ?_⟩
  simp only [c', Mod.comp_hom', Functor.mapModComapIso_hom_app_hom,
    Mod.comap_map_hom, Mod.comapComp_inv_app_hom, Mod.comapComp_hom_app_hom,
    Mod.comapCongr_hom_app_hom]
  change 𝟙 _ ≫ c.hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = c.hom
  simp only [Category.id_comp, Category.comp_id]

attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

private theorem restricted_ordinary_iso
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ' S) (N : Modules Λ' X)
    (c : ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ' S)).obj M ⟶
      (Mod.comap (condensedPullbackHom Λ' f)).obj N) [IsIso c.hom] :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      ((Mod.comap (coefficientMap a S)).obj M) ≅
        (Mod.comap (coefficientMap a X)).obj N) := by
  obtain ⟨d, hd⟩ := restrict_semilinear (upperStar Ab.{u + 1} f)
    (coefficientMap a S) (coefficientMap a X)
    (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
    (map_coefficientMap_comp_condensedPullbackHom a f) M N c
  have : IsIso d.hom := hd.symm ▸ inferInstance
  obtain ⟨e, _⟩ := ordinaryLift_iso f Λ _ _ d
  exact ⟨e⟩

/-- The specified bottom integral Tate line is preserved by ordinary inverse image.

Source: Cartesian coefficient twists, integral comparison and scalar naturality
(blueprint: lem-diagonal-integral-line-pull-iso).

Proof: the integral root comparison is semilinear over the pulled-back coefficient
ring. Restrict it along the bottom-field coefficient inclusion, using naturality
of the coefficient comparison. Scalar extension along the invertible pullback
coefficient comparison lifts this semilinear map to a linear map. The underlying
whole root comparison is an isomorphism, so the linear lift is an isomorphism.
The construction uses the whole inverse-limit comparison, not finite detection. -/
theorem diagonalIntegralLine_pullIso (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    Nonempty ((CondensedRing.upperStar
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj (zlLine l S) ≅ zlLine l X) := by
  obtain ⟨c, hc⟩ := integralModuleComparison_exists f l (bottomField l)
  have : IsIso c.hom := by
    rw [hc]
    exact nativeIntegralComparison_isIso f l (bottomField l)
  exact restricted_ordinary_iso _ _ (integralMap l (bottomField l)) f
    (spIntegralTwist S l (bottomField l)) (spIntegralTwist X l (bottomField l)) c

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
