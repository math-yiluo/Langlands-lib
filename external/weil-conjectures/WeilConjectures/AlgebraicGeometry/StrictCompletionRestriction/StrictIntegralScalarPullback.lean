/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import all WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalizationRegular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
/-! # Uniformizer action under geometric pullback -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CondensedRing.monoidal_upperStar
  Mod.monoidal_extendScalars Functor.monoidal_mapMod
universe u a b c d
private theorem monoidal_scalar {A : Type a} [Category.{b} A] [MonoidalCategory A]
    {B : Type c} [Category.{d} B] [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal]
    (r : End (𝟙_ A)) (s : End (𝟙_ B))
    (h : F.map r.asHom ≫ Functor.OplaxMonoidal.η F = Functor.OplaxMonoidal.η F ≫ s.asHom)
    (M : A) :
    F.map ((λ_ M).inv ≫ r.asHom ▷ M ≫ (λ_ M).hom) =
      (λ_ (F.obj M)).inv ≫ s.asHom ▷ F.obj M ≫ (λ_ (F.obj M)).hom := by
  simp only [Functor.map_comp, Functor.Monoidal.map_leftUnitor_inv,
    Functor.Monoidal.map_leftUnitor, Functor.Monoidal.map_whiskerRight, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, h]
  simp only [Functor.Monoidal.ε_η_assoc]

private theorem scalar_square_under_unit {C : Type*} [Category C]
    {A B M : C} (q : A ⟶ B) (r : A ⟶ A) (t : B ⟶ B)
    (η : B ⟶ M) (α : A ⟶ M) (s : M ⟶ M)
    (hn : r ≫ q = q ≫ t) (hη : q ≫ η = α) (hs : r ≫ α = α ≫ s) :
    q ≫ t ≫ η = q ≫ η ≫ s := by
  calc
    q ≫ t ≫ η = r ≫ α := by rw [← Category.assoc, ← hn, Category.assoc, hη]
    _ = α ≫ s := hs
    _ = q ≫ η ≫ s := by rw [← Category.assoc, hη]

private theorem extendUnitHom_hom_ext
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C] [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] (M : Mod C R) (N : Mod C S)
    (f g : (Mod.extendScalars φ).obj M ⟶ N)
    (h : Mod.extendUnitHom φ M ≫ f.hom = Mod.extendUnitHom φ M ≫ g.hom) : f = g := by
  apply ((Mod.extendRestrictAdjunction φ).homEquiv M N).injective
  apply Mod.hom_ext
  simp only [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change (Mod.extendUnit φ M ≫ (Mod.comap φ).map f).hom =
    (Mod.extendUnit φ M ≫ (Mod.comap φ).map g).hom
  simpa only [Mod.comp_hom', Mod.comap_map_hom, Mod.extendUnit_hom] using h

private theorem scalar_extension_square
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C] [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] (M : Mod C R) (N : Mod C S)
    (t : End M) (s : End N) (η : (Mod.extendScalars φ).obj M ⟶ N)
    (α : M.X ⟶ N.X) (hη : Mod.extendUnitHom φ M ≫ η.hom = α)
    (hs : t.asHom.hom ≫ α = α ≫ s.asHom.hom) :
    (Mod.extendScalars φ).map t.asHom ≫ η = η ≫ s.asHom := by
  apply extendUnitHom_hom_ext φ M N
  simpa only [Mod.comp_hom', Category.assoc] using
    scalar_square_under_unit (Mod.extendUnitHom φ M) t.asHom.hom
      ((Mod.extendScalars φ).map t.asHom).hom η.hom α s.asHom.hom
      (Mod.extendUnitHom_extendScalarsMap φ t.asHom).symm hη hs

private theorem naturality_square
    {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (η : F ⟶ G) {M N : C} (f : M ⟶ N)
    (a : F.obj M ⟶ F.obj N) (b : G.obj M ⟶ G.obj N)
    (α : F.obj M ⟶ G.obj M) (β : F.obj N ⟶ G.obj N)
    (ha : a = F.map f) (hb : b = G.map f)
    (hα : α = η.app M) (hβ : β = η.app N) : a ≫ β = α ≫ b := by
  rw [ha, hb, hα, hβ]
  exact η.naturality f

private theorem mapMod_hom
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] {R : C} [MonObj R]
    {M N : Mod C R} (t : M ⟶ N) :
    ((F.mapMod R).map t).hom = F.map t.hom := rfl

section Coefficients
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
private def scalarHom (d : End (Mod.regular Λ)) : End Λ := .of d.asHom.hom

attribute [local irreducible] scalarHom

private def pointScalar (X : Scheme.{u}) (d : End (Mod.regular Λ)) :
    End (Mod.regular (condensedRingObj Λ X)) :=
  .of (Mod.Hom.mk' ((upperStarFromPoint X).map (scalarHom Λ d).asHom)
    (by
      unfold scalarHom
      exact IsModHom.smul_hom
        (f := (((upperStarFromPoint X).mapMod Λ).map d.asHom).hom)))

omit [IsCommMonObj Λ] in
private theorem pointScalar_hom (X : Scheme.{u}) (d : End (Mod.regular Λ)) :
    (pointScalar Λ X d).asHom.hom = (upperStarFromPoint X).map (scalarHom Λ d).asHom := rfl

private def pullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).obj
      (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) ⟶
      𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  Functor.OplaxMonoidal.η (CondensedRing.upperStar Λ f)

attribute [local irreducible] pointScalar pullbackUnit

-- Kernel conversion compares the sheaf monoidal instances at the coefficient square.
omit [IsCommMonObj Λ] in
private theorem coefficient_scalar_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : End (Mod.regular Λ)) :
    (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).map
      (pointScalar Λ Y d).asHom).hom ≫ condensedPullbackHom Λ f =
      condensedPullbackHom Λ f ≫ (pointScalar Λ X d).asHom.hom := by
  apply naturality_square (upperStarFromPoint Y ⋙ ProEtale.upperStar Ab.{u + 1} f)
    (upperStarFromPoint X) (upperStarFromPointComp f).hom (scalarHom Λ d).asHom
  · rw [mapMod_hom, pointScalar_hom]
    rfl
  · exact pointScalar_hom Λ X d
  · rfl
  · rfl

private theorem pullback_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (t : M ⟶ N) :
    (CondensedRing.upperStar Λ f).map t =
      (Mod.extendScalars (condensedPullbackHom Λ f)).map
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).map t) := rfl

private theorem pullback_unit_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : End (Mod.regular Λ)) :
    (CondensedRing.upperStar Λ f).map (pointScalar Λ Y d).asHom ≫ pullbackUnit Λ f =
      pullbackUnit Λ f ≫ (pointScalar Λ X d).asHom := by
  let α := condensedPullbackHom Λ f
  let G := (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)
  let M := 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
  have hη : Mod.extendUnitHom α (G.obj M) ≫ (pullbackUnit Λ f).hom = α := by
    unfold pullbackUnit
    exact CondensedRing.extendUnitHom_η_upperStar Λ f
  rw [pullback_map]
  exact scalar_extension_square α (G.obj M)
    (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (.of (G.map (pointScalar Λ Y d).asHom)) (pointScalar Λ X d) (pullbackUnit Λ f) α hη
    (coefficient_scalar_naturality Λ f d)
end Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem regular_scalar_eq (X : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    (DerivedNakayama.regularPullbackIso l E X).inv ≫
      (DerivedNakayama.pullback l E X).map d.asHom ≫
      (DerivedNakayama.regularPullbackIso l E X).hom =
    (pointScalar (DerivedNakayama.integerRing l E) X d).asHom := by
  simp only [DerivedNakayama.regularPullbackIso, eqToIso_refl,
    Iso.refl_inv, Iso.refl_hom, Category.comp_id]
  apply Mod.hom_ext
  simp only [Mod.comp_hom', Mod.id_hom', pointScalar_hom]
  rfl

private theorem pullback_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (M : AdicCompletion.Modules l E Y) :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
      ((DerivedNakayama.scalarOnModules l E Y d).app M) =
      (DerivedNakayama.scalarOnModules l E X d).app
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj M) := by
  apply monoidal_scalar
  rw [regular_scalar_eq, regular_scalar_eq]
  exact pullback_unit_scalar (DerivedNakayama.integerRing l E) f d
/-- Pullback transports the canonical integral scalar action on the nose.
Source: canonical coefficient naturality; blueprint Locality, scalar comparison
(blueprint: lem-sfb-strict-integral-scalar-pullback).

Proof: The canonical point scalar is the specified uniformizer endomorphism for
every canonical cone datum. Naturality of the coefficient comparison gives the
regular-module scalar square. The extension adjunction unit identifies the inverse
monoidal unit comparison with the coefficient map; cancelling that unit proves
the scalar square for geometric module pullback. The monoidal unitor identities
then identify the scalar action on every module. -/
theorem strictIntegralScalarPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E Y))
    (T : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E X))
    (hS : IsIntegral l E Y S) (hT : IsIntegral l E X T)
    (M : AdicCompletion.Modules l E Y) :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map (S.scalar.asHom.app M) =
      T.scalar.asHom.app ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj M) := by
  obtain ⟨dS, hdS, _, hsS, _⟩ := hS
  obtain ⟨dT, hdT, _, hsT, _⟩ := hT
  rw [hsS, hsT, CoefficientCone.scalar_eq l E Y dS hdS,
    CoefficientCone.scalar_eq l E X dT hdT]
  exact pullback_scalar l E f (DerivedNakayama.uniformizerEnd l E) M

end
end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
