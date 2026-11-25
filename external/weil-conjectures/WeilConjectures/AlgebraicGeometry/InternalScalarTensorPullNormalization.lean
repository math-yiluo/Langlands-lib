/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
import WeilConjectures.AlgebraicGeometry.InternalScalarPullRouteModel
import WeilConjectures.AlgebraicGeometry.InternalTensorPullRouteModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalTensorCounit

/-! # The normalized restricted scalar pullback square is the canonical tensor square

Source: Stacks Tags 07A4, 0D6D, 0D6E, 07A6, 06YY and 06YP.
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.QuotientChange
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
set_option allowUnsafeReducibility true
attribute [local reducible] L CondensedRing.moduleObjectDerivedPullback
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private theorem modelTarget_isIso (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (P : HomotopyCategory (Modules Λ Y) (.up ℤ))
    (hP : (CondensedRing.upperStar Λ f).kFlatMap P) :
    IsIso (scalarTensorPullModelTarget a f P) := by
  have : IsIso (Functor.tensorModelTargetWith (CondensedRing.upperStar Λ f) (L Λ f)
      (pullCounit (Λ := Λ) f) (B₀ a Y) P) := by
    have h := Functor.tensorModelTarget_isIso (CondensedRing.upperStar Λ f) (B₀ a Y) P hP
    unfold Functor.tensorModelTarget at h
    exact h
  unfold scalarTensorPullModelTarget
  infer_instance

/-- The normalized restricted scalar pullback square is the canonical tensor square.

Source: Stacks Tags 07A4, 0D6D, 0D6E, 07A6, 06YY and 06YP;
blueprint integral proper-base-change proof, paragraphs (1) and (3).
(auxiliary; not a blueprint node).

Proof:
1. Choose flat-term K-flat P resolving M and Q resolving the restricted regular coefficient in
degree zero. Exact pullback preserves both. Tensoring the augmentation of Q by P is a quasi-
isomorphism on both sites, including after pullback.

2. TensorNormalized and PullNormalized identify the left side on the representatives with the
ordinary balanced scalar/pullback square. The canonical derived tensor comparison is the
localization of the ordinary total comparison, and the fixed section equivalence preserves these
representatives and maps.

3. Apply the ordinary and homotopy tensor square for arbitrary condensed coefficient maps.
Equivalently both balanced maps send pulled-back x tensor s to pulled-back x tensor c(s). The
regular coefficient is in degree zero, so no sign occurs.

4. Localize the equality and cancel the representative isomorphisms. Naturality along a resolution
of each arbitrary argument gives the desired equation. This never cancels tensoring an arbitrary
resolution with a nonflat coefficient; only the K-flat comparisons of the first step
are inverted. -/
theorem scalar_tensor_pull_normalization (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hY : TensorNormalized a Y tY)
    (hlam : PullNormalized a f lam) :
  let b := Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' f) (V a X) ≪≫
    CondensedRing.derivedComapUpperStarIso a f ≪≫
    Functor.isoWhiskerLeft (V a Y)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm
  let vY : (V a Y).obj (𝟙_ (DerivedCategory (Modules Λ' Y))) ≅ B a Y :=
    cast (by rfl) <| (V₀ a Y).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (Modules Λ' Y) 0).obj
        (Mod.regular (condensedRingObj Λ' Y))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (V₀ a Y) (.up ℤ) 0).app
        (Mod.regular (condensedRingObj Λ' Y)))
  let vX : (V a X).obj (𝟙_ (DerivedCategory (Modules Λ' X))) ≅ B a X :=
    cast (by rfl) <| (V₀ a X).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (Modules Λ' X) 0).obj
        (Mod.regular (condensedRingObj Λ' X))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (V₀ a X) (.up ℤ) 0).app
        (Mod.regular (condensedRingObj Λ' X)))
  let c := (L Λ f).mapIso vY.symm ≪≫
    b.symm.app (𝟙_ (DerivedCategory (Modules Λ' Y))) ≪≫
    (V a X).mapIso (CondensedRing.leftDerivedUpperStarUnitIso Λ' f) ≪≫ vX
  ∀ M : DerivedCategory (Modules Λ Y),
    b.inv.app ((D a Y).obj M) ≫
        (V a X).map (lam.hom.app M) ≫ tX.derived.hom.app ((L Λ f).obj M) =
      (L Λ f).map (tY.derived.hom.app M) ≫
        ((CondensedRing.leftDerivedUpperStarTensor Λ f).app M).app (B a Y) ≫
        ((L Λ f).obj M ◁ c.hom) := by
  let b := scalarTensorRestrictPullIso a f
  let c := scalarTensorRegularPullIso a f
  let α : D a Y ⋙ V a Y ⋙ L Λ f ⟶ L Λ f ⋙ tensorRight (B a X) :=
    Functor.whiskerLeft (D a Y) b.hom ≫
      Functor.whiskerRight lam.hom (V a X) ≫
      Functor.whiskerLeft (L Λ f) tX.derived.hom
  let δ : tensorRight (B a Y) ⋙ L Λ f ⟶
      L Λ f ⋙ tensorRight ((L Λ f).obj (B a Y)) :=
    { app M := ((CondensedRing.leftDerivedUpperStarTensor Λ f).app M).app (B a Y)
      naturality M N q := by
        exact NatTrans.congr_app ((CondensedRing.leftDerivedUpperStarTensor Λ f).naturality q)
          (B a Y) }
  let β : D a Y ⋙ V a Y ⋙ L Λ f ⟶ L Λ f ⋙ tensorRight (B a X) :=
    Functor.whiskerRight tY.derived.hom (L Λ f) ≫ δ ≫
      Functor.whiskerLeft (L Λ f)
        ((curriedTensor (DerivedCategory (Modules Λ X))).flip.map c.hom)
  change ∀ M, α.app M = β.app M
  intro M
  have : (CondensedRing.upperStar Λ f).PreservesFlat := CondensedRing.upperStar_preservesFlat Λ f
  obtain ⟨P, hP, ⟨e⟩⟩ := (CondensedRing.upperStar Λ f).exists_kFlatMap_iso M
  have h : α.app (DerivedCategory.Qh.obj P) = β.app (DerivedCategory.Qh.obj P) := by
    have := modelTarget_isIso a f P hP
    apply (cancel_mono (scalarTensorPullModelTarget a f P)).mp
    simpa only [α, β, δ, b, c, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.flip_map_app, curriedTensor_obj_map,
      Category.assoc] using
      (scalar_pull_route_model a f tX lam hX hlam P).trans
        (tensor_pull_route_model a f tY hY P).symm
  have hn := α.naturality e.hom
  rw [h, ← β.naturality e.hom] at hn
  exact (cancel_epi ((D a Y ⋙ V a Y ⋙ L Λ f).map e.hom)).mp hn

end AlgebraicGeometry.ProEtale.QuotientChange
