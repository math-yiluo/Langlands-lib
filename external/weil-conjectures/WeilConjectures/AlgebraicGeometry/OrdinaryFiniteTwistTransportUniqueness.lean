/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Uniqueness of normalized finite Tate transport

Source: blueprint vector integration, normalized Tate comparisons; Stacks Project,
Tags 03PK and 03Q1.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

private noncomputable def muHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleMuModulePresheaf T N ⟶
      P.obj ⋙ ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) where
  toFun f := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (f.app U).hom.toAddMonoidHom
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }⟩
  invFun f := {
    app := fun U ↦ ModuleCat.ofHom
      (X := finiteEtaleMuModuleObj T N U)
      (Y := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
      (AddMonoidHom.toZModLinearMap N
        (M := finiteEtaleMuModuleObj T N U)
        (M₁ := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
        (f.hom.app U).hom)
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private noncomputable def lineHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ P) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) :=
  ((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ P).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).whiskerRight
      T.Etaleᵒᵖ).homEquiv _ P.obj).trans (muHomEquiv T N A hA P))

private lemma lineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ P) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf N).obj.obj U) :
    (lineHomEquiv T N A hA P f).hom.app U z =
      f.hom.app U (finiteEtaleTateOneGenerator A N T hA U 1 z) := by
  dsimp [lineHomEquiv, muHomEquiv]
  change ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).homEquiv _ _
        ((toSheafify T.smallEtaleTopology _ ≫ f.hom).app U)) z = _
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The normalized roots inclusion and pure coefficient generators determine Tate
transport uniquely, even without a chosen system of identity and composition laws.
Source: Stacks Project, Tags 03PK and 03Q1; blueprint vector integration, canonical
coefficient identifications.
(auxiliary; not a blueprint node).

Proof: cancel the monomorphism from roots of unity to units to identify the roots
comparisons. For a coefficient comparison, transpose under inverse image/direct image.
Sheafification and scalar extension identify maps out of the Tate line with maps out
of the roots sheaf; this correspondence evaluates at the pure generator 1 tensor z.
The two normalization equations and the already identified roots comparison give
equality on these generators, hence equality of the transposes and the line maps.
Function extensionality and proof irrelevance identify the records. The proof also
covers the empty scheme, zero coefficient ring, and N=1. -/
theorem ordinaryFiniteTwistTransport_unique (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t t' : OrdinaryFiniteTwistTransport A N hA) :
    t = t' := by
  have hr : @t.roots = @t'.roots := by
    funext X Y f hY
    apply Iso.ext
    apply (cancel_mono (kernel.ι (N • 𝟙 X.gmSheaf))).mp
    exact (t.roots_normalization f hY).symm.trans (t'.roots_normalization f hY)
  have hl : @t.line = @t'.line := by
    funext X Y f hY
    apply Iso.ext
    apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
    apply (Scheme.lineHomEquiv Y N A hA _).injective
    ext W z
    simp only [Scheme.lineHomEquiv_generator]
    rw [t.line_normalization, t'.line_normalization]
    rw [hr]
  cases t
  cases t'
  cases hr
  cases hl
  rfl

end AlgebraicGeometry.Etale
