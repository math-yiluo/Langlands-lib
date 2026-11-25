/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineDescentRingDiagram
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.AffineKFlatPullbackChartComparison
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-! # Sheafification and derived pullback of affine projective models

Source: Stacks Project, Tag 09RF, affine case; Tags 08EB, 06YI and 06YJ.
(blueprint: lem-pc-affine-descent-stage-realization).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem realization_perfect (Y : Scheme.{u}) (A : CommRingCat.{u})
    (r : A ⟶ Γ(Y, ⊤))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite A (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A (P.X n)) :
    Y.IsPerfect ((affineDescentRealization Y A r).obj P) := by
  let T := affineDescentSheafification Y A r
  let q := Y.toSpecΓ ≫ Spec.map r
  let : (tilde.functor A).IsLeftAdjoint := (tilde.adjunction (R := A)).isLeftAdjoint
  let : (Scheme.Modules.pullback q).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction q).isLeftAdjoint
  let L := (T.mapHomologicalComplex (.up ℤ)).obj P
  let F := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) ⊤
  intro x
  refine ⟨⊤, trivial, (F.mapHomologicalComplex (.up ℤ)).obj L, ?_,
    ⟨F.mapDerivedCategoryFactors.app L⟩⟩
  constructor
  · obtain ⟨a, b, hab⟩ := hb
    exact ⟨a, b, fun n hn ↦ F.map_isZero (T.map_isZero (hab n hn))⟩
  · intro n
    have : Module.Finite A (P.X n) := hf n
    have : Module.Projective A (P.X n) := hp n
    obtain ⟨m, f, g, _, _, hfg⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective A (P.X n)
    let c := ((Pi.basisFun A (Fin m)).reindex Equiv.ulift.symm).repr.toModuleIso
    let ef := (Scheme.Modules.pullback q).mapIso (tildeFinsupp (ULift.{u} (Fin m))) ≪≫
      (SheafOfModules.mapFreeIso (Scheme.Modules.pullback q) (ULift.{u} (Fin m))
        (Scheme.Modules.pullbackObjUnitIso q).symm).symm
    let e := F.mapIso (T.mapIso c ≪≫ ef) ≪≫
      (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m)) (Iso.refl _)).symm
    have hsplit : (ModuleCat.ofHom g) ≫ (ModuleCat.ofHom f) = 𝟙 (P.X n) := by
      ext a
      exact congrArg (fun h : (P.X n) →ₗ[A] (P.X n) ↦ h a) hfg
    refine ⟨m, F.map (T.map (ModuleCat.ofHom g)) ≫ e.hom,
      e.inv ≫ F.map (T.map (ModuleCat.ofHom f)), ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, ← T.map_comp,
      hsplit, T.map_id]
    exact F.map_id _

/-- Sheafifying a bounded finite-projective complex at any specified stage is perfect,
and its canonical derived pullback is sheafification of scalar extension to the colimit.
No existence of a stage and no model for a given limit object are asserted here.
Source: Stacks Project, Tag 09RF, affine case; Tags 08EB, 06YI and 06YJ
(blueprint: lem-pc-affine-descent-stage-realization).

Proof: The stage fibre product is affine. Each finite projective module is a retract of
a finite free module. Associated sheaf and pullback along its affine spectrum isomorphism
preserve these retract diagrams and finite support, giving a perfect complex by 08EB.
These projective terms are flat; their bounded complex is K-flat. The canonical counit
of derivedPullback is an isomorphism on this K-flat representative (06YI, 06YJ).
The ordinary affine associated-sheaf base-change isomorphism identifies its termwise
pullback with sheafification of extension of scalars. The global-ring map of the
canonical baseChangeMap equals colimit.ι followed by colimit.desc, by the defining
cocone equation. Thus this base-change isomorphism uses precisely the canonical map
in the assertion. Naturality in module maps makes the termwise isomorphisms commute
with differentials. Apply derived localization and compose with the K-flat counit.
This includes the zero complex, empty affine source, and zero rings. -/
theorem affine_descent_stage_realization
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    (Z : Scheme.{u}) [IsAffine Z] (t : Z ⟶ Spec (R.obj i))
    [hDer : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{u}) (U : Y.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (j : Set.Ici i)
    (P : CochainComplex (ModuleCat.{u} ((affineDescentRings R i t).obj j)) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite ((affineDescentRings R i t).obj j) (P.X n))
    (hp : ∀ n : ℤ, Module.Projective ((affineDescentRings R i t).obj j) (P.X n)) :
    (affineDescentStage R i t j).IsPerfect
      ((affineDescentRealization (affineDescentStage R i t j)
        ((affineDescentRings R i t).obj j) (𝟙 _)).obj P) ∧
    Nonempty ((derivedPullback (affineDescentLimitMap R i t c j)).obj
      ((affineDescentRealization (affineDescentStage R i t j)
        ((affineDescentRings R i t).obj j) (𝟙 _)).obj P) ≅
      (affineDescentRealization (pullback t (Spec.map (c.ι.app i)))
        (colimit (affineDescentRings R i t) : CommRingCat.{u})
        (colimit.desc _ (affineDescentRingCocone R i t c))).obj
          (((ModuleCat.extendScalars
            (colimit.ι (affineDescentRings R i t) j).hom).mapHomologicalComplex
              (.up ℤ)).obj P))  := by
  constructor
  · exact realization_perfect _ _ _ P hb hf hp
  · let Y := affineDescentStage R i t j
    let X := pullback t (Spec.map (c.ι.app i))
    let : HasDerivedCategory.{w} Y.Modules := hDer Y
    let : HasDerivedCategory.{w} X.Modules := hDer X
    let : HasDerivedCategory.{w} (Spec Γ(X, ⊤)).Modules := hDer (Spec Γ(X, ⊤))
    let f : X ⟶ Y := affineDescentLimitMap R i t c j
    let A := Γ(Y, ⊤)
    let B := colimit (affineDescentRings R i t)
    let r : B ⟶ Γ(X, ⊤) := colimit.desc _ (affineDescentRingCocone R i t c)
    let a : A ⟶ B := colimit.ι (affineDescentRings R i t) j
    let : IsAffine Y := by dsimp [Y, affineDescentStage]; infer_instance
    let : IsAffine X := by dsimp [X]; infer_instance
    have ha : a ≫ r = f.appTop := colimit.ι_desc _ j
    let TY := tilde.functor A
    let TX := tilde.functor Γ(X, ⊤)
    let RY := Scheme.Modules.restrictFunctor Y.toSpecΓ
    let RX := Scheme.Modules.restrictFunctor X.toSpecΓ
    have : TY.Additive := ⟨by intros; exact tilde.map_add _ _⟩
    have : TX.Additive := ⟨by intros; exact tilde.map_add _ _⟩
    have hPk : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P := by
      obtain ⟨l, b, hb⟩ := hb
      have : P.IsStrictlyGE l := (P.isStrictlyGE_iff l).2 (fun n hn ↦ hb n (Or.inl hn))
      have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 (fun n hn ↦ hb n (Or.inr hn))
      apply CochainComplex.kFlat_of_bounded_of_flat P l b
      intro n
      have := hp n
      exact (ModuleCat.flat_iff_flat _).2 inferInstance
    obtain ⟨ePull⟩ := affine_kFlat_pullback_chart_comparison.{u, w, w} f P hPk
    let sourceIso : affineDescentSheafification Y A (𝟙 _) ≅ TY ⋙ RY :=
      Functor.isoWhiskerLeft TY
        (Scheme.Modules.pullbackCongr
          (show Y.toSpecΓ ≫ Spec.map (𝟙 A) = Y.toSpecΓ by
            rw [Spec.map_id]; exact Category.comp_id _) ≪≫
          (Scheme.Modules.restrictFunctorIsoPullback Y.toSpecΓ).symm)
    let eSource := (NatIso.mapHomologicalComplex sourceIso (.up ℤ)).app P
    refine ⟨(derivedPullback f).mapIso (DerivedCategory.Q.mapIso eSource) ≪≫ ePull ≪≫ ?_⟩
    let TB := tilde.functor B
    have : TB.Additive := ⟨by intros; exact tilde.map_add _ _⟩
    let targetIso : affineDescentSheafification X B r ≅
        (ModuleCat.extendScalars r.hom ⋙ TX) ⋙ RX :=
      Functor.isoWhiskerLeft TB
        (Scheme.Modules.pullbackComp X.toSpecΓ (Spec.map r)).symm ≪≫
      (Functor.associator TB (Scheme.Modules.pullback (Spec.map r))
        (Scheme.Modules.pullback X.toSpecΓ)).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.tildePullbackIso r)
        (Scheme.Modules.pullback X.toSpecΓ) ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars r.hom ⋙ TX)
        (Scheme.Modules.restrictFunctorIsoPullback X.toSpecΓ).symm
    let ec : ModuleCat.extendScalars f.appTop.hom ≅
        ModuleCat.extendScalars a.hom ⋙ ModuleCat.extendScalars r.hom :=
      eqToIso (congrArg ModuleCat.extendScalars
        (congrArg CommRingCat.Hom.hom ha.symm)) ≪≫
      ModuleCat.extendScalarsComp a.hom r.hom
    let eExt := (NatIso.mapHomologicalComplex ec (.up ℤ)).app P
    let eTarget := (NatIso.mapHomologicalComplex targetIso (.up ℤ)).app
      (((ModuleCat.extendScalars a.hom).mapHomologicalComplex (.up ℤ)).obj P)
    exact ((Functor.mapDerivedCategoryFactors.{w, w} RX).app
        ((TX.mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars f.appTop.hom).mapHomologicalComplex
            (.up ℤ)).obj P))) ≪≫
      DerivedCategory.Q.mapIso ((RX.mapHomologicalComplex (.up ℤ)).mapIso
        ((TX.mapHomologicalComplex (.up ℤ)).mapIso eExt)) ≪≫
      DerivedCategory.Q.mapIso eTarget.symm

end AlgebraicGeometry
