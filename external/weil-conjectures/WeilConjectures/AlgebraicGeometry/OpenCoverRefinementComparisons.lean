/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleRecoveryComparisonIso
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison

/-! # Explicit comparison bundle for refinement of pulled-back open charts

Source: Stacks Project, Tags 0095 and 0096; canonical comparisons in
lem-pc-open-cover-map-lift-transport.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The five explicit comparison isomorphisms for a chart refinement.
This names real constructions from pullback composition, congruence and the
existing tensor comparisons, so that proofs can share their kernel expressions.
Source: Stacks Project, Tags 0095 and 0096; the refinement comparison step of
lem-pc-open-cover-map-lift-transport.
(blueprint: def-pc-open-cover-refinement-comparisons). -/
noncomputable def openCoverRefinementComparisons
    {X Y Z W : Scheme.{u}} (q : Y ⟶ X) (v : Z ⟶ X) (h : W ⟶ X)
    (pk : W ⟶ Y) (pl : W ⟶ Z) (wk : pk ≫ q = h) (wl : pl ≫ v = h)
    (U : X.OpenCover.{u}) (a : U.I₀)
    (d : (U.pullback₁ v).X a ⟶ (U.pullback₁ q).X a)
    (hd : d ≫ U.pullbackHom q a = U.pullbackHom v a)
    (z : ((U.pullback₁ v).pullback₁ pl).X a ⟶
      ((U.pullback₁ q).pullback₁ pk).X a)
    (hz : z ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) pk a =
      Scheme.Cover.pullbackHom (U.pullback₁ v) pl a ≫ d)
    (hz0 : z ≫ ((U.pullback₁ q).pullback₁ pk).f a =
      ((U.pullback₁ v).pullback₁ pl).f a)
    :
    let Uk : Y.OpenCover.{u} := U.pullback₁ q
    let Ul : Z.OpenCover.{u} := U.pullback₁ v
    let Vk : W.OpenCover.{u} := Uk.pullback₁ pk
    let Vl : W.OpenCover.{u} := Ul.pullback₁ pl
    let D := pullback d
    let Pk := pullback (Uk.pullbackHom pk a)
    let Pl := pullback (Ul.pullbackHom pl a)
    let Zf := pullback z
    let Rk := pullback (Vk.f a)
    let Rl := pullback (Vl.f a)
    let Lk := tensorPullback q ⋙ pullback (Uk.f a)
    let Ll := tensorPullback v ⋙ pullback (Ul.f a)
    (Ll ≅ Lk ⋙ D) × (Rk ⋙ Zf ≅ Rl) × (Pk ⋙ Zf ≅ D ⋙ Pl) ×
      (tensorPullback h ⋙ Rk ≅ Lk ⋙ Pk) × (tensorPullback h ⋙ Rl ≅ Ll ⋙ Pl) := by
  intro Uk Ul Vk Vl D Pk Pl Zf Rk Rl Lk Ll
  let ek := tensorPullbackCompositionIso pk q h wk
  let el := tensorPullbackCompositionIso pl v h wl
  let tk := openCoverTensorPullbackComparison pk Uk a
  let tl := openCoverTensorPullbackComparison pl Ul a
  let alpha : Ll ≅ Lk ⋙ D :=
    (openCoverTensorPullbackComparison v U a).symm ≪≫
      Functor.isoWhiskerLeft (pullback (U.f a))
        ((pullbackCongr hd).symm ≪≫ (pullbackComp d (U.pullbackHom q a)).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openCoverTensorPullbackComparison q U a) D
  let beta : Rk ⋙ Zf ≅ Rl := pullbackComp z (Vk.f a) ≪≫ pullbackCongr hz0
  let delta : Pk ⋙ Zf ≅ D ⋙ Pl :=
    pullbackComp z (Uk.pullbackHom pk a) ≪≫ pullbackCongr hz ≪≫
      (pullbackComp (Ul.pullbackHom pl a) d).symm
  let ck := moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback q)
    (tensorPullback pk) (pullback (Uk.f a)) Pk Rk ek tk
  let cl := moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback v)
    (tensorPullback pl) (pullback (Ul.f a)) Pl Rl el tl
  exact ⟨alpha, beta, delta, ck, cl⟩

end AlgebraicGeometry.Scheme.Modules
