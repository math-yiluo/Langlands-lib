/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedPullbackSquareTensorCoherence

/-! # Base change preserves the direct-image tensor pairing
Source: Stacks Project, cohomology.tex Tag 08I3 and Remark 08HY;
duality.tex Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-tensor-pairing-base-change-identity).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Identity-pairing coherence for the canonical base-change mate.
Source: Stacks Project, cohomology.tex, Remark 08HY and Lemma 079U;
duality.tex, Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-tensor-pairing-base-change-identity).

Proof: transpose under the upper pullback/direct-image adjunction and expand the
base-change mates. Counit naturality and triangle identities reduce the equality
to compatibility of the pullback-composition comparisons with normalized tensorators.
On K-flat representatives, termwise composition comparisons and tensorators carry
pure tensors to the same pulled-back sections. The normalization equations and
invertible K-flat derived counits transport the equality to the derived category.
K-flat resolutions and naturality extend it to arbitrary A and B. No base-change
map is cancelled or assumed invertible. -/
theorem mixedTensorPairing_baseChange_identity
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (A B : schemeDerivedCategory X) :
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition A ⊗ₘ
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition B) ≫
      ((schemeHomPullbackAdjunction (pullback.snd f g)).homEquiv _ _
        ((mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
          ((schemeDerivedDirectImage (pullback.snd f g)).obj
              ((derivedPullback (pullback.fst f g)).obj A),
           (schemeDerivedDirectImage (pullback.snd f g)).obj
              ((derivedPullback (pullback.fst f g)).obj B)) ≫
          ((schemeHomPullbackAdjunction (pullback.snd f g)).counit.app
              ((derivedPullback (pullback.fst f g)).obj A) ⊗ₘ
           (schemeHomPullbackAdjunction (pullback.snd f g)).counit.app
              ((derivedPullback (pullback.fst f g)).obj B)))) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (A, B)) =
    (mixedHomTensorPullbackIso g).inv.app
        ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
      (derivedPullback g).map
        (((schemeHomPullbackAdjunction f).homEquiv _ _
      ((mixedHomTensorPullbackIso f).hom.app
        ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
        ((schemeHomPullbackAdjunction f).counit.app A ⊗ₘ
          (schemeHomPullbackAdjunction f).counit.app B)))) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (A ⊗ B) := by
  -- Use the same pinned adjunctions and square comparison as the base-change mate.
  let F := derivedPullback f
  let R := schemeDerivedDirectImage f
  let L := derivedPullback g
  let H := derivedPullback (pullback.fst f g)
  let F' := derivedPullback (pullback.snd f g)
  let p := schemeHomPullbackAdjunction f
  let p' := schemeHomPullbackAdjunction (pullback.snd f g)
  let α := (mixedPullbackSquareComparison f g).hom
  let β (M : schemeDerivedCategory X) :=
    schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition M
  have hb (M : schemeDerivedCategory X) :
      F'.map (β M) ≫ p'.counit.app (H.obj M) =
        α.app (R.obj M) ≫ H.map (p.counit.app M) := by
    change (p'.homEquiv _ _).symm (p'.homEquiv _ _ _) = _
    rw [Equiv.symm_apply_apply]
    dsimp [α, mixedPullbackSquareComparison, R, H, p,
      schemeHomPullbackAdjunction]
    simp only [Category.assoc, eqToHom_app]
  -- Transpose the upper pairing, without cancelling either base-change map.
  apply (p'.homEquiv _ _).symm.injective
  rw [← Category.assoc]
  rw [p'.homEquiv_naturality_right_symm,
    p'.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Category.assoc]
  change F'.map (β A ⊗ₘ β B) ≫
      (mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
        ((schemeDerivedDirectImage (pullback.snd f g)).obj (H.obj A),
         (schemeDerivedDirectImage (pullback.snd f g)).obj (H.obj B)) ≫
      (p'.counit.app (H.obj A) ⊗ₘ p'.counit.app (H.obj B)) ≫
      (mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (A, B) = _
  rw [p'.homEquiv_naturality_left_symm]
  rw [p'.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit]
  change _ = F'.map ((mixedHomTensorPullbackIso g).inv.app (R.obj A, R.obj B)) ≫
    F'.map (L.map _) ≫ F'.map (β (A ⊗ B)) ≫ p'.counit.app (H.obj (A ⊗ B))
  rw [hb]
  let q := p.homEquiv _ _
    ((mixedHomTensorPullbackIso f).hom.app (R.obj A, R.obj B) ≫
      (p.counit.app A ⊗ₘ p.counit.app B))
  have hq : F.map q ≫ p.counit.app (A ⊗ B) =
      (mixedHomTensorPullbackIso f).hom.app (R.obj A, R.obj B) ≫
        (p.counit.app A ⊗ₘ p.counit.app B) := by
    exact (p.homEquiv _ _).symm_apply_apply _
  have hn := (mixedHomTensorPullbackIso (pullback.snd f g)).hom.naturality
    (X := (L.obj (R.obj A), L.obj (R.obj B)))
    (Y := ((schemeDerivedDirectImage (pullback.snd f g)).obj (H.obj A),
      (schemeDerivedDirectImage (pullback.snd f g)).obj (H.obj B))) (β A, β B)
  change F'.map (β A ⊗ₘ β B) ≫ _ =
    (mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
      (L.obj (R.obj A), L.obj (R.obj B)) ≫ (F'.map (β A) ⊗ₘ F'.map (β B)) at hn
  rw [reassoc_of% hn]
  rw [tensorHom_comp_tensorHom_assoc, hb, hb]
  have ha := α.naturality q
  change F'.map (L.map q) ≫ α.app (R.obj (A ⊗ B)) =
    α.app (R.obj A ⊗ R.obj B) ≫ H.map (F.map q) at ha
  change _ = F'.map ((mixedHomTensorPullbackIso g).inv.app (R.obj A, R.obj B)) ≫
    F'.map (L.map q) ≫ α.app (R.obj (A ⊗ B)) ≫ H.map (p.counit.app (A ⊗ B))
  rw [reassoc_of% ha, ← H.map_comp, hq, H.map_comp]
  rw [← tensorHom_comp_tensorHom_assoc]
  -- The only cancellation is a pullback tensorator isomorphism.
  apply (cancel_epi (F'.map ((mixedHomTensorPullbackIso g).hom.app
    (R.obj A, R.obj B)))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  rw [reassoc_of% (mixedPullbackSquareComparison_tensor f g (R.obj A) (R.obj B))]
  have ht := (mixedHomTensorPullbackIso (pullback.fst f g)).hom.naturality
    (X := (F.obj (R.obj A), F.obj (R.obj B))) (Y := (A, B))
    (p.counit.app A, p.counit.app B)
  change H.map (p.counit.app A ⊗ₘ p.counit.app B) ≫
      (mixedHomTensorPullbackIso (pullback.fst f g)).hom.app (A, B) =
    (mixedHomTensorPullbackIso (pullback.fst f g)).hom.app
      (F.obj (R.obj A), F.obj (R.obj B)) ≫
      (H.map (p.counit.app A) ⊗ₘ H.map (p.counit.app B)) at ht
  rw [← reassoc_of% ht]
  simp only [Iso.hom_inv_id_app]
  change α.app (R.obj A ⊗ R.obj B) ≫
    H.map ((mixedHomTensorPullbackIso f).hom.app (R.obj A, R.obj B)) ≫
    H.map (p.counit.app A ⊗ₘ p.counit.app B) ≫ 𝟙 (H.obj (A ⊗ B)) =
    F'.map (𝟙 (L.obj (R.obj A ⊗ R.obj B))) ≫
      α.app (R.obj A ⊗ R.obj B) ≫
      H.map ((mixedHomTensorPullbackIso f).hom.app (R.obj A, R.obj B)) ≫
      H.map (p.counit.app A ⊗ₘ p.counit.app B)
  have hleft := congrArg
    (fun k ↦ α.app (R.obj A ⊗ R.obj B) ≫
      H.map ((mixedHomTensorPullbackIso f).hom.app (R.obj A, R.obj B)) ≫ k)
    (Category.comp_id (H.map (p.counit.app A ⊗ₘ p.counit.app B)))
  have hright := congrArg
    (fun k ↦ k ≫ α.app (R.obj A ⊗ R.obj B) ≫
      H.map ((mixedHomTensorPullbackIso f).hom.app (R.obj A, R.obj B)) ≫
      H.map (p.counit.app A ⊗ₘ p.counit.app B))
    (F'.map_id (L.obj (R.obj A ⊗ R.obj B)))
  exact hleft.trans (hright.trans (Category.id_comp _)).symm


end AlgebraicGeometry
