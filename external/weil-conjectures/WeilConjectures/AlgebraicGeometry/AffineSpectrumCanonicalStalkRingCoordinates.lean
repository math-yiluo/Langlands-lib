/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Canonical ring coordinates for affine spectrum replacement

Source: Stacks Project, Tags 0098 and 0096.
(blueprint: lem-pc-affine-spectrum-canonical-stalk-ring-coordinates).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem stalkCongr_eqToHom (Y : Scheme.{u}) (y y' : Y) (h : y = y') :
    (Y.presheaf.stalkCongr (.of_eq h)).hom = eqToHom (congrArg Y.presheaf.stalk h) := by
  subst y'
  simp [TopCat.Presheaf.stalkCongr]

/-- The actual affine-spectrum stalk ring map, with its source point transported.
Source: Stacks Project, Tag 0098; Mathlib `isoSpec_inv_naturality`.
(blueprint: lem-pc-affine-spectrum-canonical-stalk-ring-coordinates). -/
@[irreducible]
noncomputable def canonicalSpectrumStalkEquiv
    (Y : Scheme.{u}) [IsAffine Y] (y : Y) (y0 : Spec Γ(Y, ⊤))
    (h : y = Y.isoSpec.inv y0) : Y.presheaf.stalk y ≃+* (Spec Γ(Y, ⊤)).presheaf.stalk y0 :=
  ((eqToIso (congrArg Y.presheaf.stalk h)) ≪≫
    asIso (Y.isoSpec.inv.stalkMap y0)).commRingCatIsoToRingEquiv

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem canonicalSpectrumStalkEquiv_naturality
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (x : X) (x0 : Spec Γ(X, ⊤)) (hx : x = X.isoSpec.inv x0)
    (hy : f x = Y.isoSpec.inv ((Spec.map f.appTop) x0)) :
    (canonicalSpectrumStalkEquiv X x x0 hx).toRingHom.comp (f.stalkMap x).hom =
      ((Spec.map f.appTop).stalkMap x0).hom.comp
        (canonicalSpectrumStalkEquiv Y (f x) ((Spec.map f.appTop) x0) hy).toRingHom := by
  subst x
  have h := Scheme.Hom.stalkMap_congr_hom
    (X.isoSpec.inv ≫ f) (Spec.map f.appTop ≫ Y.isoSpec.inv)
    (Scheme.isoSpec_inv_naturality f).symm x0
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
  unfold canonicalSpectrumStalkEquiv
  change (f.stalkMap (X.isoSpec.inv x0) ≫ X.isoSpec.inv.stalkMap x0).hom =
    (eqToHom (congrArg Y.presheaf.stalk hy) ≫
      Y.isoSpec.inv.stalkMap ((Spec.map f.appTop) x0) ≫
      (Spec.map f.appTop).stalkMap x0).hom
  have hc := stalkCongr_eqToHom Y (f (X.isoSpec.inv x0))
    (Y.isoSpec.inv ((Spec.map f.appTop) x0)) hy
  rw [hc] at h
  exact congrArg CommRingCat.Hom.hom h

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem canonicalSpectrumStalkEquiv_congr
    (Y : Scheme.{u}) [IsAffine Y] (y y' : Y) (y0 y0' : Spec Γ(Y, ⊤))
    (hy : y = Y.isoSpec.inv y0) (hy' : y' = Y.isoSpec.inv y0')
    (h : y = y') (h0 : y0 = y0') (r : Y.presheaf.stalk y) :
    canonicalSpectrumStalkEquiv Y y' y0' hy' ((Y.presheaf.stalkCongr (.of_eq h)).hom r) =
      ((Spec Γ(Y, ⊤)).presheaf.stalkCongr (.of_eq h0)).hom
        (canonicalSpectrumStalkEquiv Y y y0 hy r) := by
  cases h
  cases h0
  simp only [stalkCongr_eqToHom, eqToHom_refl, CommRingCat.id_apply]

private theorem tensorMap_tmul
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    ∀ (a : A g' z) (b : B f' z),
      tensorMap f f' g g' sq z (a ⊗ₜ[R f g' z] b) =
        (g'.stalkMap z).hom a * (f'.stalkMap z).hom b := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  intro a b
  have hl := (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1
  have hr := (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).2
  have h (a : A g' z) (b : B f' z) :
      a ⊗ₜ[R f g' z] b =
        algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z) a *
          Algebra.TensorProduct.includeRight b := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, map_mul]
  exact congrArg₂ (· * ·) (RingHom.congr_fun hl a) (RingHom.congr_fun hr b)

/-- Compatibility of the canonical affine-spectrum stalk ring maps.
Proof: use the stalk maps of the four isoSpec inverses, with the point equalities
from isoSpec naturality. The composition law for stalk maps gives the R-to-A and
R-to-B equations. The defining two restrictions of tensorMap express its value
on a pure tensor as the product of the two projection images. Naturality of the
projection stalk maps and preservation of multiplication give the last equation.
No complex isomorphism is asserted or chosen.
Source: Stacks Project, Tags 0098 and 0096.
(blueprint: lem-pc-affine-spectrum-canonical-stalk-ring-coordinates). -/
theorem exists_canonicalSpectrum_stalk_ring_coordinates
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) :
    let z := X'.isoSpec.inv z0
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let D0 := C z0
    let hA : g' z = X.isoSpec.inv ((Spec.map g'.appTop) z0) :=
      (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X ↦ k z0)
        (Scheme.isoSpec_inv_naturality g')).symm
    let eA := canonicalSpectrumStalkEquiv X (g' z) ((Spec.map g'.appTop) z0) hA
    let eD := canonicalSpectrumStalkEquiv X' z z0 rfl
    ∃ (eR : R f g' z ≃+* R0) (eB : B f' z ≃+* B0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) := by
  dsimp only
  let z := X'.isoSpec.inv z0
  let f0 := Spec.map f.appTop
  let f0' := Spec.map f'.appTop
  let g0 := Spec.map g.appTop
  let g0' := Spec.map g'.appTop
  have hA : g' z = X.isoSpec.inv (g0' z0) :=
    (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X => k z0)
      (Scheme.isoSpec_inv_naturality g')).symm
  have hB : f' z = S'.isoSpec.inv (f0' z0) :=
    (congrArg (fun k : Spec Γ(X', ⊤) ⟶ S' => k z0)
      (Scheme.isoSpec_inv_naturality f')).symm
  have hR : f (g' z) = S.isoSpec.inv (f0 (g0' z0)) := by
    rw [hA]
    exact (congrArg (fun k : Spec Γ(X, ⊤) ⟶ S => k (g0' z0))
      (Scheme.isoSpec_inv_naturality f)).symm
  have hR' : g (f' z) = S.isoSpec.inv (g0 (f0' z0)) := by
    rw [hB]
    exact (congrArg (fun k : Spec Γ(S', ⊤) ⟶ S => k (f0' z0))
      (Scheme.isoSpec_inv_naturality g)).symm
  let eA := canonicalSpectrumStalkEquiv X (g' z) (g0' z0) hA
  let eB := canonicalSpectrumStalkEquiv S' (f' z) (f0' z0) hB
  let eR := canonicalSpectrumStalkEquiv S (f (g' z)) (f0 (g0' z0)) hR
  let eD := canonicalSpectrumStalkEquiv X' z z0 rfl
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := leftAlgebra f0 g0' z0
  let := rightAlgebra f0 f0' g0 g0' sq0 z0
  refine ⟨eR, eB, ?_, ?_, ?_⟩
  · intro r
    exact RingHom.congr_fun (canonicalSpectrumStalkEquiv_naturality f (g' z) (g0' z0) hA hR) r
  · intro r
    have h : f (g' z) = g (f' z) :=
      congrArg (fun k : X' ⟶ S => k z) sq.w
    have h0 : f0 (g0' z0) = g0 (f0' z0) :=
      congrArg (fun k : Spec Γ(X', ⊤) ⟶ Spec Γ(S, ⊤) => k z0) sq0.w
    change eB ((g.stalkMap (f' z)).hom
      ((S.presheaf.stalkCongr (.of_eq h)).hom r)) =
      (g0.stalkMap (f0' z0)).hom
        (((Spec Γ(S, ⊤)).presheaf.stalkCongr (.of_eq h0)).hom (eR r))
    exact (RingHom.congr_fun
      (canonicalSpectrumStalkEquiv_naturality g (f' z) (f0' z0) hB hR')
        ((S.presheaf.stalkCongr (.of_eq h)).hom r)).trans
      (congrArg (g0.stalkMap (f0' z0)).hom
        (canonicalSpectrumStalkEquiv_congr S (f (g' z)) (g (f' z))
          (f0 (g0' z0)) (g0 (f0' z0)) hR hR' h h0 r))
  · intro a b
    change eD (tensorMap f f' g g' sq z (a ⊗ₜ[R f g' z] b)) =
      tensorMap f0 f0' g0 g0' sq0 z0
        (eA a ⊗ₜ[R f0 g0' z0] eB b)
    rw [tensorMap_tmul, map_mul, tensorMap_tmul]
    exact congrArg₂ (· * ·)
      (RingHom.congr_fun (canonicalSpectrumStalkEquiv_naturality g' z z0 rfl hA) a)
      (RingHom.congr_fun (canonicalSpectrumStalkEquiv_naturality f' z z0 rfl hB) b)


end AlgebraicGeometry.SingleComplexBaseChange
