/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-!
# Morphisms of invertible modules are isomorphisms if they are nonzero on fibres

A morphism `β : P ⟶ Q` of invertible `𝒪_X`-modules is locally multiplication by a function `b`;
it is an isomorphism near every point `x` at which `b(x) ≠ 0`, that is, at which the pullback of
`β` to `Spec κ(x)` is nonzero.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_pullback_ne_zero`: a morphism of
  invertible modules whose pullbacks to all residue fields are nonzero is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A function vanishing at `x` maps to zero in the residue field `κ(x)`: its image under
`Spec κ(x) ⟶ X` is zero. -/
lemma appLE_fromSpecResidueField_eq_zero {U : X.Opens} {x : X} (b : Γ(X, U))
    (hb : x ∉ X.basicOpen b) (h : ⊤ ≤ X.fromSpecResidueField x ⁻¹ᵁ U) :
    (X.fromSpecResidueField x).appLE U ⊤ h b = 0 := by
  have hbot : (Spec (X.residueField x)).basicOpen
      ((X.fromSpecResidueField x).appLE U ⊤ h b) = ⊥ := by
    rw [Scheme.basicOpen_appLE, top_inf_eq, eq_bot_iff]
    rintro y hy
    apply hb
    change X.fromSpecResidueField x y ∈ X.basicOpen b at hy
    rwa [Scheme.fromSpecResidueField_apply] at hy
  exact (basicOpen_eq_bot_iff _).mp hbot
variable {P Q : X.Modules} [SheafOfModules.IsInvertible.{u, u, u} P]
  [SheafOfModules.IsInvertible.{u, u, u} Q]

/-- **Isomorphisms of invertible modules are detected on fibres.** A morphism `β : P ⟶ Q` of
invertible `𝒪_X`-modules is an isomorphism as soon as its pullback to `Spec κ(x)` is nonzero for
every point `x` of `X`. Locally `β` is multiplication by a function `b`; its pullback to
`Spec κ(x)` is multiplication by `b(x)`, so `b` is invertible near every point. -/
theorem Hom.isIso_of_forall_pullback_ne_zero (β : P ⟶ Q)
    (h : ∀ x : X, (pullback (X.fromSpecResidueField x)).map β ≠ 0) : IsIso β := by
  refine Hom.isIso_of_forall_bijective_app β fun x ↦ ?_
  obtain ⟨U, hxU, -, ⟨eP, hP⟩, eQ, hQ⟩ :=
    exists_isFreeGenerator₂ P Q (TopologicalSpace.Opens.mem_top x)
  obtain ⟨b, hb⟩ := hQ.exists_smul_eq (β.app U.1 eP)
  have hxb : x ∈ X.basicOpen b := by
    by_contra hxb
    apply h x
    have : SheafOfModules.IsInvertible.{u, u, u}
        ((pullback (X.fromSpecResidueField x)).obj P) := .pullback inferInstance
    have : SheafOfModules.IsInvertible.{u, u, u}
        ((pullback (X.fromSpecResidueField x)).obj Q) := .pullback inferInstance
    rw [← Hom.zeroLocus_eq_bot_iff, ← Hom.comap_zeroLocus]
    have hU : ⊤ ≤ X.fromSpecResidueField x ⁻¹ᵁ U.1 := by
      rintro y -
      change X.fromSpecResidueField x y ∈ U.1
      rw [Scheme.fromSpecResidueField_apply]
      exact hxU
    refine le_bot_iff.mp (Scheme.IdealSheafData.le_of_iSup_eq_top
      (fun _ : Unit ↦ (⟨⊤, isAffineOpen_top _⟩ : (Spec (X.residueField x)).affineOpens))
      (by simp) fun _ ↦ ?_)
    rw [Scheme.IdealSheafData.ideal_comap_appLE _ _ U ⟨⊤, isAffineOpen_top _⟩ hU,
      Hom.ideal_zeroLocus β U hP hQ hb.symm, Ideal.map_span, Set.image_singleton,
      appLE_fromSpecResidueField_eq_zero b hxb hU]
    simp
  refine ⟨X.basicOpen b, hxb, fun W hW ↦ ?_⟩
  have hWU : W ≤ U.1 := hW.trans (X.basicOpen_le b)
  have hunit : IsUnit (X.presheaf.map (homOfLE hWU).op b) := by
    have h' := (RingedSpace.isUnit_res_basicOpen X.toRingedSpace b).map
      (X.presheaf.map (homOfLE hW).op).hom
    convert h' using 1
    change _ = (X.presheaf.map (homOfLE (X.basicOpen_le b)).op ≫ X.presheaf.map (homOfLE hW).op) b
    rw [← Functor.map_comp]
    rfl
  have hβ (r : Γ(X, W)) : β.app W (r • P.presheaf.map (homOfLE hWU).op eP) =
      (r * X.presheaf.map (homOfLE hWU).op b) • Q.presheaf.map (homOfLE hWU).op eQ := by
    rw [Hom.app_smul, Hom.app_presheaf_map, ← hb, mul_smul]
    rw [map_smul]
  have key : β.app W ∘ (fun r : Γ(X, W) ↦ r • P.presheaf.map (homOfLE hWU).op eP) =
      (fun r : Γ(X, W) ↦ r • Q.presheaf.map (homOfLE hWU).op eQ) ∘
        (fun r ↦ r * X.presheaf.map (homOfLE hWU).op b) := funext hβ
  have hmul : Function.Bijective (fun r : Γ(X, W) ↦ r * X.presheaf.map (homOfLE hWU).op b) :=
    (hunit.unit.mulRight).bijective
  refine (Function.Bijective.of_comp_iff _ (hP.map hWU).bijective).mp ?_
  rw [key]
  exact (hQ.map hWU).bijective.comp hmul

end AlgebraicGeometry.Scheme.Modules
