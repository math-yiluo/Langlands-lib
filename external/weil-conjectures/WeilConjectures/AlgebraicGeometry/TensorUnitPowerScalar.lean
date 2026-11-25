/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-! # Tensor-unit powers and scalar multiplication

Source: Stacks Project, Tag 09MR, tensor-unit specialization of numerator maps.
(blueprint: lem-pc-tensor-unit-power-scalar).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private def unitPowerIso (Y : Scheme.{u}) :
    (n : ℕ) → (𝟙_ Y.Modules).tensorPow n ≅ 𝟙_ Y.Modules
  | 0 => Iso.refl _
  | n + 1 => (Iso.refl _ ⊗ᵢ unitPowerIso Y n) ≪≫ λ_ _

private theorem unitPowerIso_section (Y : Scheme.{u}) (b : Γ(Y, ⊤))
    (n : ℕ) (U : Y.Opens) :
    (unitPowerIso Y n).hom.app U
      (tensorPowSectionOne (homOfGlobalSection (𝟙_ Y.Modules)
        (unitSectionsEquiv ⊤ b)) n U) =
      unitSectionsEquiv U ((Y.presheaf.map (homOfLE le_top).op b) ^ n) := by
  induction n with
  | zero => simp [unitPowerIso, tensorPowSectionOne_zero, Hom.id_app]
  | succ n ih =>
    rw [tensorPowSectionOne_succ]
    simp only [tensorPow, unitPowerIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection, Hom.id_app]
    rw [ih]
    change (λ_ (𝟙_ Y.Modules)).hom.app U
      (tmulSection ((homOfGlobalSection (𝟙_ Y.Modules)
        (unitSectionsEquiv ⊤ b)).app U (1 : Γ(Y, U)))
        (unitSectionsEquiv U ((Y.presheaf.map (homOfLE le_top).op b) ^ n))) = _
    rw [homOfGlobalSection_app_one, presheaf_map_unitSectionsEquiv,
      leftUnitor_hom_app_tmulSection, ← LinearEquiv.map_smul, smul_eq_mul, pow_succ']

/-- Tensor powers of the unit can be removed compatibly with the numerator transition.

Source: Stacks Project, Tag 09MR, numerator maps specialized to the tensor unit.
(blueprint: lem-pc-tensor-unit-power-scalar).

Proof: Identify unit^0 with the unit by the identity, and identify unit^(n+1)
with the unit by tensoring the preceding identification with the identity and
applying the left unitor. Induction shows that the section s^n goes to b^n.
Tensor these isomorphisms with G and apply the right unitor. Precompose the
claimed equation with the inverse of the degree-zero right unitor. A section x
then goes to x tensor 1; the numerator map takes it to x tensor s^n. The
identification takes this to b^n x, as does smulHom. Equality on all sections
proves equality of the sheaf morphisms. This includes n=0, b=0, b a unit,
empty Y, and zero G. -/
theorem tensorUnitPower_scalar (Y : Scheme.{u}) (G : Y.Modules) (b : Γ(Y, ⊤)) :
    let L := 𝟙_ Y.Modules
    let s : Γ(L, ⊤) := unitSectionsEquiv ⊤ b
    ∃ i : ∀ n : ℕ, (G ⊗ L.tensorPow n : Y.Modules) ≅ G,
      ∀ n : ℕ, mulTensorPowSection (homOfGlobalSection L s) G 0 n ≫
        (i (0 + n)).hom = (i 0).hom ≫ G.smulHom (b ^ n) := by
  let i (n : ℕ) : (G ⊗ (𝟙_ Y.Modules).tensorPow n : Y.Modules) ≅ G :=
    (Iso.refl G ⊗ᵢ unitPowerIso Y n) ≪≫ ρ_ G
  refine ⟨i, ?_⟩
  intro n
  apply (cancel_epi (i 0).inv).mp
  ext U x
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  have hzero : (i 0).inv.app U x = tmulSection x (unitSectionsEquiv U 1) := by
    simp [i, unitPowerIso, rightUnitor_inv_app]
  rw [hzero]
  rw [← tensorPowSectionOne_zero
    (homOfGlobalSection (𝟙_ Y.Modules) (unitSectionsEquiv ⊤ b)) U]
  rw [mulTensorPowSection_app_tmulSection]
  simp only [i, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection, Hom.id_app]
  rw [unitPowerIso_section, rightUnitor_hom_app_tmulSection]
  simp [tensorPowSectionOne_zero, unitPowerIso,
    rightUnitor_hom_app_tmulSection, map_pow]

end
end AlgebraicGeometry.Scheme.Modules
