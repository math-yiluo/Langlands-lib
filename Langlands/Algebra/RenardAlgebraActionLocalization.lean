import Langlands.Algebra.CompatibleNonUnitalAction
import Langlands.Algebra.RenardEndomorphismLocalization

/-!
# Compatible algebra actions on actual endomorphism localization

Construction content for the last sentence of Renard A.III.1, example 5
(9 July 2026, printed p. 252 / PDF p. 258). The algebra and its action may
be nonunital. The B-linear universal property is a separate successor.
-/

set_option autoImplicit false

universe u v w

noncomputable section

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization

section CommutingEndomorphism

variable {k : Type u} [CommRing k] {V : Type w} [AddCommGroup V] [Module k V]

/-- Extend a commuting endomorphism to the existing localization carrier. -/
def extendEnd (a f : Module.End k V) (hf : ∀ z, f (a z) = a (f z)) :
    Module.End k (Localized a) :=
  factor a (localizedEnd a) (isUnit_localizedEnd a) ((iota a).comp f)
    (fun z => by
      change iota a (f (a z)) = localizedEnd a (iota a (f z))
      rw [hf, iota_intertwines])

/-- The extension commutes with the actual localized operator. -/
theorem extendEnd_localizedEnd (a f : Module.End k V)
    (hf : ∀ z, f (a z) = a (f z)) (z : Localized a) :
    extendEnd a f hf (localizedEnd a z) = localizedEnd a (extendEnd a f hf z) :=
  factor_intertwines a (localizedEnd a) (isUnit_localizedEnd a) _ _ z

/-- The extension restricts to the original endomorphism after the canonical map. -/
theorem extendEnd_comp_iota (a f : Module.End k V)
    (hf : ∀ z, f (a z) = a (f z)) :
    (extendEnd a f hf).comp (iota a) = (iota a).comp f :=
  factor_comp_iota a (localizedEnd a) (isUnit_localizedEnd a) _ _

@[simp] theorem extendEnd_iota (a f : Module.End k V)
    (hf : ∀ z, f (a z) = a (f z)) (z : V) :
    extendEnd a f hf (iota a z) = iota a (f z) :=
  LinearMap.congr_fun (extendEnd_comp_iota a f hf) z

/-- On an actual fraction, the extension applies the map to the numerator. -/
theorem extendEnd_frac (a f : Module.End k V)
    (hf : ∀ z, f (a z) = a (f z)) (z : V) (n : ℕ) :
    extendEnd a f hf (frac a z n) = frac a (f z) n := by
  have hn : Function.Injective (localizedEnd a ^ n) := by
    rw [Module.End.coe_pow]
    exact (localizedEquiv a).injective.iterate n
  apply hn
  rw [pow_apply_frac a (localizedEnd a) (extendEnd a f hf)
    (extendEnd_localizedEnd a f hf), extendEnd_iota, localizedEnd_pow_frac]

/-- The extension also commutes with the inverse localized operator. -/
theorem extendEnd_localizedInv (a f : Module.End k V)
    (hf : ∀ z, f (a z) = a (f z)) (z : Localized a) :
    extendEnd a f hf (localizedInv a z) = localizedInv a (extendEnd a f hf z) := by
  apply (localizedEquiv a).injective
  change localizedEnd a (extendEnd a f hf (localizedInv a z)) =
    localizedEnd a (localizedInv a (extendEnd a f hf z))
  rw [← extendEnd_localizedEnd, localizedEnd_localizedInv, localizedEnd_localizedInv]

/-- The extension is the only endomorphism commuting with the localized operator and
restricting to the original endomorphism after the canonical map. -/
theorem extendEnd_unique (a f : Module.End k V) (hf : ∀ z, f (a z) = a (f z))
    (g : Module.End k (Localized a))
    (hg : ∀ z, g (localizedEnd a z) = localizedEnd a (g z))
    (hgf : g.comp (iota a) = (iota a).comp f) :
    g = extendEnd a f hf :=
  factor_unique a (localizedEnd a) (isUnit_localizedEnd a) _ _ g hg hgf

private theorem frac_zero_numerator (a : Module.End k V) (n : ℕ) :
    frac a (0 : V) n = 0 := by
  rw [frac_eq_localizedInv_pow, map_zero, map_zero]

end CommutingEndomorphism

section Action

variable {k : Type u} [CommRing k] {B : Type v} [NonUnitalRing B] [Module k B]
  {V : Type w} [AddCommGroup V] [Module k V]

/-- The actual nonunital algebra action on the existing `Localized a`. -/
def localizedAction (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    B →ₙₐ[k] Module.End k (Localized a) where
  toFun b := extendEnd a (ρ b) (fun z => (ha b z).symm)
  map_zero' := by
    ext x
    obtain ⟨z, n, rfl⟩ := frac_surjective a x
    simp only [extendEnd_frac, map_zero, LinearMap.zero_apply, frac_zero_numerator]
  map_add' b c := by
    ext x
    obtain ⟨z, n, rfl⟩ := frac_surjective a x
    simp only [extendEnd_frac, map_add, LinearMap.add_apply, frac_add]
  map_mul' b c := by
    ext x
    obtain ⟨z, n, rfl⟩ := frac_surjective a x
    simp only [extendEnd_frac, map_mul, Module.End.mul_apply]
  map_smul' c b := by
    ext x
    obtain ⟨z, n, rfl⟩ := frac_surjective a x
    simp only [extendEnd_frac, map_smul, LinearMap.smul_apply, frac_smul,
      MonoidHom.id_apply]

@[simp] theorem localizedAction_frac (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (b : B) (z : V) (n : ℕ) :
    localizedAction a ρ ha b (frac a z n) = frac a (ρ b z) n :=
  extendEnd_frac a (ρ b) (fun z => (ha b z).symm) z n

@[simp] theorem localizedAction_iota (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (b : B) (z : V) :
    localizedAction a ρ ha b (iota a z) = iota a (ρ b z) :=
  extendEnd_iota a (ρ b) (fun z => (ha b z).symm) z

theorem localizedAction_localizedEnd (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (b : B) (z : Localized a) :
    localizedAction a ρ ha b (localizedEnd a z) =
      localizedEnd a (localizedAction a ρ ha b z) :=
  extendEnd_localizedEnd a (ρ b) (fun z => (ha b z).symm) z

theorem localizedAction_localizedInv (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (b : B) (z : Localized a) :
    localizedAction a ρ ha b (localizedInv a z) =
      localizedInv a (localizedAction a ρ ha b z) :=
  extendEnd_localizedInv a (ρ b) (fun z => (ha b z).symm) z

/-- The localized action is the only homomorphism whose action maps commute with the
localized operator and extend the original action along the canonical map. -/
theorem localizedAction_unique (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (σ : B →ₙₐ[k] Module.End k (Localized a))
    (hσ : ∀ b z, σ b (localizedEnd a z) = localizedEnd a (σ b z))
    (hσι : ∀ b z, σ b (iota a z) = iota a (ρ b z)) :
    σ = localizedAction a ρ ha :=
  NonUnitalAlgHom.ext fun b =>
    extendEnd_unique a (ρ b) (fun z => (ha b z).symm) (σ b) (hσ b)
      (LinearMap.ext (hσι b))

/-- The actual canonical map, as a linear intertwiner of the two actions. -/
def iotaIntertwiner (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    LinearIntertwiner ρ (localizedAction a ρ ha) where
  toLinearMap := iota a
  map_action' b z := (localizedAction_iota a ρ ha b z).symm

/-- The actual localized operator, as a linear intertwiner. -/
def localizedEndIntertwiner (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    LinearIntertwiner (localizedAction a ρ ha) (localizedAction a ρ ha) where
  toLinearMap := localizedEnd a
  map_action' b z := (localizedAction_localizedEnd a ρ ha b z).symm

/-- The actual inverse localized operator, as a linear intertwiner. -/
def localizedInvIntertwiner (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    LinearIntertwiner (localizedAction a ρ ha) (localizedAction a ρ ha) where
  toLinearMap := localizedInv a
  map_action' b z := (localizedAction_localizedInv a ρ ha b z).symm

@[simp] theorem iotaIntertwiner_toLinearMap (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    (iotaIntertwiner a ρ ha).toLinearMap = iota a := rfl

@[simp] theorem localizedEndIntertwiner_toLinearMap (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    (localizedEndIntertwiner a ρ ha).toLinearMap = localizedEnd a := rfl

@[simp] theorem localizedInvIntertwiner_toLinearMap (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    (localizedInvIntertwiner a ρ ha).toLinearMap = localizedInv a := rfl

/-- Named ambient action adapter; this is not a global instance. -/
abbrev localizedModule (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) : NonUnitalModule B (Localized a) :=
  NonUnitalModule.ofLinearEndHom (localizedAction a ρ ha)

theorem localizedModule_smul (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) (b : B) (z : Localized a) :
    (letI := localizedModule a ρ ha; b • z) = localizedAction a ρ ha b z := rfl

/-- Named scalar-tower adapter for the localized ambient action. -/
theorem localizedModule_isScalarTower (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    letI := localizedModule a ρ ha
    IsScalarTower k B (Localized a) :=
  NonUnitalModule.ofLinearEndHom_isScalarTower (localizedAction a ρ ha)

/-- Named commuting-action adapter for the localized ambient action. -/
theorem localizedModule_smulCommClass (a : Module.End k V)
    (ρ : B →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    letI := localizedModule a ρ ha
    SMulCommClass k B (Localized a) :=
  NonUnitalModule.ofLinearEndHom_smulCommClass (localizedAction a ρ ha)

/-- The zero action remains the zero homomorphism after localization. -/
theorem localizedAction_zero (a : Module.End k V) :
    localizedAction a (0 : B →ₙₐ[k] Module.End k V) (by intro b z; simp) = 0 := by
  ext b x
  obtain ⟨z, n, rfl⟩ := frac_surjective a x
  simp only [localizedAction_frac, NonUnitalAlgHom.zero_apply, LinearMap.zero_apply,
    frac_zero_numerator]

/-- The corresponding ambient action is exactly the published zero action. -/
theorem localizedModule_zero (a : Module.End k V) :
    localizedModule a (0 : B →ₙₐ[k] Module.End k V) (by intro b z; simp) =
      NonUnitalModule.zero := by
  change NonUnitalModule.ofLinearEndHom _ = _
  rw [localizedAction_zero, NonUnitalModule.ofLinearEndHom_zero]

end Action

/-- Conditional unit law: if B has a unit acting as the identity, so does its localization.
This is an intrinsic specialization; the main constructor assumes no unit. -/
theorem localizedAction_one {k : Type u} [CommRing k] {B : Type v} [Ring B] [Module k B]
    {V : Type w} [AddCommGroup V] [Module k V]
    (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) (h1 : ρ 1 = 1) :
    localizedAction a ρ ha 1 = 1 := by
  ext x
  obtain ⟨z, n, rfl⟩ := frac_surjective a x
  simp only [localizedAction_frac, h1, Module.End.one_apply]

/-- Source-facing constructor with the complete bilinear nonunital algebra interface. -/
def fieldLocalizedAction {k : Type u} [Field k] {B : Type v} [NonUnitalRing B]
    [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
    {V : Type w} [AddCommGroup V] [Module k V]
    (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    B →ₙₐ[k] Module.End k (Localized a) :=
  localizedAction a ρ ha

/-- The field constructor has the fraction formula, without finiteness or unit hypotheses. -/
theorem fieldLocalizedAction_frac {k : Type u} [Field k] {B : Type v} [NonUnitalRing B]
    [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
    {V : Type w} [AddCommGroup V] [Module k V]
    (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) (b : B) (z : V) (n : ℕ) :
    fieldLocalizedAction a ρ ha b (frac a z n) = frac a (ρ b z) n :=
  localizedAction_frac a ρ ha b z n

/-- The field constructor is the general constructor, so all its laws apply. -/
theorem fieldLocalizedAction_eq {k : Type u} [Field k] {B : Type v} [NonUnitalRing B]
    [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
    {V : Type w} [AddCommGroup V] [Module k V]
    (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    fieldLocalizedAction a ρ ha = localizedAction a ρ ha :=
  rfl

/-- The field constructor has the canonical-map formula. -/
theorem fieldLocalizedAction_iota {k : Type u} [Field k] {B : Type v} [NonUnitalRing B]
    [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
    {V : Type w} [AddCommGroup V] [Module k V]
    (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) (b : B) (z : V) :
    fieldLocalizedAction a ρ ha b (iota a z) = iota a (ρ b z) :=
  localizedAction_iota a ρ ha b z

end Langlands.Renard.AlgebraActionLocalization
