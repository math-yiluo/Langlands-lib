/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Invertible modules on a scheme and their tensor product

An `𝒪_X`-module is *invertible* if it is locally isomorphic to `𝒪_X`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsInvertible`: an `𝒪_X`-module locally isomorphic to `𝒪_X`.
- The symmetric monoidal category structure on `X.Modules`, from
  `SheafOfModules.monoidalCategory`: the tensor product `M ⊗ N` is the tensor product over
  `𝒪_X`, the sheafification of the tensor product of the underlying presheaves of modules.
- `AlgebraicGeometry.Scheme.Modules.tensorObj`: the tensor product `M ⊗_{𝒪_X} N`, i.e. `M ⊗ N`,
  with scoped notation `M ⊗ₘ N`.
- `AlgebraicGeometry.Scheme.Modules.tensorPow`: the tensor power `M^{⊗ n}`.
- `AlgebraicGeometry.Scheme.Modules.tensorPowAddIso`,
  `AlgebraicGeometry.Scheme.Modules.tensorPowMulIso`,
  `AlgebraicGeometry.Scheme.Modules.tensorPowTensorObjIso`: the exponent laws for tensor powers.
- `AlgebraicGeometry.Scheme.Modules.overPullback`: pullback along a morphism of schemes over a
  base.

## Main results

- `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`: the pullback of an invertible module
  along any morphism of schemes is invertible.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit`: on a scheme with a single
  point every invertible module is trivial.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.not_isZero`: an invertible module on a nonempty
  scheme is not zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module is *invertible* if every point has an open neighbourhood on which it
restricts to the structure sheaf, that is, if it is locally free of rank one for the Zariski
topology. An invertible module `M` has the tensor inverse `Mᵛ = ℋom(M, 𝒪_X)`
(`AlgebraicGeometry.Scheme.Modules.exists_tensorObj_iso_unit`). -/
class IsInvertible (M : X.Modules) : Prop where
  /-- Every point has an open neighbourhood on which `M` restricts to the structure sheaf. -/
  exists_isoUnit : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit _)

/-- **The pullback of an invertible module is invertible.** For `g : X ⟶ Y` and an invertible
`𝒪_Y`-module `M`, the pullback `g^* M` is invertible. -/
instance IsInvertible.pullback {Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) [M.IsInvertible] :
    ((Scheme.Modules.pullback g).obj M).IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) (g.base x)
    exact ⟨g ⁻¹ᵁ U, hx, ⟨(pullbackComp (g ⁻¹ᵁ U).ι g).app M ≪≫
      (pullbackCongr (morphismRestrict_ι g U).symm).app M ≪≫
      ((pullbackComp (g ∣_ U) U.ι).symm).app M ≪≫
      (Scheme.Modules.pullback (g ∣_ U)).mapIso e ≪≫ pullbackObjUnitIso (g ∣_ U)⟩⟩

/-- Invertibility of an `𝒪_X`-module only depends on its isomorphism class. -/
lemma IsInvertible.of_iso {M N : X.Modules} (e : M ≅ N) [M.IsInvertible] : N.IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, ⟨e'⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
    exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ e'⟩⟩

/-- On a scheme with a single point `x`, every invertible module is trivial. -/
lemma IsInvertible.nonempty_iso_unit [Subsingleton X] (x : X) (M : X.Modules)
    [M.IsInvertible] : Nonempty (M ≅ SheafOfModules.unit _) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun y _ ↦ by rwa [Subsingleton.elim y x]
  exact ⟨((pullbackId X).app M).symm ≪≫ (pullbackCongr (Scheme.toIso_inv_ι X).symm).app M ≪≫
    (pullbackComp _ _).symm.app M ≪≫ (Scheme.Modules.pullback X.topIso.inv).mapIso e ≪≫
    pullbackObjUnitIso _⟩

/-- The structure sheaf of a nonempty scheme is not zero. -/
lemma not_isZero_unit (X : Scheme.{u}) [Nonempty X] :
    ¬ IsZero (SheafOfModules.unit X.ringCatSheaf) := by
  intro h
  have h₁ := congr_arg (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ _ ↦ f.val.app (Opposite.op ⊤))
    (h.eq_of_src (𝟙 _) 0)
  have h₂ : (1 : Γ(X, ⊤)) = 0 := congr_arg (fun g ↦ g.hom (1 : Γ(X, ⊤))) h₁
  obtain ⟨x⟩ := ‹Nonempty X›
  have h₃ := congr_arg (X.presheaf.germ ⊤ x trivial).hom h₂
  rw [map_one, map_zero] at h₃
  exact one_ne_zero h₃

/-- An invertible module on a nonempty scheme is not zero. -/
lemma IsInvertible.not_isZero [Nonempty X] (M : X.Modules) [M.IsInvertible] : ¬ IsZero M := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hx, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  exact not_isZero_unit U (((Scheme.Modules.pullback U.ι).map_isZero h).of_iso e.symm)

/-- The monoidal category structure on `𝒪_X`-modules: the tensor product over `𝒪_X`.
This uses that `X.ringCatSheaf` is by definition the underlying sheaf of rings
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf` of `X.sheaf`. -/
noncomputable instance : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The monoidal category structure on `𝒪_X`-modules is symmetric. -/
noncomputable instance : SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategory X.sheaf

/-- The structure sheaf, the unit of the tensor product, is invertible. -/
instance isInvertible_tensorUnit : (𝟙_ X.Modules).IsInvertible where
  exists_isoUnit _ := ⟨⊤, trivial, ⟨pullbackObjUnitIso _⟩⟩

/-- The tensor product `M ⊗_{𝒪_X} N` of two `𝒪_X`-modules: the sheafification of the tensor
product of the underlying presheaves of modules (`SheafOfModules.tensorObjIsoSheafification`).
It is the tensor product `M ⊗ N` of the monoidal category `X.Modules`. -/
noncomputable abbrev tensorObj (M N : X.Modules) : X.Modules :=
  M ⊗ N

@[inherit_doc] scoped infixl:70 " ⊗ₘ " => AlgebraicGeometry.Scheme.Modules.tensorObj

/-- Pullback of an `𝒪_B`-module along a morphism `f : A ⟶ B` of schemes over a base `S`. -/
noncomputable abbrev overPullback {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    (L : B.left.Modules) : A.left.Modules :=
  (Scheme.Modules.pullback f.left).obj L

/-- The `n`-th tensor power `M^{⊗ n}` of an `𝒪_X`-module: `M^{⊗ 0} = 𝟙_ X.Modules` and
`M^{⊗ (n + 1)} = M ⊗ M^{⊗ n}`. -/
noncomputable def tensorPow (M : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => M ⊗ tensorPow M n

@[simp]
lemma tensorPow_zero (M : X.Modules) : M.tensorPow 0 = 𝟙_ X.Modules :=
  rfl

lemma tensorPow_succ (M : X.Modules) (n : ℕ) : M.tensorPow (n + 1) = M ⊗ M.tensorPow n :=
  rfl

/-- `M^{⊗ (a + b)} ≅ M^{⊗ a} ⊗ M^{⊗ b}`. -/
noncomputable def tensorPowAddIso (M : X.Modules) :
    ∀ a b : ℕ, M.tensorPow (a + b) ≅ M.tensorPow a ⊗ M.tensorPow b
  | 0, b => eqToIso (congrArg M.tensorPow (Nat.zero_add b)) ≪≫ (λ_ _).symm
  | a + 1, b => eqToIso (congrArg M.tensorPow (Nat.succ_add a b)) ≪≫
      (Iso.refl M ⊗ᵢ tensorPowAddIso M a b) ≪≫ (α_ _ _ _).symm

/-- `M^{⊗ (a * b)} ≅ (M^{⊗ a})^{⊗ b}`. -/
noncomputable def tensorPowMulIso (M : X.Modules) (a : ℕ) :
    ∀ b : ℕ, M.tensorPow (a * b) ≅ (M.tensorPow a).tensorPow b
  | 0 => eqToIso (congrArg M.tensorPow (Nat.mul_zero a))
  | b + 1 => eqToIso (congrArg M.tensorPow (by ring)) ≪≫ tensorPowAddIso M a (a * b) ≪≫
      (Iso.refl _ ⊗ᵢ tensorPowMulIso M a b)

/-- `(M ⊗ N)^{⊗ k} ≅ M^{⊗ k} ⊗ N^{⊗ k}`, using the symmetry of the tensor product. -/
noncomputable def tensorPowTensorObjIso (M N : X.Modules) :
    ∀ k : ℕ, (M ⊗ N).tensorPow k ≅ M.tensorPow k ⊗ N.tensorPow k
  | 0 => (λ_ _).symm
  | k + 1 => (Iso.refl _ ⊗ᵢ tensorPowTensorObjIso M N k) ≪≫
      { hom := tensorμ _ _ _ _, inv := tensorδ _ _ _ _ }

end Scheme.Modules

end AlgebraicGeometry
