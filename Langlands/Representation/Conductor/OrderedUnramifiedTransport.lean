import Langlands.Representation.Jacquet.LocalizationTransport
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Whittaker.LocalizationDual
import Langlands.Group.GL.Mirabolic
import Langlands.HarmonicAnalysis.CharacterTransport

/-!
# Transport of Whittaker coinvariants along equivalences

Let `e : π ≃ ρ` be an equivalence of representations of `GL_(n+1)(F)` and `θ` a
character of the upper unipotent subgroup. Then:

* the image under `e` of a nonzero subrepresentation `K` of `π` is a nonzero
  subrepresentation of the restriction of `ρ` to the mirabolic subgroup. If its
  mirabolic `θ`-coinvariants are nonzero, so are the `θ`-coinvariants of `K`;
* the spaces of `θ`-functionals of `π` and `ρ` have the same dimension.

The standard character of `x ↦ ψ(-x)` is the inverse standard character of `ψ`.
-/

noncomputable section

namespace Langlands.Conductor.OrderedUnramifiedTransport

open Langlands.GeneralLinear Langlands.Jacquet.Localization Langlands.Whittaker
open Langlands.HarmonicAnalysis

universe uF uV uW

section Transport

variable {F : Type uF} [CommRing F] {n : ℕ}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- The image of a subrepresentation of `π` under an equivalence `e : π ≃ ρ`, as a
subrepresentation of the restriction of `ρ` to the mirabolic subgroup. -/
def mirabolicImage (e : π.Equiv ρ) (K : Subrepresentation π) :
    Subrepresentation (ρ.comp (mirabolic n F).subtype) where
  toSubmodule := K.toSubmodule.map e.toLinearEquiv.toLinearMap
  apply_mem_toSubmodule g w hw := by
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨π (g : Langlands.GeneralLinear (n + 1) F) v, K.apply_mem_toSubmodule _ hv,
      LinearMap.congr_fun (e.isIntertwining' (g : Langlands.GeneralLinear (n + 1) F)) v⟩

theorem mirabolicImage_ne_bot (e : π.Equiv ρ) {K : Subrepresentation π} (hK : K ≠ ⊥) :
    mirabolicImage e K ≠ ⊥ := by
  intro h
  apply hK
  apply Subrepresentation.toSubmodule_injective
  change K.toSubmodule = ⊥
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hmem : e.toLinearEquiv v ∈ (mirabolicImage e K).toSubmodule := ⟨v, hv, rfl⟩
  rw [h] at hmem
  change e.toLinearEquiv v ∈ (⊥ : Submodule ℂ W) at hmem
  exact e.toLinearEquiv.map_eq_zero_iff.1 ((Submodule.mem_bot ℂ).1 hmem)

/-- The linear identification of the mirabolic image with the subrepresentation. -/
def imageEquiv (e : π.Equiv ρ) (K : Subrepresentation π) :
    (mirabolicImage e K).toSubmodule ≃ₗ[ℂ] K.toSubmodule :=
  (e.toLinearEquiv.submoduleMap K.toSubmodule).symm

/-- Nonzero mirabolic `θ`-coinvariants of the image give nonzero `θ`-coinvariants of
the subrepresentation. -/
theorem nontrivial_coinvariants_of_mirabolicImage (e : π.Equiv ρ) (K : Subrepresentation π)
    (θ : upperUnipotent (n + 1) F →* ℂˣ)
    (h : Nontrivial (Coinvariants (mirabolicImage e K).toRepresentation
      (Mirabolic.upperUnipotent n F) (θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom))) :
    Nontrivial (Coinvariants K.toRepresentation (upperUnipotent (n + 1) F) θ) := by
  let E := transportEquiv (mirabolicImage e K).toRepresentation K.toRepresentation
    (Mirabolic.upperUnipotent n F) (upperUnipotent (n + 1) F)
    (θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) θ
    Mirabolic.upperUnipotentEquiv (imageEquiv e K)
    (fun u v => Subtype.ext
      (LinearMap.congr_fun (e.symm.isIntertwining'
        ((u : mirabolic n F) : Langlands.GeneralLinear (n + 1) F)) v.val))
    (fun _ => rfl)
  exact @Equiv.nontrivial _ _ E.symm.toEquiv h

/-- Nonzero subrepresentations of `π` have nonzero `θ`-coinvariants when every nonzero
mirabolic subrepresentation of `ρ` has nonzero mirabolic `θ`-coinvariants. -/
theorem nontrivial_coinvariants_of_equiv (e : π.Equiv ρ) (θ : upperUnipotent (n + 1) F →* ℂˣ)
    (hρ : ∀ U : Subrepresentation (ρ.comp (mirabolic n F).subtype), U ≠ ⊥ →
      Nontrivial (Coinvariants U.toRepresentation (Mirabolic.upperUnipotent n F)
        (θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom)))
    (K : Subrepresentation π) (hK : K ≠ ⊥) :
    Nontrivial (Coinvariants K.toRepresentation (upperUnipotent (n + 1) F) θ) :=
  nontrivial_coinvariants_of_mirabolicImage e K θ
    (hρ _ (mirabolicImage_ne_bot e hK))

/-- Equivalent representations have linearly equivalent `θ`-coinvariants. -/
def coinvariantsEquiv (e : π.Equiv ρ) (θ : upperUnipotent (n + 1) F →* ℂˣ) :
    Coinvariants π (upperUnipotent (n + 1) F) θ ≃ₗ[ℂ]
      Coinvariants ρ (upperUnipotent (n + 1) F) θ :=
  transportEquiv π ρ (upperUnipotent (n + 1) F) (upperUnipotent (n + 1) F) θ θ
    (MulEquiv.refl _) e.toLinearEquiv
    (fun u v => LinearMap.congr_fun (e.isIntertwining' (u : Langlands.GeneralLinear (n + 1) F)) v)
    (fun _ => rfl)

/-- Equivalent representations have `θ`-functional spaces of equal dimension. -/
theorem finrank_functionals_eq (e : π.Equiv ρ) (θ : upperUnipotent (n + 1) F →* ℂˣ) :
    Module.finrank ℂ (functionals (upperUnipotent (n + 1) F) θ π) =
      Module.finrank ℂ (functionals (upperUnipotent (n + 1) F) θ ρ) :=
  LinearEquiv.finrank_eq ((functionalsLocalizationDualEquiv _ θ π).trans
    ((coinvariantsEquiv e θ).symm.dualMap.trans
      (functionalsLocalizationDualEquiv _ θ ρ).symm))

end Transport

section Character

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The standard character of `x ↦ ψ(-x)` is the inverse standard character of `ψ`. -/
theorem standardCharacter_scale_neg_one (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n := by
  ext u
  rw [standardCharacter_apply, inverseStandardCharacter_apply,
    UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.complex_apply,
    UnitaryAdditiveCharacter.scale_apply, Units.val_neg, Units.val_one, neg_one_mul,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

end Character

end Langlands.Conductor.OrderedUnramifiedTransport
