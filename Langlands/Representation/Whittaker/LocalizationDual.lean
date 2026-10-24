import Langlands.Representation.Whittaker.Algebraic
import Langlands.Representation.Jacquet.Localization

/-! # Equivariant functionals as the dual of character-localized coinvariants -/

noncomputable section

namespace Langlands.Whittaker

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- The quotient universal property identifies equivariant functionals with the full
algebraic dual of the actual character-localized quotient. -/
def functionalsLocalizationDualEquiv (U : Subgroup G) (θ : U →* Rˣ)
    (ρ : Representation R G V) :
    functionals U θ ρ ≃ₗ[R] Module.Dual R (Jacquet.Localization.Coinvariants ρ U θ) where
  toFun ℓ := Jacquet.Localization.lift ρ U θ ℓ.val (fun u v => ℓ.property u v)
  invFun f := ⟨f.comp (Jacquet.Localization.mk ρ U θ), by
    intro u v
    change f (Jacquet.Localization.mk ρ U θ (ρ u v)) = (θ u : R) * f (Jacquet.Localization.mk ρ U θ v)
    rw [Jacquet.Localization.mk_apply_subgroup, map_smul, smul_eq_mul]⟩
  left_inv ℓ := by
    apply Subtype.ext
    ext v
    rfl
  right_inv f := by
    apply Jacquet.Localization.hom_ext
    rfl
  map_add' ℓ m := by
    apply Jacquet.Localization.hom_ext
    rfl
  map_smul' a ℓ := by
    apply Jacquet.Localization.hom_ext
    rfl

/-- Evaluation on the quotient class recovers the supplied functional. -/
@[simp] theorem functionalsLocalizationDualEquiv_mk (U : Subgroup G) (θ : U →* Rˣ)
    (ρ : Representation R G V) (ℓ : functionals U θ ρ) (v : V) :
    functionalsLocalizationDualEquiv U θ ρ ℓ (Jacquet.Localization.mk ρ U θ v) = ℓ.val v := rfl

/-- The inverse is precisely precomposition with the canonical quotient map. -/
@[simp] theorem functionalsLocalizationDualEquiv_symm_val (U : Subgroup G) (θ : U →* Rˣ)
    (ρ : Representation R G V) (f : Module.Dual R (Jacquet.Localization.Coinvariants ρ U θ)) :
    ((functionalsLocalizationDualEquiv U θ ρ).symm f).val =
      f.comp (Jacquet.Localization.mk ρ U θ) := rfl

@[simp] theorem functionalsLocalizationDualEquiv_symm_apply (U : Subgroup G) (θ : U →* Rˣ)
    (ρ : Representation R G V) (f : Module.Dual R (Jacquet.Localization.Coinvariants ρ U θ))
    (v : V) :
    ((functionalsLocalizationDualEquiv U θ ρ).symm f).val v =
      f (Jacquet.Localization.mk ρ U θ v) := rfl

end Langlands.Whittaker
