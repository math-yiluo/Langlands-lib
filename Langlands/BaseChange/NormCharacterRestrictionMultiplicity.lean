import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.ClassFieldTheory.Local.Norms
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Restricting finite abelian characters to local norm characters -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open LocalClassField

universe u v w

/-- For a local map into a finite abelian group with kernel the actual norm
subgroup, the restricted characters are exactly the norm-trivial characters.
Every such character has as many extensions as the index of the local image. -/
def NormCharacterRestrictionMultiplicityStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E] [FiniteDimensional F E]
    (G : Type w) [CommGroup G] [Finite G] (rec : Fˣ →* G),
    rec.ker = normSubgroup F E →
    (∀ κ : Fˣ →* ℂˣ, IsNormTrivial E κ ↔ ∃ χ : G →* ℂˣ, χ.comp rec = κ) ∧
    ∀ κ : Fˣ →* ℂˣ, IsNormTrivial E κ →
      Nat.card {χ : G →* ℂˣ // χ.comp rec = κ} = rec.range.index

theorem normCharacterRestrictionMultiplicity : NormCharacterRestrictionMultiplicityStatement.{u, v, w} := by
  intro F _ E _ _ _ G _ _ rec hrec
  let exponent := Monoid.exponent G
  have hexp : exponent ≠ 0 := Monoid.exponent_ne_zero_of_finite (G := G)
  let : NeZero exponent := ⟨hexp⟩
  let : HasEnoughRootsOfUnity ℂ exponent :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp exponent hexp⟩, rootsOfUnity.isCyclic ℂ exponent⟩
  let D := rec.range
  let g := rec.rangeRestrict
  let restriction := MonoidHom.domRestrictHom D ℂˣ
  have hs : Function.Surjective restriction := MonoidHom.domRestrict_surjective (M := ℂ) D
  have extensions (κ : Fˣ →* ℂˣ) (hκ : IsNormTrivial E κ) :
      ∃ δ : D →* ℂˣ, ∀ χ : G →* ℂˣ, χ.comp rec = κ ↔ restriction χ = δ := by
    have hker : g.ker ≤ κ.ker := by
      intro x hx
      have hx' : x ∈ rec.ker := by
        rw [MonoidHom.mem_ker] at hx ⊢
        exact congrArg Subtype.val hx
      rw [hrec] at hx'
      obtain ⟨y, rfl⟩ := hx'
      exact hκ y
    let δ := g.liftOfSurjective rec.rangeRestrict_surjective ⟨κ, hker⟩
    have hδ (x : Fˣ) : δ (g x) = κ x := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
    refine ⟨δ, fun χ => ?_⟩
    constructor
    · intro h
      apply MonoidHom.ext
      intro y
      obtain ⟨x, rfl⟩ := rec.rangeRestrict_surjective y
      change χ (rec x) = δ (g x)
      rw [hδ]
      exact DFunLike.congr_fun h x
    · intro h
      apply MonoidHom.ext
      intro x
      change restriction χ (g x) = κ x
      rw [h, hδ]
  refine ⟨fun κ => ⟨?_, ?_⟩, ?_⟩
  · intro hκ
    obtain ⟨δ, hδ⟩ := extensions κ hκ
    obtain ⟨χ, hχ⟩ := hs δ
    exact ⟨χ, (hδ χ).mpr hχ⟩
  · rintro ⟨χ, rfl⟩ x
    have hx : normUnits F E x ∈ rec.ker := hrec.symm ▸ ⟨x, rfl⟩
    change χ (rec (normUnits F E x)) = 1
    rw [MonoidHom.mem_ker.mp hx, map_one]
  · intro κ hκ
    obtain ⟨δ, hδ⟩ := extensions κ hκ
    obtain ⟨χ₀, hχ₀⟩ := hs δ
    let e : {χ : G →* ℂˣ // restriction χ = δ} ≃ restriction.ker :=
      { toFun := fun χ => ⟨χ.val * χ₀⁻¹, by
          change restriction (χ.val * χ₀⁻¹) = 1
          rw [map_mul, map_inv, χ.property, hχ₀, mul_inv_cancel]⟩
        invFun := fun χ => ⟨χ.val * χ₀, by
          rw [map_mul, MonoidHom.mem_ker.mp χ.property, hχ₀, one_mul]⟩
        left_inv := fun χ => Subtype.ext (inv_mul_cancel_right χ.val χ₀)
        right_inv := fun χ => Subtype.ext (mul_inv_cancel_right χ.val χ₀) }
    calc
      _ = Nat.card restriction.ker :=
        Nat.card_congr ((Equiv.subtypeEquivRight hδ).trans e)
      _ = D.index := (CommGroup.card_domRestrictHom_ker (M := ℂ) D).trans D.index_eq_card.symm

end Langlands.BaseChange
