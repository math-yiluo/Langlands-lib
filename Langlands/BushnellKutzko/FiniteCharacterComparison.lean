import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Comparing families of characters on a finite abelian group -/

namespace Langlands

universe uX uY

/-- Suppose that `a` and `b` are homomorphisms into the complex character group of a
finite abelian group. If the characters in the image of `b` separate points and
`ker a ⊆ ker b`, every character is in the image of `a`.

This is the character-counting step used to prove transitivity on extensions of a
character by a comparison pairing. -/
def FiniteCharacterComparisonStatement : Prop :=
  ∀ {X : Type uX} {Y : Type uY} [AddCommGroup X] [AddCommGroup Y] [Finite Y]
    (a b : X →+ AddChar Y ℂ), a.ker ≤ b.ker →
      (∀ y, (∀ x, b x y = 1) → y = 0) → Function.Surjective a

/-- Evaluation embeds the finite group into the dual of the comparison image.
The kernel inclusion gives a surjection from the image of `a` onto that image. -/
theorem surjective_of_character_separation : FiniteCharacterComparisonStatement.{uX, uY} := by
  intro X Y _ _ _ a b hker hsep
  classical
  let := Fintype.ofFinite Y
  let := Fintype.ofFinite a.range
  let := Fintype.ofFinite b.range
  let ev : Y →+ AddChar b.range ℂ :=
    { toFun := fun y => (AddChar.doubleDualEmb y).compAddMonoidHom b.range.subtype
      map_zero' := by ext z; exact z.val.map_zero_eq_one
      map_add' := fun y y' => by ext z; exact z.val.map_add_eq_mul y y' }
  have hev : Function.Injective ev := by
    refine ev.ker_eq_bot_iff.mp (eq_bot_iff.mpr fun y hy => hsep y fun x => ?_)
    exact congrArg (fun χ : AddChar b.range ℂ => χ (b.rangeRestrict x))
      (AddMonoidHom.mem_ker.mp hy)
  have hab : a.rangeRestrict.ker ≤ b.rangeRestrict.ker := by
    rwa [AddMonoidHom.ker_rangeRestrict, AddMonoidHom.ker_rangeRestrict]
  let f := a.rangeRestrict.liftOfSurjective a.rangeRestrict_surjective ⟨b.rangeRestrict, hab⟩
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := b.rangeRestrict_surjective z
    exact ⟨a.rangeRestrict x, by simp [f]⟩
  have hcard : Nat.card (AddChar Y ℂ) ≤ Nat.card a.range := by
    simp only [Nat.card_eq_fintype_card, AddChar.card_eq]
    exact (by simpa only [AddChar.card_eq] using Fintype.card_le_of_injective ev hev :
      Fintype.card Y ≤ Fintype.card b.range).trans (Fintype.card_le_of_surjective f hf)
  have ha : Function.Injective a.range.subtype := Subtype.coe_injective
  exact (ha.bijective_of_nat_card_le hcard).2.comp a.rangeRestrict_surjective

end Langlands
