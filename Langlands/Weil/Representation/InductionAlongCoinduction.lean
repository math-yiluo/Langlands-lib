import Langlands.WeilDeligne.InductionAlong
import Langlands.Weil.Representation.Invariants

noncomputable section

namespace Langlands.InductionAlong

universe uK uG uH uV

variable {K : Type uK} {G : Type uG} {H : Type uH}
  [Field K] [Group G] [Group H]

open FiniteRepresentation

/-- The subgroup-range model of induction and coinduction along the original
injective map have exactly the same equivariant functions. -/
def rangeCoinductionEquiv (ι : H →* G) (hι : Function.Injective ι)
    (A : FiniteRepresentation.{uK, uH, uV} K H) :
    Representation.coindV ι.range.subtype (restrict (rangeInverse ι hι) A).representation ≃ₗ[K]
      Representation.coindV ι A.representation where
  toFun f := ⟨f.val, by
    intro h g
    have hf := f.property (⟨ι h, h, rfl⟩ : ι.range) g
    change f.val (ι h * g) =
      A.representation (rangeInverse ι hι ⟨ι h, h, rfl⟩) (f.val g) at hf
    rw [rangeInverse_apply] at hf
    exact hf⟩
  invFun f := ⟨f.val, by
    intro h g
    have hf := f.property (rangeInverse ι hι h) g
    rw [apply_rangeInverse] at hf
    exact hf⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem rangeCoinductionEquiv_apply (ι : H →* G) (hι : Function.Injective ι)
    (A : FiniteRepresentation.{uK, uH, uV} K H)
    (f : Representation.coindV ι.range.subtype
      (restrict (rangeInverse ι hι) A).representation) (g : G) :
    (rangeCoinductionEquiv ι hι A f).val g = f.val g := rfl

/-- The range comparison commutes with the ambient group action. -/
theorem rangeCoinductionEquiv_action (ι : H →* G) (hι : Function.Injective ι)
    (A : FiniteRepresentation.{uK, uH, uV} K H) (g : G)
    (f : Representation.coindV ι.range.subtype
      (restrict (rangeInverse ι hι) A).representation) :
    rangeCoinductionEquiv ι hι A
        (Representation.coind ι.range.subtype
          (restrict (rangeInverse ι hι) A).representation g f) =
      Representation.coind ι A.representation g (rangeCoinductionEquiv ι hι A f) := rfl

/-- Inertia invariants of the actual `induceAlong` carry over to the
coinduction space along the original map. -/
def invariantCoinductionEquiv (ι : H →* G) (hι : Function.Injective ι)
    [ι.range.FiniteIndex] (I : Subgroup G) [I.Normal]
    (A : FiniteRepresentation.{uK, uH, uV} K H) :
    invariants I (induceAlong ι hι A) ≃ₗ[K]
      Representation.invariants ((Representation.coind ι A.representation).comp I.subtype) where
  toFun f := ⟨rangeCoinductionEquiv ι hι A f.val, by
    intro i
    apply Subtype.ext
    funext g
    exact congrArg (fun x => x.val g) (f.property i)⟩
  invFun f := ⟨(rangeCoinductionEquiv ι hι A).symm f.val, by
    intro i
    apply Subtype.ext
    funext g
    exact congrArg (fun x => x.val g) (f.property i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The invariant-space comparison also intertwines every ambient element. -/
theorem invariantCoinductionEquiv_action (ι : H →* G) (hι : Function.Injective ι)
    [ι.range.FiniteIndex] (I : Subgroup G) [I.Normal]
    (A : FiniteRepresentation.{uK, uH, uV} K H) (g : G)
    (f : invariants I (induceAlong ι hι A)) :
    invariantCoinductionEquiv ι hι I A ((invariants I (induceAlong ι hι A)).representation g f) =
      (Representation.coind ι A.representation).toInvariants I g
        (invariantCoinductionEquiv ι hι I A f) := rfl

end Langlands.InductionAlong
