import Langlands.Weil.Representation.Twist
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Twists of an extension across a finite cyclic quotient -/

noncomputable section

universe uK uG uV uW

set_option autoImplicit false

namespace Langlands.FiniteRepresentation

/-- Every intertwining endomorphism is a scalar on the actual carrier. -/
def HasScalarEndomorphisms {K : Type uK} {G : Type uG} [Field K] [Group G]
    (A : FiniteRepresentation.{uK, uG, uV} K G) : Prop :=
  ∀ f : A.representation.IntertwiningMap A.representation,
    ∃ a : K, f.toLinearMap = a • LinearMap.id

/-- The extensions of a nonzero restriction with scalar endomorphisms are
exactly the pairwise distinct twists by the powers of a faithful character of
the finite cyclic quotient. The two extension carriers may have independent
universes. -/
def CyclicExtensionTwistClassificationStatement : Prop :=
  ∀ (K : Type uK) (G : Type uG) [Field K] [Group G]
    (N : Subgroup G) [N.Normal] [N.FiniteIndex] [IsCyclic (G ⧸ N)]
    (η : G ⧸ N →* Kˣ), Function.Injective η →
    ∀ (A : FiniteRepresentation.{uK, uG, uV} K G),
      A.rank ≠ 0 → HasScalarEndomorphisms (of (A.representation.comp N.subtype)) →
      ∀ (B : FiniteRepresentation.{uK, uG, uW} K G),
        Nonempty (Equiv (of (A.representation.comp N.subtype))
          (of (B.representation.comp N.subtype))) ↔
        ∃! i : Fin (Nat.card (G ⧸ N)),
          Nonempty (Equiv (twist ((η ^ (i : ℕ)).comp (QuotientGroup.mk' N)) A) B)

end Langlands.FiniteRepresentation
