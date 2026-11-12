import Langlands.Algebra.NonUnitalModuleLeftLimitAction

/-!
# Direct-limit descriptions of rings and modules with idempotents (Renard I.1.2, I.1.4)

`A = lim_{e ∈ 𝒥} eAe` and, for a nondegenerate module, `M = lim_{e ∈ 𝒥} e·M`, for every
filtering system `𝒥` of idempotents (I.1.2, Definitions and Remark 2), stated as universal
properties of the inclusions. Also the remark of I.1.4 that the completion of a nondegenerate
module need not be nondegenerate.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM uT

/-- Renard I.1.2, reformulation of the Definition and Remark 2, for rings: let `A` be a ring
with idempotents and `J` a filtering system of idempotents (every finite family of idempotents
has an upper bound in `J`). Then `A` is the direct limit of the corners `eAe`, `e ∈ J`, along
the inclusions, both as an abelian group and as a nonunital ring: every family of additive
(resp. nonunital ring) maps on the corners that agree on common elements of `eAe ⊂ fAf`
(`e ≤ f`) extends uniquely to `A`. -/
def IdempotentedRingDirectLimitStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
    ∀ J : Set (Idempotent A),
      (∀ s : Finset (Idempotent A), ∃ f ∈ J, ∀ e ∈ s, e ≤ f) →
      (∀ (T : Type uT) [AddCommGroup T]
          (g : ∀ e ∈ J, e.corner.toAddSubgroup →+ T),
          (∀ e (he : e ∈ J) f (hf : f ∈ J), e ≤ f →
            ∀ (a : A) (hae : a ∈ e.corner) (haf : a ∈ f.corner),
              g e he ⟨a, hae⟩ = g f hf ⟨a, haf⟩) →
          ∃! h : A →+ T, ∀ e (he : e ∈ J) (a : e.corner.toAddSubgroup),
            h a = g e he a) ∧
      (∀ (T : Type uT) [NonUnitalRing T]
          (g : ∀ e ∈ J, e.corner →ₙ+* T),
          (∀ e (he : e ∈ J) f (hf : f ∈ J), e ≤ f →
            ∀ (a : A) (hae : a ∈ e.corner) (haf : a ∈ f.corner),
              g e he ⟨a, hae⟩ = g f hf ⟨a, haf⟩) →
          ∃! h : A →ₙ+* T, ∀ e (he : e ∈ J) (a : e.corner), h a = g e he a)

/-- Renard I.1.2, Definition of nondegenerate modules with its reformulation, and Remark 2,
for modules: let `A` be a ring with idempotents, `J` a filtering system of idempotents and
`M` an original `A`-module. Then `M` is nondegenerate exactly when every vector is fixed by an
idempotent of `J`, and exactly when `M` is the direct limit of the subgroups `e·M`, `e ∈ J`,
along the inclusions: every family of additive maps on the `e·M` that agree on common vectors
for `e ≤ f` extends uniquely to `M`. -/
def NondegenerateModuleDirectLimitStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
    ∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] (J : Set (Idempotent A)),
      (∀ s : Finset (Idempotent A), ∃ f ∈ J, ∀ e ∈ s, e ≤ f) →
      (IsNondegenerate A M ↔ ∀ m : M, ∃ e ∈ J, (e : A) • m = m) ∧
      (IsNondegenerate A M ↔
        ∀ (T : Type uT) [AddCommGroup T] (g : ∀ e ∈ J, e.leftImage M →+ T),
          (∀ e (he : e ∈ J) f (hf : f ∈ J), e ≤ f →
            ∀ (m : M) (hme : m ∈ e.leftImage M) (hmf : m ∈ f.leftImage M),
              g e he ⟨m, hme⟩ = g f hf ⟨m, hmf⟩) →
          ∃! h : M →+ T, ∀ e (he : e ∈ J) (m : e.leftImage M), h m = g e he m)

/-- Renard I.1.4: the completion of a nondegenerate module, with its original action
`(a · φ)(b) = φ(ba)`, need not be nondegenerate. There are a ring with idempotents `A` and a
nondegenerate `A`-module `M` whose completion `NonUnitalModuleLeftLimit A M` is not
nondegenerate. -/
def LeftLimitNotNondegenerateStatement : Prop :=
  ∃ (A : Type) (_ : NonUnitalRing A) (hA : IsIdempotented A)
    (M : Type) (_ : AddCommGroup M) (_ : NonUnitalModule A M),
    IsNondegenerate A M ∧
      ¬ @IsNondegenerate A (NonUnitalModuleLeftLimit A M) _ _
          (NonUnitalModuleLeftLimit.nonUnitalModule hA)

end Langlands.Algebra
