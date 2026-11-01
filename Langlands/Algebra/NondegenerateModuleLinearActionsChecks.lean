import Langlands.Algebra.NondegenerateModuleLinearActions
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Ring.PUnit

/-! Complete declaration and structure-selection checks for the actual actions. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NondegenerateModuleLinearActions

universe uK uA uI uM

example : (k : Type uK) → {A : Type uA} → {M : Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    Ring (Module.End k M) :=
  @endRing.{uK, uA, uM}

example : (k : Type uK) → {A : Type uA} → {M : Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    letI := endRing k hA hM
    Module k (Module.End k M) :=
  @endModule.{uK, uA, uM}

example : (k : Type uK) → {A : Type uA} → {M : Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) → (c : k) → (m : M) →
    letI := NondegenerateScalars.module k hA hM
    IdempotentedRingRightLimitAction.act hM x (c • m) =
      c • IdempotentedRingRightLimitAction.act hM x m :=
  @act_smul.{uK, uA, uM}

example : (k : Type uK) → {A : Type uA} → {M : Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    IdempotentedRingRightLimit A → Module.End k M :=
  @linearEnd.{uK, uA, uM}

example : (k : Type uK) → {A : Type uA} → {M : Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    letI := IdempotentedRingRightLimit.ring hA
    letI := endRing k hA hM
    IdempotentedRingRightLimit A →+* Module.End k M :=
  @completedHom.{uK, uA, uM}

example : (k : Type uK) → {A : Type uA} → {M : Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := endRing k hA hM
    (completedHom k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (NondegenerateScalars.toLinearEndHom k hA hM : A →ₙ+* End k hA hM) :=
  @completedHom_comp_canonical.{uK, uA, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    Ring (∀ i, Module.End k (M i)) :=
  @productRing.{uK, uA, uI, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    Module k (∀ i, Module.End k (M i)) :=
  @productModule.{uK, uA, uI, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := productModule k hA hM
    A →ₙₐ[k] (∀ i, Module.End k (M i)) :=
  @original.{uK, uA, uI, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    IdempotentedRingRightLimit A →+* (∀ i, Module.End k (M i)) :=
  @completed.{uK, uA, uI, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    (∀ i, Module.End k (M i)) →+* Module.End k (M i) :=
  @projection.{uK, uA, uI, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    letI := endModule k hA (hM i)
    (∀ i, Module.End k (M i)) →ₙₐ[k] Module.End k (M i) :=
  @algebraProjection.{uK, uA, uI, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := productModule k hA hM
    (completed k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (original k hA hM : A →ₙ+* EndProduct k hA hM) :=
  @completed_comp_canonical.{uK, uA, uI, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    letI := endModule k hA (hM i)
    (algebraProjection k hA hM i).comp (original k hA hM) =
      NondegenerateScalars.toLinearEndHom k hA (hM i) :=
  @projection_original.{uK, uA, uI, uM}

example : (k : Type uK) → {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    (projection k hA hM i).comp (completed k hA hM) = completedHom k hA (hM i) :=
  @projection_completed.{uK, uA, uI, uM}

/-! Explicit pairwise unequal universe assignments, in both directions. -/

example : (k : Type 0) → {A : Type 1} → {I : Type 2} → {M : I → Type 3} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := productModule k hA hM
    A →ₙₐ[k] (∀ i, Module.End k (M i)) :=
  @original.{0, 1, 2, 3}

example : (k : Type 0) → {A : Type 1} → {I : Type 2} → {M : I → Type 3} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    IdempotentedRingRightLimit A →+* (∀ i, Module.End k (M i)) :=
  @completed.{0, 1, 2, 3}

example : (k : Type 0) → {A : Type 1} → {I : Type 2} → {M : I → Type 3} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    (∀ i, Module.End k (M i)) →+* Module.End k (M i) :=
  @projection.{0, 1, 2, 3}

example : (k : Type 0) → {A : Type 1} → {I : Type 2} → {M : I → Type 3} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    letI := endModule k hA (hM i)
    (∀ i, Module.End k (M i)) →ₙₐ[k] Module.End k (M i) :=
  @algebraProjection.{0, 1, 2, 3}

example : (k : Type 0) → {A : Type 1} → {I : Type 2} → {M : I → Type 3} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := productModule k hA hM
    (completed k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (original k hA hM : A →ₙ+* EndProduct k hA hM) :=
  @completed_comp_canonical.{0, 1, 2, 3}

example : (k : Type 0) → {A : Type 1} → {M : Type 3} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    letI := IdempotentedRingRightLimit.ring hA
    letI := endRing k hA hM
    IdempotentedRingRightLimit A →+* Module.End k M :=
  @completedHom.{0, 1, 3}

example : (k : Type 0) → {A : Type 1} → {M : Type 3} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    IdempotentedRingRightLimit A → Module.End k M :=
  @linearEnd.{0, 1, 3}

example : (k : Type 3) → {A : Type 2} → {I : Type 1} → {M : I → Type 0} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := productModule k hA hM
    A →ₙₐ[k] (∀ i, Module.End k (M i)) :=
  @original.{3, 2, 1, 0}

example : (k : Type 3) → {A : Type 2} → {I : Type 1} → {M : I → Type 0} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    IdempotentedRingRightLimit A →+* (∀ i, Module.End k (M i)) :=
  @completed.{3, 2, 1, 0}

example : (k : Type 3) → {A : Type 2} → {I : Type 1} → {M : I → Type 0} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    (∀ i, Module.End k (M i)) →+* Module.End k (M i) :=
  @projection.{3, 2, 1, 0}

example : (k : Type 3) → {A : Type 2} → {I : Type 1} → {M : I → Type 0} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    letI := endModule k hA (hM i)
    (∀ i, Module.End k (M i)) →ₙₐ[k] Module.End k (M i) :=
  @algebraProjection.{3, 2, 1, 0}

example : (k : Type 3) → {A : Type 2} → {I : Type 1} → {M : I → Type 0} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := productModule k hA hM
    (completed k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (original k hA hM : A →ₙ+* EndProduct k hA hM) :=
  @completed_comp_canonical.{3, 2, 1, 0}

example : (k : Type 3) → {A : Type 2} → {M : Type 0} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    letI := IdempotentedRingRightLimit.ring hA
    letI := endRing k hA hM
    IdempotentedRingRightLimit A →+* Module.End k M :=
  @completedHom.{3, 2, 0}

example : (k : Type 3) → {A : Type 2} → {M : Type 0} →
    [CommSemiring k] → [NonUnitalRing A] → [Module k A] →
    [IsScalarTower k A A] → [SMulCommClass k A A] →
    [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    IdempotentedRingRightLimit A → Module.End k M :=
  @linearEnd.{3, 2, 0}

section CompetingOriginalStructures

variable (k : Type uK) {A : Type uA} {I : Type uI} {M : I → Type uM}
  [ck : CommSemiring k]
  (rA : NonUnitalRing A) [otherRing : NonUnitalRing A]
  (sA : letI := rA; Module k A)
  (tA : letI := rA; letI := sA; IsScalarTower k A A)
  (cA : letI := rA; letI := sA; SMulCommClass k A A)
  (gM : ∀ i, AddCommGroup (M i)) [∀ i, AddCommGroup (M i)]
  (aM : letI := rA; letI := gM; ∀ i, NonUnitalModule A (M i))
  [∀ i, NonUnitalModule A (M i)]

/-! Whole constructors select the named original structures while competing
instances remain in the surrounding context. The nondegeneracy proofs are unapplied. -/

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := productModule k hA hM
    A →ₙₐ[k] (∀ i, Module.End k (M i)) :=
  @original k A I M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    IdempotentedRingRightLimit A →+* (∀ i, Module.End k (M i)) :=
  @completed k A I M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    (∀ i, Module.End k (M i)) →+* Module.End k (M i) :=
  @projection k A I M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    letI := endModule k hA (hM i)
    (∀ i, Module.End k (M i)) →ₙₐ[k] Module.End k (M i) :=
  @algebraProjection k A I M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    Ring (∀ i, Module.End k (M i)) :=
  @productRing k A I M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.module k hA (hM i)
    letI := productRing k hA hM
    Module k (∀ i, Module.End k (M i)) :=
  @productModule k A I M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := productModule k hA hM
    (completed k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (original k hA hM : A →ₙ+* EndProduct k hA hM) :=
  @completed_comp_canonical k A I M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    letI := endModule k hA (hM i)
    (algebraProjection k hA hM i).comp (original k hA hM) =
      NondegenerateScalars.toLinearEndHom k hA (hM i) :=
  @projection_original k A I M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    (i : I) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    (projection k hA hM i).comp (completed k hA hM) = completedHom k hA (hM i) :=
  @projection_completed k A I M ck rA sA tA cA gM aM

end CompetingOriginalStructures

section CompetingOriginalIndividual

variable (k : Type uK) {A : Type uA} {M : Type uM}
  [ck : CommSemiring k]
  (rA : NonUnitalRing A) [otherRing : NonUnitalRing A]
  (sA : letI := rA; Module k A)
  (tA : letI := rA; letI := sA; IsScalarTower k A A)
  (cA : letI := rA; letI := sA; SMulCommClass k A A)
  (gM : AddCommGroup M) [AddCommGroup M]
  (aM : letI := rA; letI := gM; NonUnitalModule A M)
  [NonUnitalModule A M]

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    Ring (Module.End k M) :=
  @endRing k A M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    letI := endRing k hA hM
    Module k (Module.End k M) :=
  @endModule k A M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) → (c : k) → (m : M) →
    letI := NondegenerateScalars.module k hA hM
    IdempotentedRingRightLimitAction.act hM x (c • m) =
      c • IdempotentedRingRightLimitAction.act hM x m :=
  @act_smul k A M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    IdempotentedRingRightLimit A → Module.End k M :=
  @linearEnd k A M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := NondegenerateScalars.module k hA hM
    letI := IdempotentedRingRightLimit.ring hA
    letI := endRing k hA hM
    IdempotentedRingRightLimit A →+* Module.End k M :=
  @completedHom k A M ck rA sA tA cA gM aM

example :
    letI := rA
    letI := sA
    letI := tA
    letI := cA
    letI := gM
    letI := aM
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := endRing k hA hM
    (completedHom k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (NondegenerateScalars.toLinearEndHom k hA hM : A →ₙ+* End k hA hM) :=
  @completedHom_comp_canonical k A M ck rA sA tA cA gM aM

end CompetingOriginalIndividual

section CompetingConstructedStructures

variable (k : Type uK) {A : Type uA} {I : Type uI} {M : I → Type uM}
  [CommSemiring k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [∀ i, AddCommGroup (M i)] [∀ i, NonUnitalModule A (M i)]
  (hA : IsIdempotented A) (hM : ∀ i, IsNondegenerate A (M i))
  [otherScalars : ∀ i, Module k (M i)]
  [otherEndRings : ∀ i, Ring (End k hA (hM i))]
  [otherEndModules : ∀ i, Module k (End k hA (hM i))]
  [otherProductRing : Ring (EndProduct k hA hM)]
  [otherProductModule : Module k (EndProduct k hA hM)]
  [otherCompletion : Ring (IdempotentedRingRightLimit A)]

/-! Expected whole types explicitly pin every constructed structure, despite
competing canonical scalars, coordinate rings/modules and source/target rings. -/
example (i : I) :
    IdempotentedRingRightLimit A →
      (letI := NondegenerateScalars.module k hA (hM i); Module.End k (M i)) :=
  linearEnd k hA (hM i)

example (i : I) :
    endRing k hA (hM i) =
      @Module.End.instRing k (M i) _ _ (NondegenerateScalars.module k hA (hM i)) := rfl

example (i : I) :
    @Module k (End k hA (hM i)) _ (endRing k hA (hM i)).toAddCommMonoid :=
  endModule k hA (hM i)

example (i : I) :
    @RingHom (IdempotentedRingRightLimit A) (End k hA (hM i))
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
      (endRing k hA (hM i)).toNonAssocSemiring :=
  completedHom k hA (hM i)

example :
    productRing k hA hM =
      @Pi.ring I (fun i => End k hA (hM i)) (fun i => endRing k hA (hM i)) := rfl

example :
    @Module k (EndProduct k hA hM) _ (productRing k hA hM).toAddCommMonoid :=
  productModule k hA hM

example :
    @NonUnitalAlgHom k k _ _ (MonoidHom.id k) A (EndProduct k hA hM) _ _
      (productRing k hA hM).toNonUnitalNonAssocSemiring
      (productModule k hA hM).toDistribMulAction :=
  original k hA hM

example :
    @RingHom (IdempotentedRingRightLimit A) (EndProduct k hA hM)
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
      (productRing k hA hM).toNonAssocSemiring :=
  completed k hA hM

example (i : I) :
    @RingHom (EndProduct k hA hM) (End k hA (hM i))
      (productRing k hA hM).toNonAssocSemiring
      (endRing k hA (hM i)).toNonAssocSemiring :=
  projection k hA hM i

example (i : I) :
    @NonUnitalAlgHom k k _ _ (MonoidHom.id k) (EndProduct k hA hM) (End k hA (hM i))
      (productRing k hA hM).toNonUnitalNonAssocSemiring
      (productModule k hA hM).toDistribMulAction
      (endRing k hA (hM i)).toNonUnitalNonAssocSemiring
      (endModule k hA (hM i)).toDistribMulAction :=
  algebraProjection k hA hM i

example :
    letI (i : I) := endRing k hA (hM i)
    letI (i : I) := endModule k hA (hM i)
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := productModule k hA hM
    (completed k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (original k hA hM : A →ₙ+* EndProduct k hA hM) :=
  completed_comp_canonical k hA hM

example (i : I) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    (projection k hA hM i).comp (completed k hA hM) = completedHom k hA (hM i) :=
  projection_completed k hA hM i

end CompetingConstructedStructures

section Complex

example : {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.complexModule hA (hM i)
    letI := productRing ℂ hA hM
    letI := productModule ℂ hA hM
    A →ₙₐ[ℂ] (∀ i, Module.End ℂ (M i)) :=
  @complexOriginal.{uA, uI, uM}

example : {A : Type uA} → {I : Type uI} → {M : I → Type uM} →
    [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    [∀ i, AddCommGroup (M i)] → [∀ i, NonUnitalModule A (M i)] →
    (hA : IsIdempotented A) → (hM : ∀ i, IsNondegenerate A (M i)) →
    letI := fun i => NondegenerateScalars.complexModule hA (hM i)
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing ℂ hA hM
    IdempotentedRingRightLimit A →+* (∀ i, Module.End ℂ (M i)) :=
  @complexCompleted.{uA, uI, uM}

end Complex

section DegenerateCases

variable (k : Type uK) {A : Type uA} {M : Type uM}
  [CommSemiring k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [NonUnitalModule A M]

example [Subsingleton A] (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    (fun x => (linearEnd k hA hM x).toAddMonoidHom) = fun _ => 0 := by
  funext x
  apply AddMonoidHom.ext
  intro m
  rw [show (linearEnd k hA hM x).toAddMonoidHom m = x.val _ • m from
    linearEnd_apply_eq k hA hM x m (hM m).choose (hM m).choose_spec]
  rw [show x.val (hM m).choose = 0 from Subsingleton.elim _ _]
  exact @NonUnitalModule.zero_smul A M _ _ _ m

example [Subsingleton M] (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := NondegenerateScalars.module k hA hM
    linearEnd k hA hM = fun _ => (0 : Module.End k M) := by
  let := NondegenerateScalars.module k hA hM
  funext x
  apply LinearMap.ext
  intro m
  exact Subsingleton.elim _ _

variable {I : Type uI} {N : I → Type uM}
  [∀ i, AddCommGroup (N i)] [∀ i, NonUnitalModule A (N i)]

example [∀ i, Subsingleton (N i)] (hA : IsIdempotented A)
    (hN : ∀ i, IsNondegenerate A (N i)) :
    letI := productRing k hA hN
    ⇑(completed k hA hN) = fun _ => 0 := by
  funext x i
  let := NondegenerateScalars.module k hA (hN i)
  apply LinearMap.ext
  intro m
  exact Subsingleton.elim _ _

example [IsEmpty I] (hA : IsIdempotented A) (hN : ∀ i, IsNondegenerate A (N i)) :
    Subsingleton (EndProduct k hA hN) := inferInstance

example [IsEmpty I] (hA : IsIdempotented A) (hN : ∀ i, IsNondegenerate A (N i)) :
    letI := productRing k hA hN
    letI := productModule k hA hN
    ∀ f : A →ₙₐ[k] EndProduct k hA hN, original k hA hN = f := by
  let := productRing k hA hN
  let := productModule k hA hN
  intro f
  apply NonUnitalAlgHom.ext
  intro a
  funext i
  exact isEmptyElim i

example [IsEmpty I] (hA : IsIdempotented A) (hN : ∀ i, IsNondegenerate A (N i)) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hN
    ∀ f : IdempotentedRingRightLimit A →+* EndProduct k hA hN, completed k hA hN = f := by
  intro f
  apply RingHom.ext
  intro x
  funext i
  exact isEmptyElim i

end DegenerateCases

section ExplicitZeroObjects

variable (k : Type uK) [CommSemiring k]

/-! The zero ring and zero carriers give actual whole bundled maps. -/
example :
    letI : NonUnitalModule PUnit.{1} PUnit.{1} := NonUnitalModule.ofEndHom 0
    ∃ (hA : IsIdempotented PUnit.{1})
      (hM : ∀ _ : Unit, IsNondegenerate PUnit.{1} PUnit.{1}),
      letI := productRing k hA hM
      letI := productModule k hA hM
      Nonempty (PUnit.{1} →ₙₐ[k] EndProduct k hA hM) ∧
      (letI := IdempotentedRingRightLimit.ring hA
       Nonempty (IdempotentedRingRightLimit PUnit.{1} →+* EndProduct k hA hM)) := by
  let : NonUnitalModule PUnit.{1} PUnit.{1} := NonUnitalModule.ofEndHom 0
  let hA : IsIdempotented PUnit.{1} := IsIdempotented.of_ring PUnit.{1}
  let hM : ∀ _ : Unit, IsNondegenerate PUnit.{1} PUnit.{1} :=
    fun _ _ => ⟨⟨0, IsIdempotentElem.zero⟩, rfl⟩
  exact ⟨hA, hM, ⟨original k hA hM⟩, ⟨completed k hA hM⟩⟩

end ExplicitZeroObjects

end Langlands.Algebra.NondegenerateModuleLinearActions
