import Langlands.Algebra.NonUnitalTensorSmoothingStatements
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Basic.Complex.Basic

/-!
# Interface and scope checks for prescribed additive tensor smoothing

Complete unapplied signatures and exact unfoldings at five independent
universes, with both orders of unequal concrete universes. Conditional
specializations check the original zero actions, zero carriers, zero ring
and the source's complex-algebra setting. These do not prove TensorSmoothing.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalTensorSmoothingStatementsChecks

open NonUnitalModuleTensor NonUnitalTensorSmoothing
open NonUnitalTensorSmoothingStatements

universe uA uN uM uN' uM'

section Interfaces

set_option linter.unusedVariables false

/-! Complete unapplied signatures: Arbitrary universes. -/

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @InverseIdentities.{uA, uN, uM}

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @Bijectivity.{uA, uN, uM}

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M)
    (E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M), Prop := @EquivalenceData.{uA, uN, uM}

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @PrescribedEquivalence.{uA, uN, uM}

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type uN'} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type uM'} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'), Prop := @Naturality.{uA, uN, uM, uN', uM'}

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type uN'} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type uM'} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'), Prop := @EquivalenceNaturality.{uA, uN, uM, uN', uM'}

example : Prop := @TensorSmoothing.{uA, uN, uM, uN', uM'}

/-! Exact unapplied unfoldings: Arbitrary universes. -/

example : (@InverseIdentities.{uA, uN, uM}) =
    (fun {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      (reverse hA N hM).comp (inclusion hA N M) =
        AddMonoidHom.id (Tensor A (nondegeneratePart hA.op N) M) ∧
      (inclusion hA N M).comp (reverse hA N hM) =
        AddMonoidHom.id (Tensor A N M)) := rfl

example : (@Bijectivity.{uA, uN, uM}) =
    (fun {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      Function.Bijective (inclusion hA N M) ∧
      Function.Bijective (reverse hA N hM)) := rfl

example : (@EquivalenceData.{uA, uN, uM}) =
    (fun {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M)
    (E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M) =>
      E.toAddMonoidHom = inclusion hA N M ∧
      E.symm.toAddMonoidHom = reverse hA N hM ∧
      (∀ (n : nondegeneratePart hA.op N) (m : M),
        E (tmul A (nondegeneratePart hA.op N) M n m) =
          tmul A N M (n : N) m) ∧
      (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        E.symm (tmul A N M n m) =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) := rfl

example : (@PrescribedEquivalence.{uA, uN, uM}) =
    (fun {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      ∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
        EquivalenceData hA N hM E) := rfl

example : (@Naturality.{uA, uN, uM, uN', uM'}) =
    (fun {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type uN'} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type uM'} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M') =>
      (map A f g).comp (inclusion hA N M) =
        (inclusion hA N' M').comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
      (map A (f.restrictNondegeneratePart hA.op) g).comp (reverse hA N hM) =
        (reverse hA N' hM').comp (map A f g)) := rfl

example : (@EquivalenceNaturality.{uA, uN, uM, uN', uM'}) =
    (fun {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type uN'} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type uM'} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M') =>
      ∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
        ∃ E' : Tensor A (nondegeneratePart hA.op N') M' ≃+ Tensor A N' M',
          (EquivalenceData hA N hM E) ∧
          (EquivalenceData hA N' hM' E') ∧
          (map A f g).comp E.toAddMonoidHom =
            E'.toAddMonoidHom.comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
          (map A (f.restrictNondegeneratePart hA.op) g).comp E.symm.toAddMonoidHom =
            E'.symm.toAddMonoidHom.comp (map A f g)) := rfl

example : @TensorSmoothing.{uA, uN, uM, uN', uM'} =
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M),
  ((reverse hA N hM).comp (inclusion hA N M) =
    AddMonoidHom.id (Tensor A (nondegeneratePart hA.op N) M) ∧
  (inclusion hA N M).comp (reverse hA N hM) =
    AddMonoidHom.id (Tensor A N M)) ∧
  (Function.Bijective (inclusion hA N M) ∧
  Function.Bijective (reverse hA N hM)) ∧
  (∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
    E.toAddMonoidHom = inclusion hA N M ∧
    E.symm.toAddMonoidHom = reverse hA N hM ∧
    (∀ (n : nondegeneratePart hA.op N) (m : M),
      E (tmul A (nondegeneratePart hA.op N) M n m) =
        tmul A N M (n : N) m) ∧
    (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
      E.symm (tmul A N M n m) =
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) ∧
  ∀ (N' : Type uN') [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    (M' : Type uM') [AddCommGroup M'] [NonUnitalModule A M']
    (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'),
    ((map A f g).comp (inclusion hA N M) =
      (inclusion hA N' M').comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
    (map A (f.restrictNondegeneratePart hA.op) g).comp (reverse hA N hM) =
      (reverse hA N' hM').comp (map A f g)) ∧
    (∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
      ∃ E' : Tensor A (nondegeneratePart hA.op N') M' ≃+ Tensor A N' M',
        (E.toAddMonoidHom = inclusion hA N M ∧
        E.symm.toAddMonoidHom = reverse hA N hM ∧
        (∀ (n : nondegeneratePart hA.op N) (m : M),
          E (tmul A (nondegeneratePart hA.op N) M n m) =
            tmul A N M (n : N) m) ∧
        (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
          E.symm (tmul A N M n m) =
            tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) ∧
        (E'.toAddMonoidHom = inclusion hA N' M' ∧
        E'.symm.toAddMonoidHom = reverse hA N' hM' ∧
        (∀ (n : nondegeneratePart hA.op N') (m : M'),
          E' (tmul A (nondegeneratePart hA.op N') M' n m) =
            tmul A N' M' (n : N') m) ∧
        (∀ (n : N') (m : M') (e : Idempotent A), (e : A) • m = m →
          E'.symm (tmul A N' M' n m) =
            tmul A (nondegeneratePart hA.op N') M' (smoothing hA n e) m)) ∧
        (map A f g).comp E.toAddMonoidHom =
          E'.toAddMonoidHom.comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
        (map A (f.restrictNondegeneratePart hA.op) g).comp E.symm.toAddMonoidHom =
          E'.symm.toAddMonoidHom.comp (map A f g))) := rfl

/-! Complete unapplied signatures: Ascending universes. -/

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @InverseIdentities.{0, 1, 2}

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @Bijectivity.{0, 1, 2}

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M)
    (E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M), Prop := @EquivalenceData.{0, 1, 2}

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @PrescribedEquivalence.{0, 1, 2}

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type 1} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type 3} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type 4} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'), Prop := @Naturality.{0, 1, 2, 3, 4}

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type 1} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type 3} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type 4} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'), Prop := @EquivalenceNaturality.{0, 1, 2, 3, 4}

example : Prop := @TensorSmoothing.{0, 1, 2, 3, 4}

/-! Exact unapplied unfoldings: Ascending universes. -/

example : (@InverseIdentities.{0, 1, 2}) =
    (fun {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      (reverse hA N hM).comp (inclusion hA N M) =
        AddMonoidHom.id (Tensor A (nondegeneratePart hA.op N) M) ∧
      (inclusion hA N M).comp (reverse hA N hM) =
        AddMonoidHom.id (Tensor A N M)) := rfl

example : (@Bijectivity.{0, 1, 2}) =
    (fun {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      Function.Bijective (inclusion hA N M) ∧
      Function.Bijective (reverse hA N hM)) := rfl

example : (@EquivalenceData.{0, 1, 2}) =
    (fun {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M)
    (E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M) =>
      E.toAddMonoidHom = inclusion hA N M ∧
      E.symm.toAddMonoidHom = reverse hA N hM ∧
      (∀ (n : nondegeneratePart hA.op N) (m : M),
        E (tmul A (nondegeneratePart hA.op N) M n m) =
          tmul A N M (n : N) m) ∧
      (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        E.symm (tmul A N M n m) =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) := rfl

example : (@PrescribedEquivalence.{0, 1, 2}) =
    (fun {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      ∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
        EquivalenceData hA N hM E) := rfl

example : (@Naturality.{0, 1, 2, 3, 4}) =
    (fun {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type 1} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type 3} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type 4} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M') =>
      (map A f g).comp (inclusion hA N M) =
        (inclusion hA N' M').comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
      (map A (f.restrictNondegeneratePart hA.op) g).comp (reverse hA N hM) =
        (reverse hA N' hM').comp (map A f g)) := rfl

example : (@EquivalenceNaturality.{0, 1, 2, 3, 4}) =
    (fun {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type 1} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type 3} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type 4} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M') =>
      ∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
        ∃ E' : Tensor A (nondegeneratePart hA.op N') M' ≃+ Tensor A N' M',
          (EquivalenceData hA N hM E) ∧
          (EquivalenceData hA N' hM' E') ∧
          (map A f g).comp E.toAddMonoidHom =
            E'.toAddMonoidHom.comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
          (map A (f.restrictNondegeneratePart hA.op) g).comp E.symm.toAddMonoidHom =
            E'.symm.toAddMonoidHom.comp (map A f g)) := rfl

example : @TensorSmoothing.{0, 1, 2, 3, 4} =
    (∀ (A : Type 0) [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (M : Type 2) [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M),
  ((reverse hA N hM).comp (inclusion hA N M) =
    AddMonoidHom.id (Tensor A (nondegeneratePart hA.op N) M) ∧
  (inclusion hA N M).comp (reverse hA N hM) =
    AddMonoidHom.id (Tensor A N M)) ∧
  (Function.Bijective (inclusion hA N M) ∧
  Function.Bijective (reverse hA N hM)) ∧
  (∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
    E.toAddMonoidHom = inclusion hA N M ∧
    E.symm.toAddMonoidHom = reverse hA N hM ∧
    (∀ (n : nondegeneratePart hA.op N) (m : M),
      E (tmul A (nondegeneratePart hA.op N) M n m) =
        tmul A N M (n : N) m) ∧
    (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
      E.symm (tmul A N M n m) =
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) ∧
  ∀ (N' : Type 3) [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    (M' : Type 4) [AddCommGroup M'] [NonUnitalModule A M']
    (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'),
    ((map A f g).comp (inclusion hA N M) =
      (inclusion hA N' M').comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
    (map A (f.restrictNondegeneratePart hA.op) g).comp (reverse hA N hM) =
      (reverse hA N' hM').comp (map A f g)) ∧
    (∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
      ∃ E' : Tensor A (nondegeneratePart hA.op N') M' ≃+ Tensor A N' M',
        (E.toAddMonoidHom = inclusion hA N M ∧
        E.symm.toAddMonoidHom = reverse hA N hM ∧
        (∀ (n : nondegeneratePart hA.op N) (m : M),
          E (tmul A (nondegeneratePart hA.op N) M n m) =
            tmul A N M (n : N) m) ∧
        (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
          E.symm (tmul A N M n m) =
            tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) ∧
        (E'.toAddMonoidHom = inclusion hA N' M' ∧
        E'.symm.toAddMonoidHom = reverse hA N' hM' ∧
        (∀ (n : nondegeneratePart hA.op N') (m : M'),
          E' (tmul A (nondegeneratePart hA.op N') M' n m) =
            tmul A N' M' (n : N') m) ∧
        (∀ (n : N') (m : M') (e : Idempotent A), (e : A) • m = m →
          E'.symm (tmul A N' M' n m) =
            tmul A (nondegeneratePart hA.op N') M' (smoothing hA n e) m)) ∧
        (map A f g).comp E.toAddMonoidHom =
          E'.toAddMonoidHom.comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
        (map A (f.restrictNondegeneratePart hA.op) g).comp E.symm.toAddMonoidHom =
          E'.symm.toAddMonoidHom.comp (map A f g))) := rfl

/-! Complete unapplied signatures: Descending universes. -/

example : ∀ {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @InverseIdentities.{4, 3, 2}

example : ∀ {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @Bijectivity.{4, 3, 2}

example : ∀ {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M)
    (E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M), Prop := @EquivalenceData.{4, 3, 2}

example : ∀ {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M), Prop := @PrescribedEquivalence.{4, 3, 2}

example : ∀ {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type 3} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type 1} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type 0} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'), Prop := @Naturality.{4, 3, 2, 1, 0}

example : ∀ {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type 3} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type 1} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type 0} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'), Prop := @EquivalenceNaturality.{4, 3, 2, 1, 0}

example : Prop := @TensorSmoothing.{4, 3, 2, 1, 0}

/-! Exact unapplied unfoldings: Descending universes. -/

example : (@InverseIdentities.{4, 3, 2}) =
    (fun {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      (reverse hA N hM).comp (inclusion hA N M) =
        AddMonoidHom.id (Tensor A (nondegeneratePart hA.op N) M) ∧
      (inclusion hA N M).comp (reverse hA N hM) =
        AddMonoidHom.id (Tensor A N M)) := rfl

example : (@Bijectivity.{4, 3, 2}) =
    (fun {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      Function.Bijective (inclusion hA N M) ∧
      Function.Bijective (reverse hA N hM)) := rfl

example : (@EquivalenceData.{4, 3, 2}) =
    (fun {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M)
    (E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M) =>
      E.toAddMonoidHom = inclusion hA N M ∧
      E.symm.toAddMonoidHom = reverse hA N hM ∧
      (∀ (n : nondegeneratePart hA.op N) (m : M),
        E (tmul A (nondegeneratePart hA.op N) M n m) =
          tmul A N M (n : N) m) ∧
      (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        E.symm (tmul A N M n m) =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) := rfl

example : (@PrescribedEquivalence.{4, 3, 2}) =
    (fun {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) =>
      ∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
        EquivalenceData hA N hM E) := rfl

example : (@Naturality.{4, 3, 2, 1, 0}) =
    (fun {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type 3} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type 1} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type 0} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M') =>
      (map A f g).comp (inclusion hA N M) =
        (inclusion hA N' M').comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
      (map A (f.restrictNondegeneratePart hA.op) g).comp (reverse hA N hM) =
        (reverse hA N' hM').comp (map A f g)) := rfl

example : (@EquivalenceNaturality.{4, 3, 2, 1, 0}) =
    (fun {A : Type 4} [NonUnitalRing A] (hA : IsIdempotented A)
    {N : Type 3} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type 2} [AddCommGroup M] [NonUnitalModule A M]
    {N' : Type 1} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    {M' : Type 0} [AddCommGroup M'] [NonUnitalModule A M']
    (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M') =>
      ∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
        ∃ E' : Tensor A (nondegeneratePart hA.op N') M' ≃+ Tensor A N' M',
          (EquivalenceData hA N hM E) ∧
          (EquivalenceData hA N' hM' E') ∧
          (map A f g).comp E.toAddMonoidHom =
            E'.toAddMonoidHom.comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
          (map A (f.restrictNondegeneratePart hA.op) g).comp E.symm.toAddMonoidHom =
            E'.symm.toAddMonoidHom.comp (map A f g)) := rfl

example : @TensorSmoothing.{4, 3, 2, 1, 0} =
    (∀ (A : Type 4) [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 3) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (M : Type 2) [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M),
  ((reverse hA N hM).comp (inclusion hA N M) =
    AddMonoidHom.id (Tensor A (nondegeneratePart hA.op N) M) ∧
  (inclusion hA N M).comp (reverse hA N hM) =
    AddMonoidHom.id (Tensor A N M)) ∧
  (Function.Bijective (inclusion hA N M) ∧
  Function.Bijective (reverse hA N hM)) ∧
  (∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
    E.toAddMonoidHom = inclusion hA N M ∧
    E.symm.toAddMonoidHom = reverse hA N hM ∧
    (∀ (n : nondegeneratePart hA.op N) (m : M),
      E (tmul A (nondegeneratePart hA.op N) M n m) =
        tmul A N M (n : N) m) ∧
    (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
      E.symm (tmul A N M n m) =
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) ∧
  ∀ (N' : Type 1) [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
    (M' : Type 0) [AddCommGroup M'] [NonUnitalModule A M']
    (hM' : IsNondegenerate A M')
    (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'),
    ((map A f g).comp (inclusion hA N M) =
      (inclusion hA N' M').comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
    (map A (f.restrictNondegeneratePart hA.op) g).comp (reverse hA N hM) =
      (reverse hA N' hM').comp (map A f g)) ∧
    (∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
      ∃ E' : Tensor A (nondegeneratePart hA.op N') M' ≃+ Tensor A N' M',
        (E.toAddMonoidHom = inclusion hA N M ∧
        E.symm.toAddMonoidHom = reverse hA N hM ∧
        (∀ (n : nondegeneratePart hA.op N) (m : M),
          E (tmul A (nondegeneratePart hA.op N) M n m) =
            tmul A N M (n : N) m) ∧
        (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
          E.symm (tmul A N M n m) =
            tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)) ∧
        (E'.toAddMonoidHom = inclusion hA N' M' ∧
        E'.symm.toAddMonoidHom = reverse hA N' hM' ∧
        (∀ (n : nondegeneratePart hA.op N') (m : M'),
          E' (tmul A (nondegeneratePart hA.op N') M' n m) =
            tmul A N' M' (n : N') m) ∧
        (∀ (n : N') (m : M') (e : Idempotent A), (e : A) • m = m →
          E'.symm (tmul A N' M' n m) =
            tmul A (nondegeneratePart hA.op N') M' (smoothing hA n e) m)) ∧
        (map A f g).comp E.toAddMonoidHom =
          E'.toAddMonoidHom.comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
        (map A (f.restrictNondegeneratePart hA.op) g).comp E.symm.toAddMonoidHom =
          E'.symm.toAddMonoidHom.comp (map A f g))) := rfl

end Interfaces

/-! Conditional specialization checks: no proof of TensorSmoothing is assumed globally. -/

private theorem subsingletonNondegenerate
    {A : Type uA} [NonUnitalRing A] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] [Subsingleton M] : IsNondegenerate A M :=
  fun _m => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

section ZeroRightAction

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
  (N : Type uN) [AddCommGroup N]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hM : IsNondegenerate A M)

local instance : NonUnitalModule Aᵐᵒᵖ N := NonUnitalModule.zero

/-- The entire family specializes to any additive group with its zero right action. -/
example (h : TensorSmoothing.{uA, uN, uM, uN', uM'}) :
    InverseIdentities hA N hM ∧ Bijectivity hA N hM ∧ PrescribedEquivalence hA N hM ∧
      ∀ (N' : Type uN') [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
        (M' : Type uM') [AddCommGroup M'] [NonUnitalModule A M']
        (hM' : IsNondegenerate A M')
        (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'),
        Naturality hA hM hM' f g ∧ EquivalenceNaturality hA hM hM' f g :=
  h A hA N M hM

end ZeroRightAction

section NonzeroZeroRightAction

local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.zero
local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.ofModule ℤ ℤ

private theorem integerLeftNondegenerate : IsNondegenerate ℤ ℤ :=
  fun m => ⟨⟨1, IsIdempotentElem.one⟩, one_smul ℤ m⟩

/-- The concrete right carrier is nonzero and fails nondegeneracy. -/
example : ¬ IsNondegenerate ℤᵐᵒᵖ ℤ := by
  intro h
  obtain ⟨e, he⟩ := h 1
  change (0 : ℤ) = 1 at he
  exact zero_ne_one he

/-- Its original action also fails the unit law over the unital ring. -/
example : ¬ IsUnitalModule ℤᵐᵒᵖ ℤ := by
  intro h
  have bad := h 1
  change (0 : ℤ) = 1 at bad
  exact zero_ne_one bad

example (h : TensorSmoothing.{0, 0, 0, uN', uM'}) :
    InverseIdentities (IsIdempotented.of_ring ℤ) ℤ integerLeftNondegenerate ∧
      Bijectivity (IsIdempotented.of_ring ℤ) ℤ integerLeftNondegenerate ∧
      PrescribedEquivalence (IsIdempotented.of_ring ℤ) ℤ integerLeftNondegenerate :=
  ⟨(h ℤ (IsIdempotented.of_ring ℤ) ℤ ℤ integerLeftNondegenerate).1,
    (h ℤ (IsIdempotented.of_ring ℤ) ℤ ℤ integerLeftNondegenerate).2.1,
    (h ℤ (IsIdempotented.of_ring ℤ) ℤ ℤ integerLeftNondegenerate).2.2.1⟩

example (h : TensorSmoothing.{0, 0, 0, 0, 0}) :
    Naturality (IsIdempotented.of_ring ℤ) integerLeftNondegenerate
        integerLeftNondegenerate (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ)
        (NonUnitalModuleHom.id ℤ ℤ) ∧
      EquivalenceNaturality (IsIdempotented.of_ring ℤ) integerLeftNondegenerate
        integerLeftNondegenerate (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ)
        (NonUnitalModuleHom.id ℤ ℤ) :=
  (h ℤ (IsIdempotented.of_ring ℤ) ℤ ℤ integerLeftNondegenerate).2.2.2
    ℤ ℤ integerLeftNondegenerate
      (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ) (NonUnitalModuleHom.id ℤ ℤ)

end NonzeroZeroRightAction

section ZeroCarriers

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)

/-- A zero right carrier imposes no condition on the nondegenerate left carrier. -/
example {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) (h : TensorSmoothing.{uA, uN, uM, uN', uM'}) :
    letI := NonUnitalModule.zero (A := Aᵐᵒᵖ) (M := PUnit.{uN + 1})
    InverseIdentities hA PUnit.{uN + 1} hM ∧
      Bijectivity hA PUnit.{uN + 1} hM ∧ PrescribedEquivalence hA PUnit.{uN + 1} hM := by
  let _ := NonUnitalModule.zero (A := Aᵐᵒᵖ) (M := PUnit.{uN + 1})
  exact ⟨(h A hA PUnit.{uN + 1} M hM).1, (h A hA PUnit.{uN + 1} M hM).2.1,
    (h A hA PUnit.{uN + 1} M hM).2.2.1⟩

/-- A zero left carrier is nondegenerate even with its zero action. -/
example (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (h : TensorSmoothing.{uA, uN, uM, uN', uM'}) :
    letI := NonUnitalModule.zero (A := A) (M := PUnit.{uM + 1})
    InverseIdentities hA N (subsingletonNondegenerate (M := PUnit.{uM + 1})) ∧
      Bijectivity hA N (subsingletonNondegenerate (M := PUnit.{uM + 1})) ∧
      PrescribedEquivalence hA N (subsingletonNondegenerate (M := PUnit.{uM + 1})) := by
  let _ := NonUnitalModule.zero (A := A) (M := PUnit.{uM + 1})
  exact ⟨(h A hA N PUnit.{uM + 1} subsingletonNondegenerate).1,
    (h A hA N PUnit.{uM + 1} subsingletonNondegenerate).2.1,
    (h A hA N PUnit.{uM + 1} subsingletonNondegenerate).2.2.1⟩

/-- Both target carriers may be zero in the actual two-factor naturality squares. -/
example (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) (h : TensorSmoothing.{uA, uN, uM, uN', uM'}) :
    letI := NonUnitalModule.zero (A := Aᵐᵒᵖ) (M := PUnit.{uN' + 1})
    letI := NonUnitalModule.zero (A := A) (M := PUnit.{uM' + 1})
    Naturality hA hM subsingletonNondegenerate
        (0 : NonUnitalModuleHom Aᵐᵒᵖ N PUnit.{uN' + 1})
        (0 : NonUnitalModuleHom A M PUnit.{uM' + 1}) ∧
      EquivalenceNaturality hA hM subsingletonNondegenerate
        (0 : NonUnitalModuleHom Aᵐᵒᵖ N PUnit.{uN' + 1})
        (0 : NonUnitalModuleHom A M PUnit.{uM' + 1}) := by
  let _ := NonUnitalModule.zero (A := Aᵐᵒᵖ) (M := PUnit.{uN' + 1})
  let _ := NonUnitalModule.zero (A := A) (M := PUnit.{uM' + 1})
  exact (h A hA N M hM).2.2.2 PUnit.{uN' + 1} PUnit.{uM' + 1}
    subsingletonNondegenerate 0 0

end ZeroCarriers

section ZeroRing

/-- The zero ring and every right carrier are admitted with a zero left carrier. -/
example (N : Type uN) [AddCommGroup N]
    [NonUnitalModule PUnit.{uA + 1}ᵐᵒᵖ N]
    (h : TensorSmoothing.{uA, uN, uM, uN', uM'}) :
    letI := NonUnitalModule.zero (A := PUnit.{uA + 1}) (M := PUnit.{uM + 1})
    InverseIdentities (IsIdempotented.of_ring PUnit.{uA + 1}) N
        (subsingletonNondegenerate (M := PUnit.{uM + 1})) ∧
      Bijectivity (IsIdempotented.of_ring PUnit.{uA + 1}) N
        (subsingletonNondegenerate (M := PUnit.{uM + 1})) ∧
      PrescribedEquivalence (IsIdempotented.of_ring PUnit.{uA + 1}) N
        (subsingletonNondegenerate (M := PUnit.{uM + 1})) := by
  let _ := NonUnitalModule.zero (A := PUnit.{uA + 1}) (M := PUnit.{uM + 1})
  exact ⟨(h PUnit.{uA + 1} (IsIdempotented.of_ring PUnit.{uA + 1})
        N PUnit.{uM + 1} subsingletonNondegenerate).1,
    (h PUnit.{uA + 1} (IsIdempotented.of_ring PUnit.{uA + 1})
        N PUnit.{uM + 1} subsingletonNondegenerate).2.1,
    (h PUnit.{uA + 1} (IsIdempotented.of_ring PUnit.{uA + 1})
        N PUnit.{uM + 1} subsingletonNondegenerate).2.2.1⟩

end ZeroRing

section ComplexAlgebra

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
  (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hM : IsNondegenerate A M)

/-- Only A has a complex module structure; both original module carriers remain arbitrary. -/
example (h : TensorSmoothing.{uA, uN, uM, uN', uM'}) :
    InverseIdentities hA N hM ∧ Bijectivity hA N hM ∧ PrescribedEquivalence hA N hM ∧
      ∀ (N' : Type uN') [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
        (M' : Type uM') [AddCommGroup M'] [NonUnitalModule A M']
        (hM' : IsNondegenerate A M')
        (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'),
        Naturality hA hM hM' f g ∧ EquivalenceNaturality hA hM hM' f g :=
  h A hA N M hM

end ComplexAlgebra

end Langlands.Algebra.NonUnitalTensorSmoothingStatementsChecks
