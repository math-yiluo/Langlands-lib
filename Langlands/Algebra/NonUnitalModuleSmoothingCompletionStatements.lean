import Langlands.Algebra.NonUnitalModuleCompletionFunctor
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Smoothing and completion: additive correspondence and actual adjunction

Renard I.1.5, printed pp.10–11/PDF16–17. These are proposition definitions,
with the original ambient source action and actual smoothing/completion functors.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uN uM uV

variable {A : Type uA} [NonUnitalRing A]

/-- The additive correspondence, pinned by coordinate extension and whole-map
restriction through the actual canonical family map. Only the master target
requires nondegeneracy of the target module; the source module is arbitrary. -/
def NonUnitalModuleSmoothingCompletionHomEquivalence (hA : IsIdempotented A)
    (N : Type uN) (M : Type uM) [AddCommGroup N] [AddCommGroup M]
    [NonUnitalModule A N] [NonUnitalModule A M] : Prop :=
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
      NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
    (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
      (n : N) (e : Idempotent A),
      (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
    (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
      (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
        phi.comp (nondegeneratePart hA N).subtype)

/-- The actual smoothing functor is left adjoint to the actual completion
functor at a carrier universe saturated by the independently sized scalar ring.
Its actual Hom equivalences have the specified extension, restriction and addition. -/
def NonUnitalModuleSmoothingCompletionAdjunction (hA : IsIdempotented A) : Prop :=
  ∃ adj : nondegeneratePartFunctor.{uA, max uA uV} hA ⊣
      nondegenerateModuleCompletionFunctor.{uA, max uA uV} hA,
    (∀ (N : NonUnitalModuleCat.{uA, max uA uV} A)
      (M : NondegenerateModuleCat.{uA, max uA uV} A)
      (f : (nondegeneratePartFunctor hA).obj N ⟶ M) (n : N) (e : Idempotent A),
      ((adj.homEquiv N M f).toAddMonoidHom n).val e =
        f.hom.toAddMonoidHom ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
    (∀ (N : NonUnitalModuleCat.{uA, max uA uV} A)
      (M : NondegenerateModuleCat.{uA, max uA uV} A)
      (phi : N ⟶ (nondegenerateModuleCompletionFunctor hA).obj M),
      let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA
      (NonUnitalModuleLeftLimit.canonicalHom (M := M.obj) hA).comp
          ((adj.homEquiv N M).symm phi).hom =
        phi.comp (nondegeneratePart hA N).subtype) ∧
    (∀ (N : NonUnitalModuleCat.{uA, max uA uV} A)
      (M : NondegenerateModuleCat.{uA, max uA uV} A)
      (f g : (nondegeneratePartFunctor hA).obj N ⟶ M),
      adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g)

/-- The smoothing/completion clauses of I.1.5 for arbitrary original ambient
sources, nondegenerate targets, and the actual saturated categorical functors. -/
def NonUnitalModuleSmoothingCompletionAdjunctionTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    (∀ (N : Type uN) (M : Type uM) [AddCommGroup N] [AddCommGroup M]
      [NonUnitalModule A N] [NonUnitalModule A M],
      IsNondegenerate A M → NonUnitalModuleSmoothingCompletionHomEquivalence hA N M) ∧
    NonUnitalModuleSmoothingCompletionAdjunction.{uA, max uN uM} hA

/-! Complete unapplied interfaces and exact bodies at independent universes. -/

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (N : Type uN) → (M : Type uM) → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleSmoothingCompletionHomEquivalence.{uA, uN, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NonUnitalModuleSmoothingCompletionAdjunction.{uA, uV}

example : Prop := NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{uA, uN, uM}

example {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) (M : Type uM) [AddCommGroup N] [AddCommGroup M]
    [NonUnitalModule A N] [NonUnitalModule A M] :
    NonUnitalModuleSmoothingCompletionHomEquivalence hA N M =
      (
       let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
           NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
         (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
           (n : N) (e : Idempotent A),
           (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
         (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
           (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
             phi.comp (nondegeneratePart hA N).subtype)) := rfl

example {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) :
    NonUnitalModuleSmoothingCompletionAdjunction.{uA, uV} hA =
      (
       ∃ adj : nondegeneratePartFunctor.{uA, max uA uV} hA ⊣
           nondegenerateModuleCompletionFunctor.{uA, max uA uV} hA,
         (∀ (N : NonUnitalModuleCat.{uA, max uA uV} A)
           (M : NondegenerateModuleCat.{uA, max uA uV} A)
           (f : (nondegeneratePartFunctor hA).obj N ⟶ M) (n : N) (e : Idempotent A),
           ((adj.homEquiv N M f).toAddMonoidHom n).val e =
             f.hom.toAddMonoidHom ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
         (∀ (N : NonUnitalModuleCat.{uA, max uA uV} A)
           (M : NondegenerateModuleCat.{uA, max uA uV} A)
           (phi : N ⟶ (nondegenerateModuleCompletionFunctor hA).obj M),
           let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA
           (NonUnitalModuleLeftLimit.canonicalHom (M := M.obj) hA).comp
               ((adj.homEquiv N M).symm phi).hom =
             phi.comp (nondegeneratePart hA N).subtype) ∧
         (∀ (N : NonUnitalModuleCat.{uA, max uA uV} A)
           (M : NondegenerateModuleCat.{uA, max uA uV} A)
           (f g : (nondegeneratePartFunctor hA).obj N ⟶ M),
           adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g)) := rfl

example :
    NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{uA, uN, uM} =
      (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (N : Type uN) (M : Type uM) [AddCommGroup N] [AddCommGroup M]
          [NonUnitalModule A N] [NonUnitalModule A M],
          IsNondegenerate A M →
            (
             let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
             ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
                 NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
               (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
                 (n : N) (e : Idempotent A),
                 (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
               (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
                 (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
                   phi.comp (nondegeneratePart hA N).subtype))) ∧
        (
         ∃ adj : nondegeneratePartFunctor.{uA, max uA (max uN uM)} hA ⊣
             nondegenerateModuleCompletionFunctor.{uA, max uA (max uN uM)} hA,
           (∀ (N : NonUnitalModuleCat.{uA, max uA (max uN uM)} A)
             (M : NondegenerateModuleCat.{uA, max uA (max uN uM)} A)
             (f : (nondegeneratePartFunctor hA).obj N ⟶ M) (n : N) (e : Idempotent A),
             ((adj.homEquiv N M f).toAddMonoidHom n).val e =
               f.hom.toAddMonoidHom ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
           (∀ (N : NonUnitalModuleCat.{uA, max uA (max uN uM)} A)
             (M : NondegenerateModuleCat.{uA, max uA (max uN uM)} A)
             (phi : N ⟶ (nondegenerateModuleCompletionFunctor hA).obj M),
             let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA
             (NonUnitalModuleLeftLimit.canonicalHom (M := M.obj) hA).comp
                 ((adj.homEquiv N M).symm phi).hom =
               phi.comp (nondegeneratePart hA N).subtype) ∧
           (∀ (N : NonUnitalModuleCat.{uA, max uA (max uN uM)} A)
             (M : NondegenerateModuleCat.{uA, max uA (max uN uM)} A)
             (f g : (nondegeneratePartFunctor hA).obj N ⟶ M),
             adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g))) := rfl

/-! Both unequal scalar/vector assignments, including full expanded bodies. -/

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    (N : Type 1) → (M : Type 1) → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleSmoothingCompletionHomEquivalence.{0, 1, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NonUnitalModuleSmoothingCompletionAdjunction.{0, 1}

example : Prop := NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{0, 1, 1}

example {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 1) (M : Type 1) [AddCommGroup N] [AddCommGroup M]
    [NonUnitalModule A N] [NonUnitalModule A M] :
    NonUnitalModuleSmoothingCompletionHomEquivalence hA N M =
      (
       let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
           NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
         (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
           (n : N) (e : Idempotent A),
           (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
         (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
           (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
             phi.comp (nondegeneratePart hA N).subtype)) := rfl

example {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) :
    NonUnitalModuleSmoothingCompletionAdjunction.{0, 1} hA =
      (
       ∃ adj : nondegeneratePartFunctor.{0, max 0 1} hA ⊣
           nondegenerateModuleCompletionFunctor.{0, max 0 1} hA,
         (∀ (N : NonUnitalModuleCat.{0, max 0 1} A)
           (M : NondegenerateModuleCat.{0, max 0 1} A)
           (f : (nondegeneratePartFunctor hA).obj N ⟶ M) (n : N) (e : Idempotent A),
           ((adj.homEquiv N M f).toAddMonoidHom n).val e =
             f.hom.toAddMonoidHom ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
         (∀ (N : NonUnitalModuleCat.{0, max 0 1} A)
           (M : NondegenerateModuleCat.{0, max 0 1} A)
           (phi : N ⟶ (nondegenerateModuleCompletionFunctor hA).obj M),
           let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA
           (NonUnitalModuleLeftLimit.canonicalHom (M := M.obj) hA).comp
               ((adj.homEquiv N M).symm phi).hom =
             phi.comp (nondegeneratePart hA N).subtype) ∧
         (∀ (N : NonUnitalModuleCat.{0, max 0 1} A)
           (M : NondegenerateModuleCat.{0, max 0 1} A)
           (f g : (nondegeneratePartFunctor hA).obj N ⟶ M),
           adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g)) := rfl

example :
    NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{0, 1, 1} =
      (∀ (A : Type 0) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (N : Type 1) (M : Type 1) [AddCommGroup N] [AddCommGroup M]
          [NonUnitalModule A N] [NonUnitalModule A M],
          IsNondegenerate A M →
            (
             let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
             ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
                 NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
               (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
                 (n : N) (e : Idempotent A),
                 (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
               (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
                 (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
                   phi.comp (nondegeneratePart hA N).subtype))) ∧
        (
         ∃ adj : nondegeneratePartFunctor.{0, max 0 (max 1 1)} hA ⊣
             nondegenerateModuleCompletionFunctor.{0, max 0 (max 1 1)} hA,
           (∀ (N : NonUnitalModuleCat.{0, max 0 (max 1 1)} A)
             (M : NondegenerateModuleCat.{0, max 0 (max 1 1)} A)
             (f : (nondegeneratePartFunctor hA).obj N ⟶ M) (n : N) (e : Idempotent A),
             ((adj.homEquiv N M f).toAddMonoidHom n).val e =
               f.hom.toAddMonoidHom ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
           (∀ (N : NonUnitalModuleCat.{0, max 0 (max 1 1)} A)
             (M : NondegenerateModuleCat.{0, max 0 (max 1 1)} A)
             (phi : N ⟶ (nondegenerateModuleCompletionFunctor hA).obj M),
             let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA
             (NonUnitalModuleLeftLimit.canonicalHom (M := M.obj) hA).comp
                 ((adj.homEquiv N M).symm phi).hom =
               phi.comp (nondegeneratePart hA N).subtype) ∧
           (∀ (N : NonUnitalModuleCat.{0, max 0 (max 1 1)} A)
             (M : NondegenerateModuleCat.{0, max 0 (max 1 1)} A)
             (f g : (nondegeneratePartFunctor hA).obj N ⟶ M),
             adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g))) := rfl

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    (N : Type 0) → (M : Type 0) → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleSmoothingCompletionHomEquivalence.{1, 0, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NonUnitalModuleSmoothingCompletionAdjunction.{1, 0}

example : Prop := NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{1, 0, 0}

example {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type 0) (M : Type 0) [AddCommGroup N] [AddCommGroup M]
    [NonUnitalModule A N] [NonUnitalModule A M] :
    NonUnitalModuleSmoothingCompletionHomEquivalence hA N M =
      (
       let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
           NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
         (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
           (n : N) (e : Idempotent A),
           (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
         (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
           (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
             phi.comp (nondegeneratePart hA N).subtype)) := rfl

example {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) :
    NonUnitalModuleSmoothingCompletionAdjunction.{1, 0} hA =
      (
       ∃ adj : nondegeneratePartFunctor.{1, max 1 0} hA ⊣
           nondegenerateModuleCompletionFunctor.{1, max 1 0} hA,
         (∀ (N : NonUnitalModuleCat.{1, max 1 0} A)
           (M : NondegenerateModuleCat.{1, max 1 0} A)
           (f : (nondegeneratePartFunctor hA).obj N ⟶ M) (n : N) (e : Idempotent A),
           ((adj.homEquiv N M f).toAddMonoidHom n).val e =
             f.hom.toAddMonoidHom ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
         (∀ (N : NonUnitalModuleCat.{1, max 1 0} A)
           (M : NondegenerateModuleCat.{1, max 1 0} A)
           (phi : N ⟶ (nondegenerateModuleCompletionFunctor hA).obj M),
           let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA
           (NonUnitalModuleLeftLimit.canonicalHom (M := M.obj) hA).comp
               ((adj.homEquiv N M).symm phi).hom =
             phi.comp (nondegeneratePart hA N).subtype) ∧
         (∀ (N : NonUnitalModuleCat.{1, max 1 0} A)
           (M : NondegenerateModuleCat.{1, max 1 0} A)
           (f g : (nondegeneratePartFunctor hA).obj N ⟶ M),
           adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g)) := rfl

example :
    NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{1, 0, 0} =
      (∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (N : Type 0) (M : Type 0) [AddCommGroup N] [AddCommGroup M]
          [NonUnitalModule A N] [NonUnitalModule A M],
          IsNondegenerate A M →
            (
             let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
             ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
                 NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
               (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
                 (n : N) (e : Idempotent A),
                 (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
               (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
                 (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
                   phi.comp (nondegeneratePart hA N).subtype))) ∧
        (
         ∃ adj : nondegeneratePartFunctor.{1, max 1 (max 0 0)} hA ⊣
             nondegenerateModuleCompletionFunctor.{1, max 1 (max 0 0)} hA,
           (∀ (N : NonUnitalModuleCat.{1, max 1 (max 0 0)} A)
             (M : NondegenerateModuleCat.{1, max 1 (max 0 0)} A)
             (f : (nondegeneratePartFunctor hA).obj N ⟶ M) (n : N) (e : Idempotent A),
             ((adj.homEquiv N M f).toAddMonoidHom n).val e =
               f.hom.toAddMonoidHom ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
           (∀ (N : NonUnitalModuleCat.{1, max 1 (max 0 0)} A)
             (M : NondegenerateModuleCat.{1, max 1 (max 0 0)} A)
             (phi : N ⟶ (nondegenerateModuleCompletionFunctor hA).obj M),
             let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA
             (NonUnitalModuleLeftLimit.canonicalHom (M := M.obj) hA).comp
                 ((adj.homEquiv N M).symm phi).hom =
               phi.comp (nondegeneratePart hA N).subtype) ∧
           (∀ (N : NonUnitalModuleCat.{1, max 1 (max 0 0)} A)
             (M : NondegenerateModuleCat.{1, max 1 (max 0 0)} A)
             (f g : (nondegeneratePartFunctor hA).obj N ⟶ M),
             adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g))) := rfl

/-! Source and target carrier universes are independent of each other as well. -/

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    (N : Type 0) → (M : Type 1) → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleSmoothingCompletionHomEquivalence.{0, 0, 1}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    (N : Type 1) → (M : Type 0) → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleSmoothingCompletionHomEquivalence.{1, 1, 0}

/-! The prescribed family action takes precedence over another same-carrier action. -/

example (hA : IsIdempotented A)
    (N : Type uN) (M : Type uM) [AddCommGroup N] [AddCommGroup M]
    [NonUnitalModule A N] [NonUnitalModule A M]
    (other : NonUnitalModule A (NonUnitalModuleLeftLimit A M)) :
    let _ := other
    NonUnitalModuleSmoothingCompletionHomEquivalence hA N M =
      (
       let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
           NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
         (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
           (n : N) (e : Idempotent A),
           (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
         (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
           (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
             phi.comp (nondegeneratePart hA N).subtype)) := rfl

/-! Original same-carrier zero actions retain the actual target hypothesis. -/

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (let _ : NonUnitalModule A A := NonUnitalModule.zero
     IsNondegenerate A A → NonUnitalModuleSmoothingCompletionHomEquivalence hA A A) =
      (let _ : NonUnitalModule A A := NonUnitalModule.zero
       IsNondegenerate A A →
         (
          let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := A) hA
          ∃ E : NonUnitalModuleHom A (nondegeneratePart hA A) A ≃+
              NonUnitalModuleHom A A (NonUnitalModuleLeftLimit A A),
            (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA A) A)
              (n : A) (e : Idempotent A),
              (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
            (∀ phi : NonUnitalModuleHom A A (NonUnitalModuleLeftLimit A A),
              (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
                phi.comp (nondegeneratePart hA A).subtype))) := rfl

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] :
    (let _ : NonUnitalModule A A := NonUnitalModule.zero
     IsNondegenerate A M → NonUnitalModuleSmoothingCompletionHomEquivalence hA A M) =
      (let _ : NonUnitalModule A A := NonUnitalModule.zero
       IsNondegenerate A M →
         (
          let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
          ∃ E : NonUnitalModuleHom A (nondegeneratePart hA A) M ≃+
              NonUnitalModuleHom A A (NonUnitalModuleLeftLimit A M),
            (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA A) M)
              (n : A) (e : Idempotent A),
              (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
            (∀ phi : NonUnitalModuleHom A A (NonUnitalModuleLeftLimit A M),
              (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
                phi.comp (nondegeneratePart hA A).subtype))) := rfl

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule A N] :
    (let _ : NonUnitalModule A A := NonUnitalModule.zero
     IsNondegenerate A A → NonUnitalModuleSmoothingCompletionHomEquivalence hA N A) =
      (let _ : NonUnitalModule A A := NonUnitalModule.zero
       IsNondegenerate A A →
         (
          let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := A) hA
          ∃ E : NonUnitalModuleHom A (nondegeneratePart hA N) A ≃+
              NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A A),
            (∀ (f : NonUnitalModuleHom A (nondegeneratePart hA N) A)
              (n : N) (e : Idempotent A),
              (E f n).val e = f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩) ∧
            (∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A A),
              (NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
                phi.comp (nondegeneratePart hA N).subtype))) := rfl

end Langlands.Algebra
