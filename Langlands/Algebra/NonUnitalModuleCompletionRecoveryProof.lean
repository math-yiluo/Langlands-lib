import Langlands.Algebra.NonUnitalModuleCompletionRecoveryStatements

/-!
# Recovery and faithfulness of actual module completion

Renard I.1.5, printed pp.10–11/PDF16–17. The proof works directly on
compatible families and their named original action.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uM uN

namespace NonUnitalModuleLeftLimit

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule A M] [NonUnitalModule A N]

/-- The canonical map onto the actual part is an additive bijection;
the inverse is evaluation at every fixing idempotent. -/
theorem partRecovery (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    NonUnitalModuleCompletionPartRecovery hA M := by
  let _ := nonUnitalModule (M := M) hA
  let f : M →+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M) :=
    { toFun := fun m => ⟨canonical m, by
        obtain ⟨e, he⟩ := hM m
        refine ⟨e, ?_⟩
        change scalarAction hA (e : A) (canonical m) = canonical m
        rw [scalarAction_canonical, he]⟩
      map_zero' := Subtype.ext (map_zero canonical)
      map_add' := fun m n => Subtype.ext (map_add canonical m n) }
  have hf : Function.Bijective f := by
    constructor
    · intro m n h
      exact canonical_injective hM (congrArg Subtype.val h)
    · intro x
      obtain ⟨e, he⟩ := x.property
      refine ⟨x.val.val e, ?_⟩
      apply Subtype.ext
      exact (idempotent_smul hA e x.val).symm.trans he
  let E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M) :=
    AddEquiv.ofBijective f hf
  refine ⟨E, ?_, ?_, ?_⟩
  · rfl
  · intro a m
    apply Subtype.ext
    exact (scalarAction_canonical hA a m).symm
  · intro x e he
    apply canonical_injective hM
    calc
      canonical (E.symm x) = x.val :=
        congrArg Subtype.val (E.apply_symm_apply x)
      _ = canonical (x.val.val e) :=
        he.symm.trans (idempotent_smul hA e x.val)

/-- Coordinatewise extension detects original maps from any nondegenerate
source, including an arbitrary ambient target action. -/
theorem mapAddHom_injective (hM : IsNondegenerate A M) :
    Function.Injective (mapAddHom (A := A) (M := M) (N := N)) := by
  intro f g hfg
  apply NonUnitalModuleHom.ext
  intro m
  obtain ⟨e, he⟩ := hM m
  have h := congrArg
    (fun F : NonUnitalModuleLeftLimit A M →+ NonUnitalModuleLeftLimit A N =>
      (F (canonical m)).val e) hfg
  change f ((e : A) • m) = g ((e : A) • m) at h
  rwa [he] at h

end NonUnitalModuleLeftLimit

variable {A : Type uA} [NonUnitalRing A]

/-- The actual nondegenerate-source completion functor is faithful. -/
theorem nondegenerateModuleCompletionFaithful_proof (hA : IsIdempotented A) :
    NondegenerateModuleCompletionFaithful.{uA, uM} hA := by
  refine ⟨?_⟩
  intro M N f g hfg
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleLeftLimit.mapAddHom_injective M.property
  exact congrArg NonUnitalModuleHom.toAddMonoidHom hfg

/-- The exact recovery and faithfulness target. -/
theorem nonUnitalModuleCompletionRecoveryFaithfulnessTheorem_proof :
    NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{uA, uM} := by
  intro A _ hA
  constructor
  · intro M _ _ hM
    exact NonUnitalModuleLeftLimit.partRecovery hA hM
  · exact nondegenerateModuleCompletionFaithful_proof hA

/-! Complete unapplied proof interfaces, including the arbitrary ambient target. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      NonUnitalModuleCompletionPartRecovery hA M :=
  @NonUnitalModuleLeftLimit.partRecovery.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → {N : Type uN} →
    [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    IsNondegenerate A M →
      Function.Injective
        (NonUnitalModuleLeftLimit.mapAddHom (A := A) (M := M) (N := N)) :=
  @NonUnitalModuleLeftLimit.mapAddHom_injective.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateModuleCompletionFunctor.{uA, uM} hA).Faithful :=
  @nondegenerateModuleCompletionFaithful_proof.{uA, uM}

example : NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{uA, uM} :=
  nonUnitalModuleCompletionRecoveryFaithfulnessTheorem_proof.{uA, uM}

/-! The whole theorem has exactly the canonical recovery and actual-functor body. -/

example :
    ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
        IsNondegenerate A M →
          (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
           ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
             (nondegeneratePart hA
                 (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
                 E.toAddMonoidHom =
               NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
             (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
             (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M))
               (e : Idempotent A),
               (e : A) • x.val = x.val → E.symm x = x.val.val e))) ∧
      (nondegenerateModuleCompletionFunctor.{uA, uM} hA).Faithful :=
  nonUnitalModuleCompletionRecoveryFaithfulnessTheorem_proof.{uA, uM}

/-! Both unequal scalar/vector universe assignments retain the entire interfaces. -/

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      NonUnitalModuleCompletionPartRecovery hA M :=
  @NonUnitalModuleLeftLimit.partRecovery.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      NonUnitalModuleCompletionPartRecovery hA M :=
  @NonUnitalModuleLeftLimit.partRecovery.{1, 0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateModuleCompletionFunctor.{0, 1} hA).Faithful :=
  @nondegenerateModuleCompletionFaithful_proof.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateModuleCompletionFunctor.{1, 0} hA).Faithful :=
  @nondegenerateModuleCompletionFaithful_proof.{1, 0}

example : NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{0, 1} :=
  nonUnitalModuleCompletionRecoveryFaithfulnessTheorem_proof.{0, 1}

example : NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{1, 0} :=
  nonUnitalModuleCompletionRecoveryFaithfulnessTheorem_proof.{1, 0}

/-! The original same-carrier zero action is retained with actual nondegeneracy. -/

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    let _ : NonUnitalModule A A := NonUnitalModule.zero
    IsNondegenerate A A → NonUnitalModuleCompletionPartRecovery hA A := by
  let _ : NonUnitalModule A A := NonUnitalModule.zero
  exact NonUnitalModuleLeftLimit.partRecovery hA

end Langlands.Algebra
