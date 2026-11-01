import Langlands.Algebra.NonUnitalModuleSmoothingCompletionStatements

/-!
# The actual smoothing/completion adjunction

The direct compatible-family proof of Renard I.1.5, printed pp.10–11/PDF16–17.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uN uM uV

namespace NonUnitalModuleSmoothingCompletion

variable {A : Type uA} [NonUnitalRing A]
  {N : Type uN} {M : Type uM} [AddCommGroup N] [AddCommGroup M]
  [NonUnitalModule A N] [NonUnitalModule A M]

private def partVector (hA : IsIdempotented A) (e : Idempotent A) (n : N) :
    nondegeneratePart hA N :=
  ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩

/-- Extension into actual compatible families, with no target nondegeneracy needed. -/
def extendFamily (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A (nondegeneratePart hA N) M) (n : N) :
    NonUnitalModuleLeftLimit A M :=
  ⟨fun e => f (partVector hA e n), by
    constructor
    · intro e
      rw [← f.map_smul]
      apply congrArg f
      apply Subtype.ext
      exact (mul_smul (e : A) (e : A) n).symm.trans
        (congrArg (fun a : A => a • n) e.property.eq)
    · intro e d hed
      rw [← f.map_smul]
      apply congrArg f
      apply Subtype.ext
      exact (mul_smul (e : A) (d : A) n).symm.trans
        (congrArg (fun a : A => a • n) ((Idempotent.le_iff_mul e d).mp hed).2)⟩

@[simp] theorem extendFamily_val (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
    (n : N) (e : Idempotent A) :
    (extendFamily hA f n).val e =
      f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩ := rfl

/-- The extension is an actual original intertwiner for the specified family action. -/
def extendHom (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A (nondegeneratePart hA N) M) :
    @NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M) _ _ _ _
      (NonUnitalModuleLeftLimit.nonUnitalModule hA) := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  exact
    { toFun := extendFamily hA f
      map_zero' := by
        apply Subtype.ext
        funext e
        change f (partVector hA e 0) = 0
        rw [show partVector hA e (0 : N) = 0 from Subtype.ext (smul_zero _),
          f.map_zero]
      map_add' := by
        intro n n'
        apply Subtype.ext
        funext e
        change f (partVector hA e (n + n')) =
          f (partVector hA e n) + f (partVector hA e n')
        rw [show partVector hA e (n + n') =
          partVector hA e n + partVector hA e n' from
            Subtype.ext (smul_add (e : A) n n'), f.map_add]
      map_smul' := by
        intro a n
        apply Subtype.ext
        funext e
        classical
        obtain ⟨d, hd⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA)
          {(e : A) * a}
        have hed : ((e : A) * a) * (d : A) = (e : A) * a :=
          (hd ((e : A) * a) (by simp)).2
        change f (partVector hA e (a • n)) =
          (NonUnitalModuleLeftLimit.scalarAction hA a (extendFamily hA f n)).val e
        rw [NonUnitalModuleLeftLimit.scalarAction_val hA a _ e d hed]
        change f (partVector hA e (a • n)) = ((e : A) * a) • f (partVector hA d n)
        rw [← f.map_smul]
        apply congrArg f
        apply Subtype.ext
        change (e : A) • (a • n) = ((e : A) * a) • ((d : A) • n)
        simp only [← mul_smul, hed] }

@[simp] theorem extendHom_val (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A (nondegeneratePart hA N) M)
    (n : N) (e : Idempotent A) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    ((extendHom hA f).toAddMonoidHom n).val e =
      f ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩ := rfl

/-- Extension preserves pointwise addition of original part intertwiners. -/
theorem extendHom_add (hA : IsIdempotented A)
    (f g : NonUnitalModuleHom A (nondegeneratePart hA N) M) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    extendHom hA (f + g) = extendHom hA f + extendHom hA g := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  rfl

/-- On the actual part the extension agrees with the actual canonical family map. -/
theorem extendHom_restrict (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A (nondegeneratePart hA N) M) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    (NonUnitalModuleLeftLimit.canonicalHom hA).comp f =
      (extendHom hA f).comp (nondegeneratePart hA N).subtype := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  apply NonUnitalModuleHom.ext
  intro p
  apply Subtype.ext
  funext e
  change (e : A) • f p = f (partVector hA e p.val)
  rw [← f.map_smul]
  apply congrArg f
  apply Subtype.ext
  rfl

/-- A map into the family module takes each actual part vector into the canonical
image. A fixing idempotent gives an explicit preimage. -/
theorem part_image_exists (hA : IsIdempotented A) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    ∀ (phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M))
      (p : nondegeneratePart hA N),
      ∃ m : M, NonUnitalModuleLeftLimit.canonicalHom (M := M) hA m = phi p.val := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  dsimp only
  intro phi p
  obtain ⟨e, he⟩ := p.property
  refine ⟨(phi p.val).val e, ?_⟩
  change NonUnitalModuleLeftLimit.canonical _ = phi p.val
  rw [← NonUnitalModuleLeftLimit.idempotent_smul hA e (phi p.val),
    ← phi.map_smul, he]

/-- Restrict to the actual part and recover the unique original target value. -/
def restrictHom (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M) →
      NonUnitalModuleHom A (nondegeneratePart hA N) M := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  dsimp only
  intro phi
  let j := NonUnitalModuleLeftLimit.canonicalHom (M := M) hA
  have hj : Function.Injective j :=
    NonUnitalModuleLeftLimit.canonical_injective hM
  let r (p : nondegeneratePart hA N) : M :=
    Classical.choose (part_image_exists hA phi p)
  have hr (p : nondegeneratePart hA N) : j (r p) = phi p.val :=
    Classical.choose_spec (part_image_exists hA phi p)
  exact
    { toFun := r
      map_zero' := hj (by rw [hr, j.map_zero]; exact phi.map_zero)
      map_add' := fun p q => hj (by
        rw [hr, j.map_add, hr, hr]
        exact phi.map_add p.val q.val)
      map_smul' := fun a p => hj (by
        change j (r (a • p)) = j (a • r p)
        rw [hr, j.map_smul, hr]
        exact phi.map_smul a p.val) }

/-- Whole-map restriction for the recovered original intertwiner. -/
theorem canonicalHom_restrictHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    ∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
      (NonUnitalModuleLeftLimit.canonicalHom hA).comp (restrictHom hA hM phi) =
        phi.comp (nondegeneratePart hA N).subtype := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  dsimp only
  intro phi
  apply NonUnitalModuleHom.ext
  intro p
  exact Classical.choose_spec (part_image_exists hA phi p)

/-- Recovery followed by coordinate extension is the identity on all ambient maps. -/
theorem extendHom_restrictHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    ∀ phi : NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M),
      extendHom hA (restrictHom hA hM phi) = phi := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  dsimp only
  intro phi
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  funext e
  change restrictHom hA hM phi (partVector hA e n) = (phi n).val e
  apply NonUnitalModuleLeftLimit.canonical_injective hM
  have hr := congrArg
    (fun f : NonUnitalModuleHom A (nondegeneratePart hA N)
      (NonUnitalModuleLeftLimit A M) => f (partVector hA e n))
    (canonicalHom_restrictHom hA hM phi)
  change NonUnitalModuleLeftLimit.canonical
      (restrictHom hA hM phi (partVector hA e n)) = phi ((e : A) • n) at hr
  rw [phi.map_smul, NonUnitalModuleLeftLimit.idempotent_smul hA e (phi n)] at hr
  exact hr

/-- Coordinate extension separates original part intertwiners. -/
theorem extendHom_injective (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    Function.Injective (extendHom (N := N) hA (M := M)) := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  dsimp only
  intro f g hfg
  apply NonUnitalModuleHom.ext
  intro p
  apply NonUnitalModuleLeftLimit.canonical_injective hM
  have hf := congrArg
    (fun k : NonUnitalModuleHom A (nondegeneratePart hA N)
      (NonUnitalModuleLeftLimit A M) => k p) (extendHom_restrict hA f)
  have hg := congrArg
    (fun k : NonUnitalModuleHom A (nondegeneratePart hA N)
      (NonUnitalModuleLeftLimit A M) => k p) (extendHom_restrict hA g)
  change NonUnitalModuleLeftLimit.canonical (f p) = extendHom hA f p.val at hf
  change NonUnitalModuleLeftLimit.canonical (g p) = extendHom hA g p.val at hg
  exact hf.trans ((congrArg (fun k => k.toAddMonoidHom p.val) hfg).trans hg.symm)

/-- The actual additive Hom correspondence for independent original actions. -/
def homAddEquiv (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
      NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M) := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  exact
    { toFun := extendHom hA
      invFun := restrictHom hA hM
      left_inv := fun f => extendHom_injective hA hM
        (extendHom_restrictHom hA hM (extendHom hA f))
      right_inv := extendHom_restrictHom hA hM
      map_add' := extendHom_add hA }

/-- The correspondence proves the per-action Prop target. -/
theorem homEquivalence (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    NonUnitalModuleSmoothingCompletionHomEquivalence hA N M := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  refine ⟨homAddEquiv hA hM, ?_, canonicalHom_restrictHom hA hM⟩
  intro f n e
  rfl

/-- The original additive correspondence with the actual full-subcategory wrappers. -/
def categoricalHomEquiv (hA : IsIdempotented A)
    (N : NonUnitalModuleCat.{uA, max uA uV} A)
    (M : NondegenerateModuleCat.{uA, max uA uV} A) :
    ((nondegeneratePartFunctor hA).obj N ⟶ M) ≃
      (N ⟶ (nondegenerateModuleCompletionFunctor hA).obj M) := by
  let E := homAddEquiv (N := N) (M := M.obj) hA M.property
  exact
    { toFun := fun f => E f.hom
      invFun := fun phi => ObjectProperty.homMk (E.symm phi)
      left_inv := by
        intro f
        apply ObjectProperty.hom_ext
        exact E.symm_apply_apply f.hom
      right_inv := E.apply_symm_apply }

@[simp] theorem categoricalHomEquiv_val (hA : IsIdempotented A)
    (N : NonUnitalModuleCat.{uA, max uA uV} A)
    (M : NondegenerateModuleCat.{uA, max uA uV} A)
    (f : (nondegeneratePartFunctor hA).obj N ⟶ M)
    (n : N) (e : Idempotent A) :
    ((categoricalHomEquiv hA N M f).toAddMonoidHom n).val e =
      f.hom.toAddMonoidHom ⟨(e : A) • n, e, by rw [← mul_smul, e.property.eq]⟩ := rfl

theorem categoricalHomEquiv_naturality_left (hA : IsIdempotented A)
    {N' N : NonUnitalModuleCat.{uA, max uA uV} A}
    {M : NondegenerateModuleCat.{uA, max uA uV} A}
    (f : N' ⟶ N) (g : (nondegeneratePartFunctor hA).obj N ⟶ M) :
    categoricalHomEquiv hA N' M ((nondegeneratePartFunctor hA).map f ≫ g) =
      f ≫ categoricalHomEquiv hA N M g := by
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  funext e
  change g.hom.toAddMonoidHom
      ⟨f.toAddMonoidHom ((e : A) • n),
        (f.map_mem_nondegeneratePart hA (partVector hA e n).property)⟩ =
    g.hom.toAddMonoidHom (partVector hA e (f.toAddMonoidHom n))
  apply congrArg g.hom.toAddMonoidHom
  apply Subtype.ext
  exact f.map_smul (e : A) n

theorem categoricalHomEquiv_naturality_right (hA : IsIdempotented A)
    {N : NonUnitalModuleCat.{uA, max uA uV} A}
    {M M' : NondegenerateModuleCat.{uA, max uA uV} A}
    (f : (nondegeneratePartFunctor hA).obj N ⟶ M) (g : M ⟶ M') :
    categoricalHomEquiv hA N M' (f ≫ g) =
      categoricalHomEquiv hA N M f ≫ (nondegenerateModuleCompletionFunctor hA).map g := by
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  rfl

/-- A genuine adjunction between the actual saturated smoothing/completion functors. -/
def adjunction (hA : IsIdempotented A) :
    nondegeneratePartFunctor.{uA, max uA uV} hA ⊣
      nondegenerateModuleCompletionFunctor.{uA, max uA uV} hA :=
  Adjunction.mkOfHomEquiv
    { homEquiv := categoricalHomEquiv hA
      homEquiv_naturality_left_symm := by
        intro N' N M f g
        apply (categoricalHomEquiv hA N' M).injective
        rw [(categoricalHomEquiv hA N' M).apply_symm_apply,
          categoricalHomEquiv_naturality_left,
          (categoricalHomEquiv hA N M).apply_symm_apply]
      homEquiv_naturality_right := categoricalHomEquiv_naturality_right hA }

@[simp] theorem adjunction_homEquiv (hA : IsIdempotented A) :
    (adjunction.{uA, uV} hA).homEquiv = categoricalHomEquiv hA :=
  Adjunction.mkOfHomEquiv_homEquiv _

/-- The actual adjunction satisfies all coordinate, whole-map and additive clauses. -/
theorem adjunctionStatement (hA : IsIdempotented A) :
    NonUnitalModuleSmoothingCompletionAdjunction.{uA, uV} hA := by
  refine ⟨adjunction hA, ?_, ?_, ?_⟩
  · intro N M f n e
    rw [adjunction_homEquiv]
    rfl
  · intro N M phi
    rw [adjunction_homEquiv]
    exact canonicalHom_restrictHom hA M.property phi
  · intro N M f g
    rw [adjunction_homEquiv]
    exact extendHom_add hA f.hom g.hom

end NonUnitalModuleSmoothingCompletion

/-- Renard I.1.5 smoothing/completion adjunction, with independent original data. -/
theorem nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof :
    NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{uA, uN, uM} := by
  intro A _ hA
  constructor
  · intro N M _ _ _ _ hM
    exact NonUnitalModuleSmoothingCompletion.homEquivalence hA hM
  · exact NonUnitalModuleSmoothingCompletion.adjunctionStatement hA

/-! Complete unapplied interfaces preserve all original actions and universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {N : Type uN} → {M : Type uM} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
         NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M)) :=
  @NonUnitalModuleSmoothingCompletion.homAddEquiv.{uA, uN, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {N : Type uN} → {M : Type uM} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      NonUnitalModuleSmoothingCompletionHomEquivalence hA N M :=
  @NonUnitalModuleSmoothingCompletion.homEquivalence.{uA, uN, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    nondegeneratePartFunctor.{uA, max uA uV} hA ⊣
      nondegenerateModuleCompletionFunctor.{uA, max uA uV} hA :=
  @NonUnitalModuleSmoothingCompletion.adjunction.{uA, uV}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NonUnitalModuleSmoothingCompletionAdjunction.{uA, uV} hA :=
  @NonUnitalModuleSmoothingCompletion.adjunctionStatement.{uA, uV}

example : NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{uA, uN, uM} :=
  nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof.{uA, uN, uM}

/-! The entire theorem has exactly the original-action correspondence and actual
categorical adjunction body, including its whole-map restriction and addition. -/

example :
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
             adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g))) :=
  nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof.{uA, uN, uM}

/-! Unequal scalar/source/target universes preserve complete unapplied types. -/

example : {A : Type 0} → [NonUnitalRing A] →
    {N : Type 1} → {M : Type 1} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
         NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M)) :=
  @NonUnitalModuleSmoothingCompletion.homAddEquiv.{0, 1, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {N : Type 1} → {M : Type 1} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      NonUnitalModuleSmoothingCompletionHomEquivalence hA N M :=
  @NonUnitalModuleSmoothingCompletion.homEquivalence.{0, 1, 1}

example : NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{0, 1, 1} :=
  nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof.{0, 1, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {N : Type 0} → {M : Type 0} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
         NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M)) :=
  @NonUnitalModuleSmoothingCompletion.homAddEquiv.{1, 0, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {N : Type 0} → {M : Type 0} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      NonUnitalModuleSmoothingCompletionHomEquivalence hA N M :=
  @NonUnitalModuleSmoothingCompletion.homEquivalence.{1, 0, 0}

example : NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{1, 0, 0} :=
  nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof.{1, 0, 0}

example : {A : Type 0} → [NonUnitalRing A] →
    {N : Type 0} → {M : Type 1} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
         NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M)) :=
  @NonUnitalModuleSmoothingCompletion.homAddEquiv.{0, 0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {N : Type 0} → {M : Type 1} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      NonUnitalModuleSmoothingCompletionHomEquivalence hA N M :=
  @NonUnitalModuleSmoothingCompletion.homEquivalence.{0, 0, 1}

example : NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{0, 0, 1} :=
  nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof.{0, 0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {N : Type 1} → {M : Type 0} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
         NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M)) :=
  @NonUnitalModuleSmoothingCompletion.homAddEquiv.{1, 1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {N : Type 1} → {M : Type 0} → [AddCommGroup N] → [AddCommGroup M] →
    [NonUnitalModule A N] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
      NonUnitalModuleSmoothingCompletionHomEquivalence hA N M :=
  @NonUnitalModuleSmoothingCompletion.homEquivalence.{1, 1, 0}

example : NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{1, 1, 0} :=
  nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof.{1, 1, 0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    nondegeneratePartFunctor.{0, max 0 1} hA ⊣
      nondegenerateModuleCompletionFunctor.{0, max 0 1} hA :=
  @NonUnitalModuleSmoothingCompletion.adjunction.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NonUnitalModuleSmoothingCompletionAdjunction.{0, 1} hA :=
  @NonUnitalModuleSmoothingCompletion.adjunctionStatement.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    nondegeneratePartFunctor.{1, max 1 0} hA ⊣
      nondegenerateModuleCompletionFunctor.{1, max 1 0} hA :=
  @NonUnitalModuleSmoothingCompletion.adjunction.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NonUnitalModuleSmoothingCompletionAdjunction.{1, 0} hA :=
  @NonUnitalModuleSmoothingCompletion.adjunctionStatement.{1, 0}

/-! A competing family action cannot replace the specified action. -/

example {A : Type uA} [NonUnitalRing A]
    {N : Type uN} {M : Type uM} [AddCommGroup N] [AddCommGroup M]
    [NonUnitalModule A N] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (other : NonUnitalModule A (NonUnitalModuleLeftLimit A M)) :
    let _ := other
    (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
       NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M)) :=
  NonUnitalModuleSmoothingCompletion.homAddEquiv hA hM

/-! The original same-carrier zero actions keep the actual target premise. -/

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    let _ : NonUnitalModule A A := NonUnitalModule.zero
    IsNondegenerate A A → NonUnitalModuleSmoothingCompletionHomEquivalence hA A A := by
  let _ : NonUnitalModule A A := NonUnitalModule.zero
  exact NonUnitalModuleSmoothingCompletion.homEquivalence hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] :
    let _ : NonUnitalModule A A := NonUnitalModule.zero
    IsNondegenerate A M → NonUnitalModuleSmoothingCompletionHomEquivalence hA A M := by
  let _ : NonUnitalModule A A := NonUnitalModule.zero
  exact NonUnitalModuleSmoothingCompletion.homEquivalence hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule A N] :
    let _ : NonUnitalModule A A := NonUnitalModule.zero
    IsNondegenerate A A → NonUnitalModuleSmoothingCompletionHomEquivalence hA N A := by
  let _ : NonUnitalModule A A := NonUnitalModule.zero
  exact NonUnitalModuleSmoothingCompletion.homEquivalence hA

end Langlands.Algebra
