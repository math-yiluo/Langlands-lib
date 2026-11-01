import Langlands.Algebra.NonUnitalModuleCompletionFunctor
import Langlands.Algebra.NonUnitalModuleLeftLimitUniformity

/-!
# Completed submodule inclusion and the three ranges of I.1.5.3

Renard 2026, printed p.11/PDF17. These are proposition definitions;
the conclusions are reserved for a separate exact-target proof.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open NonUnitalModuleLeftLimit

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- The actual completed inclusion preserves its full coordinate additive map,
is injective, is a uniform embedding and has closed range in the named topology. -/
def NonUnitalModuleCompletionSubmoduleInclusion (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M) : Prop :=
  let _ := nonUnitalModule (M := S) hA
  let _ := nonUnitalModule (M := M) hA
  let _ := uniformSpace A S
  let _ := uniformSpace A M
  let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
    (uniformSpace A S).toTopologicalSpace
  let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
    (uniformSpace A M).toTopologicalSpace
  (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
    Function.Injective (mapHom hA S.subtype) ∧
    IsUniformEmbedding (mapHom hA S.subtype) ∧
    IsClosed (Set.range (mapHom hA S.subtype))

/-- The range of the actual completed subtype intertwiner is exactly the
closure of the canonical submodule image and each of the two sets in I.1.5.3. -/
def NonUnitalModuleCompletionSubmoduleRange (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M) : Prop :=
  let _ := nonUnitalModule (M := S) hA
  let _ := nonUnitalModule (M := M) hA
  let _ := uniformSpace A S
  let _ := uniformSpace A M
  let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
    (uniformSpace A S).toTopologicalSpace
  let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
    (uniformSpace A M).toTopologicalSpace
  Set.range (mapHom hA S.subtype) =
      closure (canonical (A := A) (M := M) '' (S : Set M)) ∧
    Set.range (mapHom hA S.subtype) =
      {x : NonUnitalModuleLeftLimit A M |
        ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} ∧
    Set.range (mapHom hA S.subtype) =
      {x : NonUnitalModuleLeftLimit A M |
        ∀ a : A, a • x ∈ canonical (A := A) (M := M) '' (S : Set M)}

/-- The source-facing submodule-completion target retains precisely
nondegeneracy of the original ambient action, at independent universes. -/
def NonUnitalModuleCompletionSubmoduleTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
      (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    IsNondegenerate A M → ∀ S : NonUnitalSubmodule A M,
      NonUnitalModuleCompletionSubmoduleInclusion hA M S ∧
      NonUnitalModuleCompletionSubmoduleRange hA M S

/-! Complete unapplied interfaces, including both unequal universe assignments. -/

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type uM) → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalSubmodule A M → Prop :=
  @NonUnitalModuleCompletionSubmoduleInclusion.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type uM) → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalSubmodule A M → Prop :=
  @NonUnitalModuleCompletionSubmoduleRange.{uA, uM}

example : Prop := NonUnitalModuleCompletionSubmoduleTheorem.{uA, uM}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type 1) → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalSubmodule A M → Prop :=
  @NonUnitalModuleCompletionSubmoduleInclusion.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type 1) → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalSubmodule A M → Prop :=
  @NonUnitalModuleCompletionSubmoduleRange.{0, 1}

example : Prop := NonUnitalModuleCompletionSubmoduleTheorem.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type 0) → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalSubmodule A M → Prop :=
  @NonUnitalModuleCompletionSubmoduleInclusion.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type 0) → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalSubmodule A M → Prop :=
  @NonUnitalModuleCompletionSubmoduleRange.{1, 0}

example : Prop := NonUnitalModuleCompletionSubmoduleTheorem.{1, 0}

/-! Exact expanded bodies at all three universe assignments. -/

example {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M) :
    NonUnitalModuleCompletionSubmoduleInclusion hA M S =
      (let _ := nonUnitalModule (M := S) hA
       let _ := nonUnitalModule (M := M) hA
       let _ := uniformSpace A S
       let _ := uniformSpace A M
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
         (uniformSpace A S).toTopologicalSpace
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
         (uniformSpace A M).toTopologicalSpace
       (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
         Function.Injective (mapHom hA S.subtype) ∧
         IsUniformEmbedding (mapHom hA S.subtype) ∧
         IsClosed (Set.range (mapHom hA S.subtype))) := rfl

example {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M) :
    NonUnitalModuleCompletionSubmoduleRange hA M S =
      (let _ := nonUnitalModule (M := S) hA
       let _ := nonUnitalModule (M := M) hA
       let _ := uniformSpace A S
       let _ := uniformSpace A M
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
         (uniformSpace A S).toTopologicalSpace
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
         (uniformSpace A M).toTopologicalSpace
       Set.range (mapHom hA S.subtype) =
           closure (canonical (A := A) (M := M) '' (S : Set M)) ∧
         Set.range (mapHom hA S.subtype) =
           {x : NonUnitalModuleLeftLimit A M |
             ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} ∧
         Set.range (mapHom hA S.subtype) =
           {x : NonUnitalModuleLeftLimit A M |
             ∀ a : A, a • x ∈ canonical (A := A) (M := M) '' (S : Set M)}) := rfl

example :
    NonUnitalModuleCompletionSubmoduleTheorem.{uA, uM} =
      (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
           (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
         IsNondegenerate A M → ∀ S : NonUnitalSubmodule A M,
           (let _ := nonUnitalModule (M := S) hA
           let _ := nonUnitalModule (M := M) hA
           let _ := uniformSpace A S
           let _ := uniformSpace A M
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
             (uniformSpace A S).toTopologicalSpace
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
             (uniformSpace A M).toTopologicalSpace
           (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
             Function.Injective (mapHom hA S.subtype) ∧
             IsUniformEmbedding (mapHom hA S.subtype) ∧
             IsClosed (Set.range (mapHom hA S.subtype))) ∧
           (let _ := nonUnitalModule (M := S) hA
           let _ := nonUnitalModule (M := M) hA
           let _ := uniformSpace A S
           let _ := uniformSpace A M
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
             (uniformSpace A S).toTopologicalSpace
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
             (uniformSpace A M).toTopologicalSpace
           Set.range (mapHom hA S.subtype) =
               closure (canonical (A := A) (M := M) '' (S : Set M)) ∧
             Set.range (mapHom hA S.subtype) =
               {x : NonUnitalModuleLeftLimit A M |
                 ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} ∧
             Set.range (mapHom hA S.subtype) =
               {x : NonUnitalModuleLeftLimit A M |
                 ∀ a : A, a • x ∈ canonical (A := A) (M := M) '' (S : Set M)})) := rfl

example {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M) :
    NonUnitalModuleCompletionSubmoduleInclusion hA M S =
      (let _ := nonUnitalModule (M := S) hA
       let _ := nonUnitalModule (M := M) hA
       let _ := uniformSpace A S
       let _ := uniformSpace A M
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
         (uniformSpace A S).toTopologicalSpace
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
         (uniformSpace A M).toTopologicalSpace
       (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
         Function.Injective (mapHom hA S.subtype) ∧
         IsUniformEmbedding (mapHom hA S.subtype) ∧
         IsClosed (Set.range (mapHom hA S.subtype))) := rfl

example {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M) :
    NonUnitalModuleCompletionSubmoduleRange hA M S =
      (let _ := nonUnitalModule (M := S) hA
       let _ := nonUnitalModule (M := M) hA
       let _ := uniformSpace A S
       let _ := uniformSpace A M
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
         (uniformSpace A S).toTopologicalSpace
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
         (uniformSpace A M).toTopologicalSpace
       Set.range (mapHom hA S.subtype) =
           closure (canonical (A := A) (M := M) '' (S : Set M)) ∧
         Set.range (mapHom hA S.subtype) =
           {x : NonUnitalModuleLeftLimit A M |
             ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} ∧
         Set.range (mapHom hA S.subtype) =
           {x : NonUnitalModuleLeftLimit A M |
             ∀ a : A, a • x ∈ canonical (A := A) (M := M) '' (S : Set M)}) := rfl

example :
    NonUnitalModuleCompletionSubmoduleTheorem.{0, 1} =
      (∀ (A : Type 0) [NonUnitalRing A] (hA : IsIdempotented A)
           (M : Type 1) [AddCommGroup M] [NonUnitalModule A M],
         IsNondegenerate A M → ∀ S : NonUnitalSubmodule A M,
           (let _ := nonUnitalModule (M := S) hA
           let _ := nonUnitalModule (M := M) hA
           let _ := uniformSpace A S
           let _ := uniformSpace A M
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
             (uniformSpace A S).toTopologicalSpace
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
             (uniformSpace A M).toTopologicalSpace
           (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
             Function.Injective (mapHom hA S.subtype) ∧
             IsUniformEmbedding (mapHom hA S.subtype) ∧
             IsClosed (Set.range (mapHom hA S.subtype))) ∧
           (let _ := nonUnitalModule (M := S) hA
           let _ := nonUnitalModule (M := M) hA
           let _ := uniformSpace A S
           let _ := uniformSpace A M
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
             (uniformSpace A S).toTopologicalSpace
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
             (uniformSpace A M).toTopologicalSpace
           Set.range (mapHom hA S.subtype) =
               closure (canonical (A := A) (M := M) '' (S : Set M)) ∧
             Set.range (mapHom hA S.subtype) =
               {x : NonUnitalModuleLeftLimit A M |
                 ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} ∧
             Set.range (mapHom hA S.subtype) =
               {x : NonUnitalModuleLeftLimit A M |
                 ∀ a : A, a • x ∈ canonical (A := A) (M := M) '' (S : Set M)})) := rfl

example {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type 0) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M) :
    NonUnitalModuleCompletionSubmoduleInclusion hA M S =
      (let _ := nonUnitalModule (M := S) hA
       let _ := nonUnitalModule (M := M) hA
       let _ := uniformSpace A S
       let _ := uniformSpace A M
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
         (uniformSpace A S).toTopologicalSpace
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
         (uniformSpace A M).toTopologicalSpace
       (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
         Function.Injective (mapHom hA S.subtype) ∧
         IsUniformEmbedding (mapHom hA S.subtype) ∧
         IsClosed (Set.range (mapHom hA S.subtype))) := rfl

example {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type 0) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M) :
    NonUnitalModuleCompletionSubmoduleRange hA M S =
      (let _ := nonUnitalModule (M := S) hA
       let _ := nonUnitalModule (M := M) hA
       let _ := uniformSpace A S
       let _ := uniformSpace A M
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
         (uniformSpace A S).toTopologicalSpace
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
         (uniformSpace A M).toTopologicalSpace
       Set.range (mapHom hA S.subtype) =
           closure (canonical (A := A) (M := M) '' (S : Set M)) ∧
         Set.range (mapHom hA S.subtype) =
           {x : NonUnitalModuleLeftLimit A M |
             ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} ∧
         Set.range (mapHom hA S.subtype) =
           {x : NonUnitalModuleLeftLimit A M |
             ∀ a : A, a • x ∈ canonical (A := A) (M := M) '' (S : Set M)}) := rfl

example :
    NonUnitalModuleCompletionSubmoduleTheorem.{1, 0} =
      (∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A)
           (M : Type 0) [AddCommGroup M] [NonUnitalModule A M],
         IsNondegenerate A M → ∀ S : NonUnitalSubmodule A M,
           (let _ := nonUnitalModule (M := S) hA
           let _ := nonUnitalModule (M := M) hA
           let _ := uniformSpace A S
           let _ := uniformSpace A M
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
             (uniformSpace A S).toTopologicalSpace
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
             (uniformSpace A M).toTopologicalSpace
           (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
             Function.Injective (mapHom hA S.subtype) ∧
             IsUniformEmbedding (mapHom hA S.subtype) ∧
             IsClosed (Set.range (mapHom hA S.subtype))) ∧
           (let _ := nonUnitalModule (M := S) hA
           let _ := nonUnitalModule (M := M) hA
           let _ := uniformSpace A S
           let _ := uniformSpace A M
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
             (uniformSpace A S).toTopologicalSpace
           let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
             (uniformSpace A M).toTopologicalSpace
           Set.range (mapHom hA S.subtype) =
               closure (canonical (A := A) (M := M) '' (S : Set M)) ∧
             Set.range (mapHom hA S.subtype) =
               {x : NonUnitalModuleLeftLimit A M |
                 ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} ∧
             Set.range (mapHom hA S.subtype) =
               {x : NonUnitalModuleLeftLimit A M |
                 ∀ a : A, a • x ∈ canonical (A := A) (M := M) '' (S : Set M)})) := rfl

/-! Competing actions, uniformities and topologies on the same completed
carriers do not replace the structures specified in either target. -/

example {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M)
    (otherActionS : NonUnitalModule A (NonUnitalModuleLeftLimit A S))
    (otherActionM : NonUnitalModule A (NonUnitalModuleLeftLimit A M))
    (otherUniformityS : UniformSpace (NonUnitalModuleLeftLimit A S))
    (otherUniformityM : UniformSpace (NonUnitalModuleLeftLimit A M))
    (otherTopologyS : TopologicalSpace (NonUnitalModuleLeftLimit A S))
    (otherTopologyM : TopologicalSpace (NonUnitalModuleLeftLimit A M)) :
    (let _ := otherActionS
     let _ := otherActionM
     let _ := otherUniformityS
     let _ := otherUniformityM
     let _ := otherTopologyS
     let _ := otherTopologyM
     NonUnitalModuleCompletionSubmoduleInclusion hA M S) =
      (let _ := nonUnitalModule (M := S) hA
       let _ := nonUnitalModule (M := M) hA
       let _ := uniformSpace A S
       let _ := uniformSpace A M
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
         (uniformSpace A S).toTopologicalSpace
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
         (uniformSpace A M).toTopologicalSpace
       (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
         Function.Injective (mapHom hA S.subtype) ∧
         IsUniformEmbedding (mapHom hA S.subtype) ∧
         IsClosed (Set.range (mapHom hA S.subtype))) := rfl

example {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (S : NonUnitalSubmodule A M)
    (otherActionS : NonUnitalModule A (NonUnitalModuleLeftLimit A S))
    (otherActionM : NonUnitalModule A (NonUnitalModuleLeftLimit A M))
    (otherUniformityS : UniformSpace (NonUnitalModuleLeftLimit A S))
    (otherUniformityM : UniformSpace (NonUnitalModuleLeftLimit A M))
    (otherTopologyS : TopologicalSpace (NonUnitalModuleLeftLimit A S))
    (otherTopologyM : TopologicalSpace (NonUnitalModuleLeftLimit A M)) :
    (let _ := otherActionS
     let _ := otherActionM
     let _ := otherUniformityS
     let _ := otherUniformityM
     let _ := otherTopologyS
     let _ := otherTopologyM
     NonUnitalModuleCompletionSubmoduleRange hA M S) =
      (let _ := nonUnitalModule (M := S) hA
       let _ := nonUnitalModule (M := M) hA
       let _ := uniformSpace A S
       let _ := uniformSpace A M
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
         (uniformSpace A S).toTopologicalSpace
       let _ : TopologicalSpace (NonUnitalModuleLeftLimit A M) :=
         (uniformSpace A M).toTopologicalSpace
       Set.range (mapHom hA S.subtype) =
           closure (canonical (A := A) (M := M) '' (S : Set M)) ∧
         Set.range (mapHom hA S.subtype) =
           {x : NonUnitalModuleLeftLimit A M |
             ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} ∧
         Set.range (mapHom hA S.subtype) =
           {x : NonUnitalModuleLeftLimit A M |
             ∀ a : A, a • x ∈ canonical (A := A) (M := M) '' (S : Set M)}) := rfl

/-! Same original scalar/vector carrier with its original zero action.
The source-facing specialization retains its nondegeneracy premise. -/

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (let _ : NonUnitalModule A A := NonUnitalModule.zero
     ∀ S : NonUnitalSubmodule A A, NonUnitalModuleCompletionSubmoduleInclusion hA A S) =
      (let _ : NonUnitalModule A A := NonUnitalModule.zero
       ∀ S : NonUnitalSubmodule A A,
         (let _ := nonUnitalModule (M := S) hA
          let _ := nonUnitalModule (M := A) hA
          let _ := uniformSpace A S
          let _ := uniformSpace A A
          let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
            (uniformSpace A S).toTopologicalSpace
          let _ : TopologicalSpace (NonUnitalModuleLeftLimit A A) :=
            (uniformSpace A A).toTopologicalSpace
          (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
            Function.Injective (mapHom hA S.subtype) ∧
            IsUniformEmbedding (mapHom hA S.subtype) ∧
            IsClosed (Set.range (mapHom hA S.subtype)))) := rfl

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (let _ : NonUnitalModule A A := NonUnitalModule.zero
     ∀ S : NonUnitalSubmodule A A, NonUnitalModuleCompletionSubmoduleRange hA A S) =
      (let _ : NonUnitalModule A A := NonUnitalModule.zero
       ∀ S : NonUnitalSubmodule A A,
         (let _ := nonUnitalModule (M := S) hA
          let _ := nonUnitalModule (M := A) hA
          let _ := uniformSpace A S
          let _ := uniformSpace A A
          let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
            (uniformSpace A S).toTopologicalSpace
          let _ : TopologicalSpace (NonUnitalModuleLeftLimit A A) :=
            (uniformSpace A A).toTopologicalSpace
          Set.range (mapHom hA S.subtype) =
              closure (canonical (A := A) (M := A) '' (S : Set A)) ∧
            Set.range (mapHom hA S.subtype) =
              {x : NonUnitalModuleLeftLimit A A |
                ∀ e : Idempotent A, ∃ n : A, n ∈ S ∧ (e : A) • n = x.val e} ∧
            Set.range (mapHom hA S.subtype) =
              {x : NonUnitalModuleLeftLimit A A |
                ∀ a : A, a • x ∈ canonical (A := A) (M := A) '' (S : Set A)})) := rfl

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (let _ : NonUnitalModule A A := NonUnitalModule.zero
     IsNondegenerate A A → ∀ S : NonUnitalSubmodule A A,
       NonUnitalModuleCompletionSubmoduleInclusion hA A S ∧ NonUnitalModuleCompletionSubmoduleRange hA A S) =
      (let _ : NonUnitalModule A A := NonUnitalModule.zero
       IsNondegenerate A A → ∀ S : NonUnitalSubmodule A A,
         (let _ := nonUnitalModule (M := S) hA
          let _ := nonUnitalModule (M := A) hA
          let _ := uniformSpace A S
          let _ := uniformSpace A A
          let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
            (uniformSpace A S).toTopologicalSpace
          let _ : TopologicalSpace (NonUnitalModuleLeftLimit A A) :=
            (uniformSpace A A).toTopologicalSpace
          (mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype ∧
            Function.Injective (mapHom hA S.subtype) ∧
            IsUniformEmbedding (mapHom hA S.subtype) ∧
            IsClosed (Set.range (mapHom hA S.subtype))) ∧
         (let _ := nonUnitalModule (M := S) hA
          let _ := nonUnitalModule (M := A) hA
          let _ := uniformSpace A S
          let _ := uniformSpace A A
          let _ : TopologicalSpace (NonUnitalModuleLeftLimit A S) :=
            (uniformSpace A S).toTopologicalSpace
          let _ : TopologicalSpace (NonUnitalModuleLeftLimit A A) :=
            (uniformSpace A A).toTopologicalSpace
          Set.range (mapHom hA S.subtype) =
              closure (canonical (A := A) (M := A) '' (S : Set A)) ∧
            Set.range (mapHom hA S.subtype) =
              {x : NonUnitalModuleLeftLimit A A |
                ∀ e : Idempotent A, ∃ n : A, n ∈ S ∧ (e : A) • n = x.val e} ∧
            Set.range (mapHom hA S.subtype) =
              {x : NonUnitalModuleLeftLimit A A |
                ∀ a : A, a • x ∈ canonical (A := A) (M := A) '' (S : Set A)})) := rfl

end Langlands.Algebra
