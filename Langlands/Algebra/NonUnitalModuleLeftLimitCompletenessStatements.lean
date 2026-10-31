import Langlands.Algebra.NonUnitalModuleLeftLimitUniformity
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Algebra.Ring.PUnit

/-!
# Closedness, density and completeness targets for the actual left-image module inverse limit

Renard I.1.4, printed p.9/PDF15, identifies the completion of a nondegenerate
module with the left-image inverse limit and says that the I.1.3 arguments
adapt. Closedness in the full discrete product and the generality of the
targets are internal. These proposition definitions provide statement coverage only.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uM

/-- The actual compatible families form a closed subset of the full product of
discrete original vector carriers. -/
def NonUnitalModuleLeftLimitClosedFamily (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  @IsClosed (Idempotent A → M)
    (NonUnitalModuleLeftLimit.discreteProductUniformSpace A M).toTopologicalSpace
    (leftCompatibleFamilies A M : Set (Idempotent A → M))

/-- The actual coordinate uniformity on the existing family carrier is complete. -/
def NonUnitalModuleLeftLimitComplete (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  @CompleteSpace (NonUnitalModuleLeftLimit A M) (NonUnitalModuleLeftLimit.uniformSpace A M)

/-- The original canonical additive map has dense range in the actual family topology. -/
def NonUnitalModuleLeftLimitCanonicalDense (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  @DenseRange (NonUnitalModuleLeftLimit A M)
    (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace M
    (NonUnitalModuleLeftLimit.canonical (A := A) (M := M))

/-- The same canonical map is a dense embedding for the two exact uniform topologies. -/
def NonUnitalModuleLeftLimitCanonicalDenseEmbedding (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  @IsDenseEmbedding M (NonUnitalModuleLeftLimit A M)
    (nonUnitalModuleUniformSpace A M).toTopologicalSpace
    (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace
    (NonUnitalModuleLeftLimit.canonical (A := A) (M := M))

/-- Closed target: closedness and completeness for every original module; density
under finite local units; dense embedding under finite local units and original
nondegeneracy. -/
def NonUnitalModuleLeftLimitDensityCompletenessTheorem : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
    NonUnitalModuleLeftLimitClosedFamily A M ∧
    NonUnitalModuleLeftLimitComplete A M ∧
    (IsIdempotented A → NonUnitalModuleLeftLimitCanonicalDense A M) ∧
    (IsIdempotented A → IsNondegenerate A M →
      NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M)

/-! Complete unapplied interfaces at independent ring/vector universes and at
both unequal assignments. -/

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitClosedFamily.{uA, uM}

example : (A : Type) → (M : Type 1) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitClosedFamily.{0, 1}

example : (A : Type 1) → (M : Type) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitClosedFamily.{1, 0}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitComplete.{uA, uM}

example : (A : Type) → (M : Type 1) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitComplete.{0, 1}

example : (A : Type 1) → (M : Type) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitComplete.{1, 0}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitCanonicalDense.{uA, uM}

example : (A : Type) → (M : Type 1) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitCanonicalDense.{0, 1}

example : (A : Type 1) → (M : Type) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitCanonicalDense.{1, 0}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitCanonicalDenseEmbedding.{uA, uM}

example : (A : Type) → (M : Type 1) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitCanonicalDenseEmbedding.{0, 1}

example : (A : Type 1) → (M : Type) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleLeftLimitCanonicalDenseEmbedding.{1, 0}

example : Prop :=
  @NonUnitalModuleLeftLimitDensityCompletenessTheorem.{uA, uM}

example : Prop :=
  @NonUnitalModuleLeftLimitDensityCompletenessTheorem.{0, 1}

example : Prop :=
  @NonUnitalModuleLeftLimitDensityCompletenessTheorem.{1, 0}

/-! The master body at the arbitrary and both unequal universe assignments. -/

example : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{uA, uM} =
    ∀ (A : Type uA) (M : Type uM)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      NonUnitalModuleLeftLimitClosedFamily A M ∧
      NonUnitalModuleLeftLimitComplete A M ∧
      (IsIdempotented A → NonUnitalModuleLeftLimitCanonicalDense A M) ∧
      (IsIdempotented A → IsNondegenerate A M →
        NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M) := rfl

example : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{0, 1} =
    ∀ (A : Type) (M : Type 1)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      NonUnitalModuleLeftLimitClosedFamily A M ∧
      NonUnitalModuleLeftLimitComplete A M ∧
      (IsIdempotented A → NonUnitalModuleLeftLimitCanonicalDense A M) ∧
      (IsIdempotented A → IsNondegenerate A M →
        NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M) := rfl

example : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{1, 0} =
    ∀ (A : Type 1) (M : Type)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      NonUnitalModuleLeftLimitClosedFamily A M ∧
      NonUnitalModuleLeftLimitComplete A M ∧
      (IsIdempotented A → NonUnitalModuleLeftLimitCanonicalDense A M) ∧
      (IsIdempotented A → IsNondegenerate A M →
        NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M) := rfl

/-! The selected topologies are the actual constructed ones. The ambient topology
is Mathlib's product of discrete topologies on the original vector carrier; the
family topology is the infimum of the discrete coordinate pullbacks and the
subspace topology of that product; the domain topology is the infimum of the
discrete pullbacks along the original left action of each idempotent. -/

example (A : Type uA) (M : Type uM) [NonUnitalRing A] :
    (NonUnitalModuleLeftLimit.discreteProductUniformSpace A M).toTopologicalSpace =
      @Pi.topologicalSpace (Idempotent A) (fun _ => M) (fun _ => ⊥) := rfl

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace =
      ⨅ e : Idempotent A,
        TopologicalSpace.induced (fun x : NonUnitalModuleLeftLimit A M => x.val e)
          (⊥ : TopologicalSpace M) :=
  UniformSpace.toTopologicalSpace_iInf

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace =
      @instTopologicalSpaceSubtype (Idempotent A → M) (· ∈ leftCompatibleFamilies A M)
        (@Pi.topologicalSpace (Idempotent A) (fun _ => M) (fun _ => ⊥)) :=
  congrArg (fun u : UniformSpace (NonUnitalModuleLeftLimit A M) => u.toTopologicalSpace)
    (NonUnitalModuleLeftLimit.uniformSpace_eq_subtype A M)

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    (nonUnitalModuleUniformSpace A M).toTopologicalSpace =
      ⨅ e : Idempotent A,
        TopologicalSpace.induced (fun m : M => (e : A) • m) (⊥ : TopologicalSpace M) :=
  UniformSpace.toTopologicalSpace_iInf

/-! The four predicate bodies, with the actual uniformities installed locally. -/

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    NonUnitalModuleLeftLimitClosedFamily A M =
      (let := NonUnitalModuleLeftLimit.discreteProductUniformSpace A M
       IsClosed {x : Idempotent A → M | (∀ e : Idempotent A, (e : A) • x e = x e) ∧
         ∀ e f : Idempotent A, e ≤ f → (e : A) • x f = x e}) := rfl

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    NonUnitalModuleLeftLimitComplete A M =
      (let := NonUnitalModuleLeftLimit.uniformSpace A M
       CompleteSpace (NonUnitalModuleLeftLimit A M)) := rfl

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    NonUnitalModuleLeftLimitCanonicalDense A M =
      (let := NonUnitalModuleLeftLimit.uniformSpace A M
       Dense (Set.range fun m : M => NonUnitalModuleLeftLimit.canonical (A := A) m)) := rfl

/-- Both topologies are named explicitly: with two local uniformities, instance
inference on the subtype could select a different codomain topology. -/
example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M =
      @IsDenseEmbedding M (NonUnitalModuleLeftLimit A M)
        (⨅ e : Idempotent A,
          UniformSpace.comap (fun m : M => (e : A) • m) (⊥ : UniformSpace M)).toTopologicalSpace
        (⨅ e : Idempotent A,
          UniformSpace.comap (fun x : NonUnitalModuleLeftLimit A M => x.val e)
            (⊥ : UniformSpace M)).toTopologicalSpace
        (NonUnitalModuleLeftLimit.canonical (A := A) (M := M)) := rfl

/-- The canonical map is the actual original family `m ↦ (e ↦ e • m)`. -/
example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] (m : M) (e : Idempotent A) :
    (NonUnitalModuleLeftLimit.canonical (A := A) m).val e = (e : A) • m := rfl

/-- The dense-embedding target selects the same codomain topology as the density target. -/
example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (h : NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M) :
    NonUnitalModuleLeftLimitCanonicalDense A M :=
  @IsDenseInducing.dense M (NonUnitalModuleLeftLimit A M)
    (nonUnitalModuleUniformSpace A M).toTopologicalSpace
    (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace _
    (@IsDenseEmbedding.toIsDenseInducing M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M).toTopologicalSpace
      (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace _ h)

/-- The dense-embedding target is inducing for the original topology and injective. -/
example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M →
      @Topology.IsInducing M (NonUnitalModuleLeftLimit A M)
        (nonUnitalModuleUniformSpace A M).toTopologicalSpace
        (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace
        (NonUnitalModuleLeftLimit.canonical (A := A) (M := M)) ∧
      Function.Injective (NonUnitalModuleLeftLimit.canonical (A := A) (M := M)) :=
  fun h =>
    ⟨@IsDenseInducing.toIsInducing M (NonUnitalModuleLeftLimit A M)
        (nonUnitalModuleUniformSpace A M).toTopologicalSpace
        (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace _
        (@IsDenseEmbedding.toIsDenseInducing M (NonUnitalModuleLeftLimit A M)
          (nonUnitalModuleUniformSpace A M).toTopologicalSpace
          (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace _ h),
      @IsDenseEmbedding.injective M (NonUnitalModuleLeftLimit A M)
        (nonUnitalModuleUniformSpace A M).toTopologicalSpace
        (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace _ h⟩

/-! The master specializes to every original module, including zero actions,
zero rings, trivial carriers and ordinary unital modules. -/

example (h : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{uA, uM})
    (A : Type uA) (M : Type uM) [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    NonUnitalModuleLeftLimitCanonicalDense A M ∧
      NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M :=
  ⟨(h A M).2.2.1 hA, (h A M).2.2.2 hA hM⟩

/-- Closedness and completeness need no unit law: the zero action of any original ring. -/
example (h : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{uA, uM})
    (A : Type uA) [NonUnitalRing A] (M : Type uM) [AddCommGroup M] :
    @NonUnitalModuleLeftLimitClosedFamily A M _ _ NonUnitalModule.zero ∧
      @NonUnitalModuleLeftLimitComplete A M _ _ NonUnitalModule.zero :=
  ⟨(@h A M _ _ NonUnitalModule.zero).1, (@h A M _ _ NonUnitalModule.zero).2.1⟩

/-- Density needs no vector nondegeneracy: the zero action of an idempotented ring. -/
example (h : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{uA, uM})
    (A : Type uA) [NonUnitalRing A] (M : Type uM) [AddCommGroup M] (hA : IsIdempotented A) :
    @NonUnitalModuleLeftLimitCanonicalDense A M _ _ NonUnitalModule.zero :=
  (@h A M _ _ NonUnitalModule.zero).2.2.1 hA

/-- The zero ring acting on the trivial carrier. -/
example (h : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{0, 1}) :
    @NonUnitalModuleLeftLimitComplete PUnit.{1} PUnit.{2} _ _ NonUnitalModule.zero :=
  (@h PUnit.{1} PUnit.{2} _ _ NonUnitalModule.zero).2.1

/-- An ordinary unital module is an original nondegenerate module over an idempotented ring. -/
example (h : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{uA, uM})
    (R : Type uA) [Ring R] (M : Type uM) [AddCommGroup M] [Module R M] :
    @NonUnitalModuleLeftLimitCanonicalDenseEmbedding R M _ _ (NonUnitalModule.ofModule R M) :=
  (@h R M _ _ (NonUnitalModule.ofModule R M)).2.2.2 (IsIdempotented.of_ring R)
    (fun m => ⟨⟨1, IsIdempotentElem.one⟩, one_smul R m⟩)

end Langlands.Algebra
