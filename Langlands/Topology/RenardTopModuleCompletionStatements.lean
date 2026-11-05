import Langlands.Topology.RenardTopModuleCompletion
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Universal-property statements for actual topological-module completion

These are propositions for the published completion and chosen maps under the
corrected continuous-linear convention for Renard A.III.1 example 2. The ring,
universe and adjunction packaging are internal elaborations. Proofs and the
printed all-continuous-maps problem remain separate.
-/

set_option autoImplicit false

open CategoryTheory UniformSpace

universe u v w

namespace Langlands.Renard.TopModuleCompletion

/-- The published chosen extension factors every actual continuous linear map. -/
def ExtensionTriangleStatement : Prop :=
  ∀ (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : TopModuleCat.{v} R) (N : CompleteSepModuleCat.{u, v} R)
    (f : M ⟶ N.obj),
    canonicalMap R M ≫ (inclusion R).map (extensionHom R M N f) = f

/-- Every competing continuous linear factor equals the published extension. -/
def ExtensionUniqueStatement : Prop :=
  ∀ (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : TopModuleCat.{v} R) (N : CompleteSepModuleCat.{u, v} R)
    (f : M ⟶ N.obj) (g : completionObject R M ⟶ N),
    canonicalMap R M ≫ (inclusion R).map g = f →
      g = extensionHom R M N f

/-- The actual canonical structured arrow is initial for the actual inclusion. -/
def RightUniversalStatement : Prop :=
  ∀ (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : TopModuleCat.{v} R),
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (T := inclusion R) (canonicalMap R M)))

/-- An adjunction for the existing functors has exactly the published unit
and exactly the specified forward and inverse Hom correspondences. -/
def CanonicalAdjunctionStatement : Prop :=
  ∀ (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R],
    ∃ adj : completionFunctor.{u, v} R ⊣ inclusion R,
      adj.unit = canonicalNatTrans R ∧
      (∀ (M : TopModuleCat.{v} R) (N : CompleteSepModuleCat.{u, v} R)
        (f : M ⟶ N.obj),
        (adj.homEquiv M N).symm f = extensionHom R M N f) ∧
      (∀ (M : TopModuleCat.{v} R) (N : CompleteSepModuleCat.{u, v} R)
        (g : completionObject R M ⟶ N),
        adj.homEquiv M N g = canonicalMap R M ≫ (inclusion R).map g)

/-- The actual canonical map is dense, and is a uniform embedding for a
separated source, with the canonical source and actual completion uniformities. -/
def CanonicalMapStatement : Prop :=
  ∀ (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : TopModuleCat.{v} R),
    letI : UniformSpace M := canonicalUniformSpace M
    DenseRange ((canonicalMap R M).hom : M → Completion M) ∧
      (T0Space M →
        @IsUniformEmbedding M (Completion M) (canonicalUniformSpace M)
          (inferInstance : UniformSpace (Completion M)) (canonicalMap R M).hom)

/-- The chosen concrete extension agrees with the original map and is the
unique continuous linear extension, with independent coefficient and carrier
universes and completeness only for the target's canonical uniformity. -/
def ConcreteUniversalStatement : Prop :=
  ∀ (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M]
    (N : Type w) [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul R N]
    [@CompleteSpace N (canonicalUniformSpace N)] [T0Space N] (f : M →L[R] N),
    letI : UniformSpace M := canonicalUniformSpace M
    letI : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
    letI : UniformContinuousConstSMul R M :=
      uniformContinuousConstSMul_of_continuousConstSMul R M
    (∀ x : M, concreteExtension R M N f (x : Completion M) = f x) ∧
    (∀ g : Completion M →L[R] N,
      (∀ x : M, g (x : Completion M) = f x) →
        g = concreteExtension R M N f) ∧
    ∃! g : Completion M →L[R] N, ∀ x : M, g (x : Completion M) = f x

/-- Exact topological-field specialization using the published field aliases,
including the concrete property with independent source and target universes. -/
def FieldSpecializationStatement : Prop :=
  ∀ (k : Type u) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k],
    (∀ (M : TopModuleCat.{v} k) (N : CompleteSepVectCat.{u, v} k)
      (f : M ⟶ N.obj),
      canonicalMap k M ≫ (inclusion k).map (fieldExtensionHom k M N f) = f ∧
      ∀ g : (fieldCompletionFunctor k).obj M ⟶ N,
        canonicalMap k M ≫ (inclusion k).map g = f →
          g = fieldExtensionHom k M N f) ∧
    (∀ M : TopModuleCat.{v} k,
      Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (T := inclusion k) (canonicalMap k M)))) ∧
    (∃ adj : fieldCompletionFunctor.{u, v} k ⊣ inclusion k,
      adj.unit = fieldCanonicalNatTrans k ∧
      (∀ (M : TopModuleCat.{v} k) (N : CompleteSepVectCat.{u, v} k)
        (f : M ⟶ N.obj),
        (adj.homEquiv M N).symm f = fieldExtensionHom k M N f) ∧
      (∀ (M : TopModuleCat.{v} k) (N : CompleteSepVectCat.{u, v} k)
        (g : (fieldCompletionFunctor k).obj M ⟶ N),
        adj.homEquiv M N g = canonicalMap k M ≫ (inclusion k).map g)) ∧
    (∀ M : TopModuleCat.{v} k,
      letI : UniformSpace M := canonicalUniformSpace M
      DenseRange ((canonicalMap k M).hom : M → Completion M) ∧
        (T0Space M →
          @IsUniformEmbedding M (Completion M) (canonicalUniformSpace M)
            (inferInstance : UniformSpace (Completion M)) (canonicalMap k M).hom)) ∧
    (∀ (M : Type v) [AddCommGroup M] [Module k M] [TopologicalSpace M]
      [IsTopologicalAddGroup M] [ContinuousSMul k M]
      (N : Type w) [AddCommGroup N] [Module k N] [TopologicalSpace N]
      [IsTopologicalAddGroup N] [ContinuousSMul k N]
      [@CompleteSpace N (canonicalUniformSpace N)] [T0Space N] (f : M →L[k] N),
      letI : UniformSpace M := canonicalUniformSpace M
      letI : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
      letI : UniformContinuousConstSMul k M :=
        uniformContinuousConstSMul_of_continuousConstSMul k M
      (∀ x : M, fieldConcreteExtension k M N f (x : Completion M) = f x) ∧
      (∀ g : Completion M →L[k] N,
        (∀ x : M, g (x : Completion M) = f x) →
          g = fieldConcreteExtension k M N f) ∧
      ∃! g : Completion M →L[k] N, ∀ x : M, g (x : Completion M) = f x)

/-- Closed aggregate: chosen factorization, arbitrary-competitor uniqueness,
initiality, canonical adjunction, density and separated embedding, concrete
universality, and the exact field specialization, in that order. -/
def UniversalStatements : Prop :=
  ExtensionTriangleStatement.{u, v} ∧
  ExtensionUniqueStatement.{u, v} ∧
  RightUniversalStatement.{u, v} ∧
  CanonicalAdjunctionStatement.{u, v} ∧
  CanonicalMapStatement.{u, v} ∧
  ConcreteUniversalStatement.{u, v, w} ∧
  FieldSpecializationStatement.{u, v, w}

end Langlands.Renard.TopModuleCompletion
