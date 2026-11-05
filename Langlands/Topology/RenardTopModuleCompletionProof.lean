import Langlands.Topology.RenardTopModuleCompletionStatements

/-!
# The actual continuous-linear completion universal property

Proof of the published closed aggregate, using restriction to the dense
canonical image and the published chosen continuous-linear extensions.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory UniformSpace

universe u v w

namespace Langlands.Renard.TopModuleCompletion

attribute [local instance] ambientUniformSpace ambientUniformAddGroup
  ambientUniformConstSMul completeSpace separatedSpace completionContinuousSMul

theorem extensionTriangleStatement_proof : ExtensionTriangleStatement.{u, v} := by
  intro R _ _ _ M N f
  ext x
  exact extensionHom_coe R M N f x

theorem extensionUniqueStatement_proof : ExtensionUniqueStatement.{u, v} := by
  intro R _ _ _ M N f g h
  have heq : f.hom.fromCompletion = g.hom.hom :=
    ContinuousLinearMap.fromCompletion_unique f.hom g.hom.hom (fun x =>
      (congrArg (fun k : M ⟶ N.obj => k.hom x) h).symm)
  apply ObjectProperty.hom_ext
  ext z
  exact congrArg (fun l : Completion M →L[R] N.obj => l z) heq.symm

theorem rightUniversalStatement_proof : RightUniversalStatement.{u, v} := by
  intro R _ _ _ M
  refine ⟨Limits.IsInitial.ofUniqueHom
    (fun A => StructuredArrow.homMk (extensionHom R M A.right A.hom)
      (extensionTriangleStatement_proof R M A.right A.hom)) ?_⟩
  intro A g
  apply StructuredArrow.hom_ext
  exact extensionUniqueStatement_proof R M A.right A.hom g.right
    (StructuredArrow.w g)

section HomEquivalence

variable (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Restriction to the canonical image, with the published extension as inverse. -/
def completionHomEquiv (M : TopModuleCat.{v} R) (N : CompleteSepModuleCat.{u, v} R) :
    (completionObject R M ⟶ N) ≃ (M ⟶ N.obj) where
  toFun g := canonicalMap R M ≫ (inclusion R).map g
  invFun := extensionHom R M N
  left_inv g := (extensionUniqueStatement_proof R M N _ g rfl).symm
  right_inv f := extensionTriangleStatement_proof R M N f

/-- Naturality of restriction and extension for the existing completion functor. -/
def completionHomEquivData :
    Adjunction.CoreHomEquiv (completionFunctor.{u, v} R) (inclusion R) where
  homEquiv := completionHomEquiv R
  homEquiv_naturality_left_symm {X' X Y} f g := by
    change X ⟶ Y.obj at g
    change extensionHom R X' Y (f ≫ g) =
      (completionFunctor R).map f ≫ extensionHom R X Y g
    symm
    apply extensionUniqueStatement_proof R X' Y (f ≫ g)
    ext x
    change g.hom.fromCompletion (f.hom.completion (x : Completion X')) =
      g.hom (f.hom x)
    simp only [ContinuousLinearMap.completion_apply_coe,
      ContinuousLinearMap.fromCompletion_apply_coe]
  homEquiv_naturality_right {X Y Y'} f g := by
    ext x
    rfl

end HomEquivalence

theorem canonicalAdjunctionStatement_proof : CanonicalAdjunctionStatement.{u, v} := by
  intro R _ _ _
  let core := completionHomEquivData.{u, v} R
  let adj := Adjunction.mkOfHomEquiv core
  refine ⟨adj, ?_, ?_, ?_⟩
  · ext M x
    rfl
  · intro M N f
    change ((Adjunction.mkOfHomEquiv core).homEquiv M N).symm f =
      extensionHom R M N f
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  · intro M N g
    change (Adjunction.mkOfHomEquiv core).homEquiv M N g =
      canonicalMap R M ≫ (inclusion R).map g
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl

theorem canonicalMapStatement_proof : CanonicalMapStatement.{u, v} := by
  intro R _ _ _ M
  let : UniformSpace M := canonicalUniformSpace M
  constructor
  · exact Completion.denseRange_coe
  · intro hT
    let : T0Space M := hT
    exact Completion.isUniformEmbedding_coe M

theorem concreteUniversalStatement_proof : ConcreteUniversalStatement.{u, v, w} := by
  intro R _ _ _ M _ _ _ _ _ N _ _ _ _ _ _ _ f
  let : UniformSpace M := canonicalUniformSpace M
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  let : UniformContinuousConstSMul R M :=
    uniformContinuousConstSMul_of_continuousConstSMul R M
  let : UniformSpace N := canonicalUniformSpace N
  let : IsUniformAddGroup N := isUniformAddGroup_of_addCommGroup
  let : UniformContinuousConstSMul R N :=
    uniformContinuousConstSMul_of_continuousConstSMul R N
  have agree : ∀ x : M, concreteExtension R M N f (x : Completion M) = f x :=
    concreteExtension_coe R M N f
  have unique : ∀ g : Completion M →L[R] N,
      (∀ x : M, g (x : Completion M) = f x) →
        g = concreteExtension R M N f := by
    intro g h
    exact (ContinuousLinearMap.fromCompletion_unique f g
      (fun x => (h x).symm)).symm
  exact ⟨agree, unique, concreteExtension R M N f, agree, unique⟩

theorem fieldSpecializationStatement_proof : FieldSpecializationStatement.{u, v, w} := by
  intro k _ _ _
  refine ⟨?_, rightUniversalStatement_proof k, canonicalAdjunctionStatement_proof k,
    canonicalMapStatement_proof k, concreteUniversalStatement_proof k⟩
  intro M N f
  exact ⟨extensionTriangleStatement_proof k M N f,
    extensionUniqueStatement_proof k M N f⟩

/-- All seven published clauses, with independent coefficient and carrier universes. -/
theorem universalStatements_proof : UniversalStatements.{u, v, w} :=
  ⟨extensionTriangleStatement_proof, extensionUniqueStatement_proof,
    rightUniversalStatement_proof, canonicalAdjunctionStatement_proof,
    canonicalMapStatement_proof, concreteUniversalStatement_proof,
    fieldSpecializationStatement_proof⟩

end Langlands.Renard.TopModuleCompletion
