import Langlands.Algebra.NondegenerateInductionAdjunctionStatements
import Langlands.Algebra.NonUnitalTensorHomAdjunctionProof

/-! # The canonical adjunction between Renard's actual P and pseudoF -/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateInductionAdjunction.PProof

open NonUnitalModuleTensor (tmul)

universe uA uB v

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule Aᵐᵒᵖ B]

local instance : NonUnitalModule B B := NonUnitalModule.regular B

variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hBA : ActionsCommute B A B) (hnd : IsNondegenerateBimodule B A B)

/-- The published intrinsic refinement, on the actual full-subcategory morphisms.
Its inverse is exactly the prescribed quotient lift from the statement. -/
def homAddEquiv (M : NondegenerateModuleCat.{uA, max uB v} A)
    (N : NondegenerateModuleCat.{uB, max uB v} B) :
    ((NondegenerateTensorFunctor.P hB hBA hnd).obj M ⟶ N) ≃+
      (M ⟶ (RenardHomFunctors.pseudoF hBA hA).obj N) where
  toFun f := ObjectProperty.homMk
    (NonUnitalTensorHomAdjunction.Left.refinedEquivalence A B M.obj B N.obj
      hBA hA M.property f.hom)
  invFun := pUncurry hA hB hBA hnd M N
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext A (fun _ _ => rfl))
  right_inv g := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro n
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro b
    rfl
  map_add' f g := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro n
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro b
    rfl

@[simp] theorem homAddEquiv_apply
    (M : NondegenerateModuleCat.{uA, max uB v} A)
    (N : NondegenerateModuleCat.{uB, max uB v} B)
    (f : (NondegenerateTensorFunctor.P hB hBA hnd).obj M ⟶ N)
    (n : M.obj) (b : B) :
    pEvaluationPairing hA hBA M N (homAddEquiv hA hB hBA hnd M N f) b n =
      f.hom.toAddMonoidHom (tmul A B M.obj b n) := rfl

/-- Naturality uses the published tensor map and restricted postcomposition. -/
theorem naturality_left
    {M' M : NondegenerateModuleCat.{uA, max uB v} A}
    {N : NondegenerateModuleCat.{uB, max uB v} B}
    (s : M' ⟶ M) (f : (NondegenerateTensorFunctor.P hB hBA hnd).obj M ⟶ N) :
    homAddEquiv hA hB hBA hnd M' N
        ((NondegenerateTensorFunctor.P hB hBA hnd).map s ≫ f) =
      s ≫ homAddEquiv hA hB hBA hnd M N f := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro b
  rfl

theorem naturality_right
    {M : NondegenerateModuleCat.{uA, max uB v} A}
    {N N' : NondegenerateModuleCat.{uB, max uB v} B}
    (f : (NondegenerateTensorFunctor.P hB hBA hnd).obj M ⟶ N) (t : N ⟶ N') :
    homAddEquiv hA hB hBA hnd M N' (f ≫ t) =
      homAddEquiv hA hB hBA hnd M N f ≫ (RenardHomFunctors.pseudoF hBA hA).map t := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro b
  rfl

/-- The actual functors are adjoint, with precisely the additive correspondence above. -/
def adjunction : (NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd) ⊣
    (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => (homAddEquiv hA hB hBA hnd M N).toEquiv
      homEquiv_naturality_left_symm := by
        intro M' M N s g
        apply (homAddEquiv hA hB hBA hnd M' N).injective
        change _ = homAddEquiv hA hB hBA hnd M' N
          ((NondegenerateTensorFunctor.P hB hBA hnd).map s ≫
            (homAddEquiv hA hB hBA hnd M N).symm g)
        exact ((homAddEquiv hA hB hBA hnd M' N).apply_symm_apply (s ≫ g)).trans
          ((naturality_left hA hB hBA hnd s
              ((homAddEquiv hA hB hBA hnd M N).symm g)).trans
            (congrArg (fun k => s ≫ k)
              ((homAddEquiv hA hB hBA hnd M N).apply_symm_apply g))).symm
      homEquiv_naturality_right := naturality_right hA hB hBA hnd }

@[simp] theorem adjunction_homEquiv
    (M : NondegenerateModuleCat.{uA, max uB v} A)
    (N : NondegenerateModuleCat.{uB, max uB v} B) :
    (adjunction hA hB hBA hnd).homEquiv M N =
      (homAddEquiv hA hB hBA hnd M N).toEquiv := by
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) M) N

/-- Both directions of whole-map naturality and coherence for this same adjunction. -/
theorem coherence :
    AdditiveAdjunctionCoherence _ _ (adjunction.{uA, uB, v} hA hB hBA hnd)
      (homAddEquiv.{uA, uB, v} hA hB hBA hnd) := by
  have forward : ∀ (M' M : NondegenerateModuleCat.{uA, max uB v} A)
      (N N' : NondegenerateModuleCat.{uB, max uB v} B) (s : M' ⟶ M) (t : N ⟶ N'),
      (homAddEquiv hA hB hBA hnd M' N').toAddMonoidHom.comp
          (compositionMap ((NondegenerateTensorFunctor.P hB hBA hnd).map s) t) =
        (compositionMap s ((RenardHomFunctors.pseudoF hBA hA).map t)).comp
          (homAddEquiv hA hB hBA hnd M N).toAddMonoidHom := by
    intro M' M N N' s t
    apply AddMonoidHom.ext
    intro f
    change homAddEquiv hA hB hBA hnd M' N'
        ((NondegenerateTensorFunctor.P hB hBA hnd).map s ≫ f ≫ t) =
      s ≫ homAddEquiv hA hB hBA hnd M N f ≫ (RenardHomFunctors.pseudoF hBA hA).map t
    rw [naturality_left, naturality_right]
  refine ⟨fun M N => (adjunction_homEquiv hA hB hBA hnd M N).symm,
    forward, ?_, ?_, ?_, ?_, ?_⟩
  · intro M' M N N' s t
    exact NonUnitalTensorHomAdjunction.inverse_naturality
      (homAddEquiv hA hB hBA hnd M N) (homAddEquiv hA hB hBA hnd M' N')
      _ _ (forward M' M N N' s t)
  · intro M M' s
    exact (adjunction hA hB hBA hnd).unit.naturality s
  · intro N N' t
    exact (adjunction hA hB hBA hnd).counit.naturality t
  · exact (adjunction hA hB hBA hnd).left_triangle_components
  · exact (adjunction hA hB hBA hnd).right_triangle_components

/-- All canonical clauses, including whole inverse lifts and actual unit/counit formulas. -/
theorem canonical : CanonicalPInductionAdjunction.{uA, uB, v} hA hB hBA hnd := by
  refine ⟨adjunction hA hB hBA hnd, homAddEquiv hA hB hBA hnd,
    coherence hA hB hBA hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact homAddEquiv_apply hA hB hBA hnd
  · intro M N
    rfl
  · exact pUncurry_toAddMonoidHom hA hB hBA hnd
  · intro M N g b n
    rfl
  · intro M N
    constructor
    · apply AddMonoidHom.ext
      intro f
      exact (homAddEquiv hA hB hBA hnd M N).symm_apply_apply f
    · apply AddMonoidHom.ext
      intro g
      exact (homAddEquiv hA hB hBA hnd M N).apply_symm_apply g
  · intro M n b
    rw [← (adjunction hA hB hBA hnd).homEquiv_id M,
      adjunction_homEquiv]
    rfl
  · intro N b h
    rw [← (adjunction hA hB hBA hnd).homEquiv_symm_id N,
      adjunction_homEquiv]
    rfl

end Langlands.Algebra.NondegenerateInductionAdjunction.PProof

namespace Langlands.Algebra.NondegenerateInductionAdjunction

universe uA uB v

/-- Renard's canonical P–pseudoF adjunction for the original arbitrary-ring additive models. -/
theorem nondegeneratePInductionAdjunction :
    NondegeneratePInductionAdjunctionTheorem.{uA, uB, v} := by
  intro A B _ _ _ hA hB hBA hnd
  exact PProof.canonical hA hB hBA hnd

/-- The complete theorem retains the specified original structures and no extra premise. -/
example : ∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    [hRight : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hRight)
    (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hRight),
    CanonicalPInductionAdjunction.{uA, uB, v} hA hB hBA hnd :=
  nondegeneratePInductionAdjunction.{uA, uB, v}

-- These include a ring universe strictly larger than the common carrier universe.
example : NondegeneratePInductionAdjunctionTheorem.{1, 0, 0} :=
  nondegeneratePInductionAdjunction.{1, 0, 0}

example : NondegeneratePInductionAdjunctionTheorem.{0, 1, 0} :=
  nondegeneratePInductionAdjunction.{0, 1, 0}

end Langlands.Algebra.NondegenerateInductionAdjunction
