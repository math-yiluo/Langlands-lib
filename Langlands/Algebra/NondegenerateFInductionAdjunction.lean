import Langlands.Algebra.NondegenerateInductionAdjunctionStatements
import Langlands.Algebra.NonUnitalTensorHomAdjunctionProof

/-! # The canonical adjunction between Renard's actual F and I -/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateInductionAdjunction.FProof

open NonUnitalModuleTensor (tmul)

universe uA uB v

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule A B]

local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B

variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B)

/-- The published intrinsic refinement, on the actual full-subcategory morphisms.
Its inverse is exactly the prescribed quotient lift from the statement. -/
def homAddEquiv (N : NondegenerateModuleCat.{uB, max uB v} B)
    (M : NondegenerateModuleCat.{uA, max uB v} A) :
    ((NondegenerateTensorFunctor.F hA hAB hnd).obj N ⟶ M) ≃+
      (N ⟶ (RenardHomFunctors.I hAB hB).obj M) where
  toFun f := ObjectProperty.homMk
    (NonUnitalTensorHomAdjunction.Left.refinedEquivalence B A N.obj B M.obj
      hAB hB N.property f.hom)
  invFun := fUncurry hA hB hAB hnd N M
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext B (fun _ _ => rfl))
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
    (N : NondegenerateModuleCat.{uB, max uB v} B)
    (M : NondegenerateModuleCat.{uA, max uB v} A)
    (f : (NondegenerateTensorFunctor.F hA hAB hnd).obj N ⟶ M)
    (n : N.obj) (b : B) :
    fEvaluationPairing hB hAB N M (homAddEquiv hA hB hAB hnd N M f) b n =
      f.hom.toAddMonoidHom (tmul B B N.obj b n) := rfl

/-- Naturality uses the published tensor map and restricted postcomposition. -/
theorem naturality_left
    {N' N : NondegenerateModuleCat.{uB, max uB v} B}
    {M : NondegenerateModuleCat.{uA, max uB v} A}
    (s : N' ⟶ N) (f : (NondegenerateTensorFunctor.F hA hAB hnd).obj N ⟶ M) :
    homAddEquiv hA hB hAB hnd N' M
        ((NondegenerateTensorFunctor.F hA hAB hnd).map s ≫ f) =
      s ≫ homAddEquiv hA hB hAB hnd N M f := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro b
  rfl

theorem naturality_right
    {N : NondegenerateModuleCat.{uB, max uB v} B}
    {M M' : NondegenerateModuleCat.{uA, max uB v} A}
    (f : (NondegenerateTensorFunctor.F hA hAB hnd).obj N ⟶ M) (t : M ⟶ M') :
    homAddEquiv hA hB hAB hnd N M' (f ≫ t) =
      homAddEquiv hA hB hAB hnd N M f ≫ (RenardHomFunctors.I hAB hB).map t := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro b
  rfl

/-- The actual functors are adjoint, with precisely the additive correspondence above. -/
def adjunction : (NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd) ⊣
    (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N M => (homAddEquiv hA hB hAB hnd N M).toEquiv
      homEquiv_naturality_left_symm := by
        intro N' N M s g
        apply (homAddEquiv hA hB hAB hnd N' M).injective
        change _ = homAddEquiv hA hB hAB hnd N' M
          ((NondegenerateTensorFunctor.F hA hAB hnd).map s ≫
            (homAddEquiv hA hB hAB hnd N M).symm g)
        exact ((homAddEquiv hA hB hAB hnd N' M).apply_symm_apply (s ≫ g)).trans
          ((naturality_left hA hB hAB hnd s
              ((homAddEquiv hA hB hAB hnd N M).symm g)).trans
            (congrArg (fun k => s ≫ k)
              ((homAddEquiv hA hB hAB hnd N M).apply_symm_apply g))).symm
      homEquiv_naturality_right := naturality_right hA hB hAB hnd }

@[simp] theorem adjunction_homEquiv
    (N : NondegenerateModuleCat.{uB, max uB v} B)
    (M : NondegenerateModuleCat.{uA, max uB v} A) :
    (adjunction hA hB hAB hnd).homEquiv N M =
      (homAddEquiv hA hB hAB hnd N M).toEquiv := by
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) N) M

/-- Both directions of whole-map naturality and coherence for this same adjunction. -/
theorem coherence :
    AdditiveAdjunctionCoherence _ _ (adjunction.{uA, uB, v} hA hB hAB hnd)
      (homAddEquiv.{uA, uB, v} hA hB hAB hnd) := by
  have forward : ∀ (N' N : NondegenerateModuleCat.{uB, max uB v} B)
      (M M' : NondegenerateModuleCat.{uA, max uB v} A) (s : N' ⟶ N) (t : M ⟶ M'),
      (homAddEquiv hA hB hAB hnd N' M').toAddMonoidHom.comp
          (compositionMap ((NondegenerateTensorFunctor.F hA hAB hnd).map s) t) =
        (compositionMap s ((RenardHomFunctors.I hAB hB).map t)).comp
          (homAddEquiv hA hB hAB hnd N M).toAddMonoidHom := by
    intro N' N M M' s t
    apply AddMonoidHom.ext
    intro f
    change homAddEquiv hA hB hAB hnd N' M'
        ((NondegenerateTensorFunctor.F hA hAB hnd).map s ≫ f ≫ t) =
      s ≫ homAddEquiv hA hB hAB hnd N M f ≫ (RenardHomFunctors.I hAB hB).map t
    rw [naturality_left, naturality_right]
  refine ⟨fun N M => (adjunction_homEquiv hA hB hAB hnd N M).symm,
    forward, ?_, ?_, ?_, ?_, ?_⟩
  · intro N' N M M' s t
    exact NonUnitalTensorHomAdjunction.inverse_naturality
      (homAddEquiv hA hB hAB hnd N M) (homAddEquiv hA hB hAB hnd N' M')
      _ _ (forward N' N M M' s t)
  · intro N N' s
    exact (adjunction hA hB hAB hnd).unit.naturality s
  · intro M M' t
    exact (adjunction hA hB hAB hnd).counit.naturality t
  · exact (adjunction hA hB hAB hnd).left_triangle_components
  · exact (adjunction hA hB hAB hnd).right_triangle_components

/-- All canonical clauses, including whole inverse lifts and actual unit/counit formulas. -/
theorem canonical : CanonicalFInductionAdjunction.{uA, uB, v} hA hB hAB hnd := by
  refine ⟨adjunction hA hB hAB hnd, homAddEquiv hA hB hAB hnd,
    coherence hA hB hAB hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact homAddEquiv_apply hA hB hAB hnd
  · intro N M
    rfl
  · exact fUncurry_toAddMonoidHom hA hB hAB hnd
  · intro N M g b n
    rfl
  · intro N M
    constructor
    · apply AddMonoidHom.ext
      intro f
      exact (homAddEquiv hA hB hAB hnd N M).symm_apply_apply f
    · apply AddMonoidHom.ext
      intro g
      exact (homAddEquiv hA hB hAB hnd N M).apply_symm_apply g
  · intro N n b
    rw [← (adjunction hA hB hAB hnd).homEquiv_id N,
      adjunction_homEquiv]
    rfl
  · intro M b h
    rw [← (adjunction hA hB hAB hnd).homEquiv_symm_id M,
      adjunction_homEquiv]
    rfl

end Langlands.Algebra.NondegenerateInductionAdjunction.FProof

namespace Langlands.Algebra.NondegenerateInductionAdjunction

universe uA uB v

/-- Renard's canonical F–I adjunction for the original arbitrary-ring additive models. -/
theorem nondegenerateFInductionAdjunction :
    NondegenerateFInductionAdjunctionTheorem.{uA, uB, v} := by
  intro A B _ _ _ hA hB hAB hnd
  exact FProof.canonical hA hB hAB hnd

/-- The complete theorem retains the specified original structures and no extra premise. -/
example : ∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    [hLeft : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hLeft (NonUnitalModule.rightRegular B))
    (hnd : @IsNondegenerateBimodule A B B _ _ _ hLeft (NonUnitalModule.rightRegular B)),
    CanonicalFInductionAdjunction.{uA, uB, v} hA hB hAB hnd :=
  nondegenerateFInductionAdjunction.{uA, uB, v}

-- These include a ring universe strictly larger than the common carrier universe.
example : NondegenerateFInductionAdjunctionTheorem.{1, 0, 0} :=
  nondegenerateFInductionAdjunction.{1, 0, 0}

example : NondegenerateFInductionAdjunctionTheorem.{0, 1, 0} :=
  nondegenerateFInductionAdjunction.{0, 1, 0}

end Langlands.Algebra.NondegenerateInductionAdjunction
