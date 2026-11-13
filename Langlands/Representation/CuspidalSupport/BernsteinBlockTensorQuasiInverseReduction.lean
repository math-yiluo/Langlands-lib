import Langlands.Representation.CuspidalSupport.BernsteinBlockTensorQuasiInverseStatement
import Langlands.Representation.CuspidalSupport.BernsteinBlockHomEquivalenceReduction
import Langlands.Representation.Category.GeneratorTensorEvaluation
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Generator.Preadditive

/-! # Renard VI.10.2: the tensor quasi-inverse from the progenerator

The evaluation `ev_τ : Hom_G(Π_Ω, τ) ⊗ Π_Ω → τ`, `α ⊗ w ↦ α(w)`, on the published Bernstein
block, and two conditional reductions of `BernsteinBlockTensorQuasiInverseStatement`. If
`Π_Ω` is a projective generator of the block, then for every object `τ` the evaluation
`Hom(Π_Ω, τ) ⊗[ℤ] Π_Ω → τ` is onto with kernel the balancing span. The VI.10.1 progenerator
statement and the VI.10.2 Hom-equivalence statement each supply these hypotheses; both
remain explicit premises here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.CuspidalSupport

universe uF uV

section Block

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinBlockTensorEvaluationAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinBlockTensorEvaluationTopology :
    TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)
  (s : BernsteinInertialClass.{uF, max uF uV} i ν family)

/-- Renard VI.10.2 (through the proof of VI.4.1), the evaluation `ev_τ`, for objects `P`
and `τ` of the published Bernstein block: the `ℤ`-linear map `(P ⟶ τ) ⊗[ℤ] P → τ`,
`α ⊗ w ↦ α(w)`. Renard's `ev_τ` is defined on the tensor product over `End P`, the quotient
of this one by the balancing span. -/
def bernsteinSaturatedBlockTensorEvaluation
    (P τ : BernsteinSaturatedBlock i ν family s) : (P ⟶ τ) ⊗[ℤ] P.obj →ₗ[ℤ] τ.obj :=
  SmoothRep.fullSubcategoryTensorEvaluation P τ

@[simp]
theorem bernsteinSaturatedBlockTensorEvaluation_tmul
    {P τ : BernsteinSaturatedBlock i ν family s} (α : P ⟶ τ) (w : P.obj) :
    bernsteinSaturatedBlockTensorEvaluation i ν family s P τ (α ⊗ₜ w) =
      SmoothRep.hom α.hom w :=
  SmoothRep.fullSubcategoryTensorEvaluation_tmul α w

/-- For a projective generator `P` of the published Bernstein block, in the
epimorphism-lifting and morphism-separation formulation of the VI.10.1 statement, and for
every object `τ` of the block, the evaluation `(P ⟶ τ) ⊗[ℤ] P → τ`, `α ⊗ w ↦ α(w)`, is
surjective and its kernel is the span of the balancing elements `(r ≫ α) ⊗ w - α ⊗ r(w)`. -/
theorem bernsteinSaturatedBlockTensorEvaluation_surjective_and_ker
    (P : BernsteinSaturatedBlock i ν family s)
    (hproj : ∀ (Y Z : BernsteinSaturatedBlock i ν family s) (q : Y ⟶ Z),
      Epi q → ∀ f : P ⟶ Z, ∃ g : P ⟶ Y, g ≫ q = f)
    (hgen : ∀ (X Y : BernsteinSaturatedBlock i ν family s) (f g : X ⟶ Y),
      f ≠ g → ∃ h : P ⟶ X, h ≫ f ≠ h ≫ g)
    (τ : BernsteinSaturatedBlock i ν family s) :
    Function.Surjective (bernsteinSaturatedBlockTensorEvaluation i ν family s P τ) ∧
      LinearMap.ker (bernsteinSaturatedBlockTensorEvaluation i ν family s P τ) =
        Submodule.span ℤ (Set.range
          (fun p : End P × (P ⟶ τ) × P.obj =>
            (p.1 ≫ p.2.1) ⊗ₜ[ℤ] p.2.2 - p.2.1 ⊗ₜ[ℤ] (SmoothRep.hom p.1.hom p.2.2))) := by
  have : Projective P := ⟨fun {E Y} f e he => hproj E Y e he f⟩
  have hseparator : IsSeparator P := by
    rw [isSeparator_def]
    intro X Y f g h
    by_contra hfg
    obtain ⟨k, hk⟩ := hgen X Y f g hfg
    exact hk (h k)
  exact SmoothRep.fullSubcategoryTensorEvaluation_surjective_and_ker P hseparator τ

/-- Existential packaging of `bernsteinSaturatedBlockTensorEvaluation_surjective_and_ker`,
in the shape of the conclusion of `BernsteinBlockTensorQuasiInverseStatement`. -/
theorem exists_bernsteinSaturatedBlockTensorEvaluation
    (P : BernsteinSaturatedBlock i ν family s)
    (hproj : ∀ (Y Z : BernsteinSaturatedBlock i ν family s) (q : Y ⟶ Z),
      Epi q → ∀ f : P ⟶ Z, ∃ g : P ⟶ Y, g ≫ q = f)
    (hgen : ∀ (X Y : BernsteinSaturatedBlock i ν family s) (f g : X ⟶ Y),
      f ≠ g → ∃ h : P ⟶ X, h ≫ f ≠ h ≫ g)
    (τ : BernsteinSaturatedBlock i ν family s) :
    ∃ ev : (P ⟶ τ) ⊗[ℤ] P.obj →ₗ[ℤ] τ.obj,
      (∀ (α : P ⟶ τ) (w : P.obj), ev (α ⊗ₜ w) = SmoothRep.hom α.hom w) ∧
      Function.Surjective ev ∧
      LinearMap.ker ev = Submodule.span ℤ (Set.range
        (fun p : End P × (P ⟶ τ) × P.obj =>
          (p.1 ≫ p.2.1) ⊗ₜ[ℤ] p.2.2 - p.2.1 ⊗ₜ[ℤ] (SmoothRep.hom p.1.hom p.2.2))) :=
  ⟨bernsteinSaturatedBlockTensorEvaluation i ν family s P τ,
    fun α w => bernsteinSaturatedBlockTensorEvaluation_tmul i ν family s α w,
    bernsteinSaturatedBlockTensorEvaluation_surjective_and_ker i ν family s P hproj hgen τ⟩

/-- If `Hom(P, •)` is an equivalence from the published Bernstein block to right
`End P`-modules, then `P` lifts maps along epimorphisms (an equivalence preserves
epimorphisms) and separates morphisms (an equivalence is faithful). -/
theorem projective_and_generator_of_isEquivalence_preadditiveCoyonedaObj
    (P : BernsteinSaturatedBlock i ν family s)
    (hP : (preadditiveCoyonedaObj P).IsEquivalence) :
    (∀ (Y Z : BernsteinSaturatedBlock i ν family s) (q : Y ⟶ Z),
      Epi q → ∀ f : P ⟶ Z, ∃ g : P ⟶ Y, g ≫ q = f) ∧
    ∀ (X Y : BernsteinSaturatedBlock i ν family s) (f g : X ⟶ Y),
      f ≠ g → ∃ h : P ⟶ X, h ≫ f ≠ h ≫ g := by
  have hprojective : Projective P :=
    (Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj P).2
      (Functor.preservesEpimorphisms_of_adjunction
        (preadditiveCoyonedaObj P).asEquivalence.toAdjunction)
  have hseparator : IsSeparator P :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj P).2 hP.faithful
  refine ⟨fun Y Z q _ f => ⟨Projective.factorThru f q, Projective.factorThru_comp f q⟩, ?_⟩
  intro X Y f g hfg
  by_contra h
  exact hfg ((isSeparator_def P).1 hseparator f g
    (fun k => not_not.1 fun hk => h ⟨k, hk⟩))

end Block

/-- The exact published VI.10.1 progenerator proposition implies the exact published
VI.10.2 tensor quasi-inverse proposition, with the same quantifiers, premises, universes and
block-membership witness. Only the projectivity and generator conjuncts are used. -/
theorem bernsteinBlockTensorQuasiInverse_of_inducedProgenerator
    (hProg : BernsteinInducedProgeneratorStatement.{uF, uV}) :
    BernsteinBlockTensorQuasiInverseStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a ρ₀ hρ₀ j hj
  obtain ⟨hmem, hproj, -, hgen⟩ := hProg F G T i ν family a ρ₀ hρ₀ j hj
  exact ⟨hmem, exists_bernsteinSaturatedBlockTensorEvaluation i ν family
    (bernsteinInertialClass i ν family a) _ hproj hgen⟩

/-- The exact published VI.10.2 Hom-equivalence proposition implies the exact published
VI.10.2 tensor quasi-inverse proposition, with the same quantifiers, premises, universes and
block-membership witness. -/
theorem bernsteinBlockTensorQuasiInverse_of_homEquivalence
    (hThm : BernsteinBlockHomEquivalenceStatement.{uF, uV}) :
    BernsteinBlockTensorQuasiInverseStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a ρ₀ hρ₀ j hj
  obtain ⟨hmem, hequiv⟩ := hThm F G T i ν family a ρ₀ hρ₀ j hj
  obtain ⟨hproj, hgen⟩ := projective_and_generator_of_isEquivalence_preadditiveCoyonedaObj
    i ν family (bernsteinInertialClass i ν family a) _ hequiv
  exact ⟨hmem, exists_bernsteinSaturatedBlockTensorEvaluation i ν family
    (bernsteinInertialClass i ν family a) _ hproj hgen⟩

end Langlands.CuspidalSupport
