import Langlands.Representation.CuspidalSupport.RationalSummandTensorQuasiInverseStatement
import Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceReduction
import Langlands.Representation.Category.GeneratorTensorEvaluation
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Generator.Preadditive

/-! Renard VI.4.1: the evaluation `ev_E : Hom(Π, τ) ⊗ Π → τ`, `α ⊗ w ↦ α(w)`, of
the proof of the Theorem, on the actual inertia block; and the quasi-inverse
(VI.4.1.4) follows from the Theorem. If `Hom(Π, •)` is an equivalence of the
actual inertia block with right `End Π`-modules, then `Π` is a projective
separator of the block, and the evaluation `Hom(Π, τ) ⊗[ℤ] Π → τ` is onto with
kernel the balancing span. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.CuspidalSupport

universe uF uV

section Block

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSummandTensorQuasiInverseTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- The Serre-class structure of the actual inertia block, as in the published
`rationalInertiaBlockProperty_isSerreClass`, restated under a module-specific
name (see `RationalSummandHomEquivalenceReduction`). -/
local instance rationalSummandTensorQuasiInverseSerreClass
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    (rationalInertiaBlockProperty G π).IsSerreClass :=
  SmoothRep.irreducibleSubquotientsProperty_isSerreClass (IsRationalInertiaRelated G π)

/-- Closure of the actual inertia block under finite products, as in the
published `rationalInertiaBlockProperty_isClosedUnderFiniteProducts`. -/
local instance rationalSummandTensorQuasiInverseFiniteProducts
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    (rationalInertiaBlockProperty G π).IsClosedUnderFiniteProducts :=
  SmoothRep.irreducibleSubquotientsProperty_isClosedUnderFiniteProducts
    (IsRationalInertiaRelated G π)

/-- An object of the actual inertia block whose `Hom` functor is an equivalence
with modules over its endomorphism ring is projective in the block. -/
theorem projective_of_isEquivalence_preadditiveCoyonedaObj
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (P : RationalInertiaBlock G π) (hP : (preadditiveCoyonedaObj P).IsEquivalence) :
    Projective P := by
  have := hP
  exact (Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj P).2
    (Functor.preservesEpimorphisms_of_adjunction
      (preadditiveCoyonedaObj P).asEquivalence.toAdjunction)

/-- An object of the actual inertia block whose `Hom` functor is an equivalence
with modules over its endomorphism ring is a separator of the block. -/
theorem isSeparator_of_isEquivalence_preadditiveCoyonedaObj
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (P : RationalInertiaBlock G π) (hP : (preadditiveCoyonedaObj P).IsEquivalence) :
    IsSeparator P :=
  (isSeparator_iff_faithful_preadditiveCoyonedaObj P).2 hP.faithful

/-- Renard VI.4.1, the evaluation `ev_E` in the proof of the Theorem, for objects `P`
and `τ` of the actual inertia block: the `ℤ`-linear map
`(P ⟶ τ) ⊗[ℤ] P → τ`, `α ⊗ w ↦ α(w)`. Renard's `ev_E` is defined on the tensor
product over `End P`, the quotient of this one by the balancing span. -/
def rationalInertiaBlockTensorEvaluation
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (P τ : RationalInertiaBlock G π) : (P ⟶ τ) ⊗[ℤ] P.obj →ₗ[ℤ] τ.obj :=
  SmoothRep.fullSubcategoryTensorEvaluation P τ

@[simp]
theorem rationalInertiaBlockTensorEvaluation_tmul
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    {P τ : RationalInertiaBlock G π} (α : P ⟶ τ) (w : P.obj) :
    rationalInertiaBlockTensorEvaluation G π P τ (α ⊗ₜ w) = SmoothRep.hom α.hom w :=
  SmoothRep.fullSubcategoryTensorEvaluation_tmul α w

/-- VI.4.1.4, objectwise: if `Hom(P, •)` is an equivalence from the actual
inertia block to right `End P`-modules, then for every object `τ` of the block
the evaluation `(P ⟶ τ) ⊗[ℤ] P → τ`, `α ⊗ w ↦ α(w)`, is surjective and its kernel
is the span of the balancing elements `(r ≫ α) ⊗ w - α ⊗ r(w)`. -/
theorem rationalInertiaBlockTensorEvaluation_surjective_and_ker
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (P : RationalInertiaBlock G π) (hP : (preadditiveCoyonedaObj P).IsEquivalence)
    (τ : RationalInertiaBlock G π) :
    Function.Surjective (rationalInertiaBlockTensorEvaluation G π P τ) ∧
      LinearMap.ker (rationalInertiaBlockTensorEvaluation G π P τ) =
        Submodule.span ℤ (Set.range
          (fun p : End P × (P ⟶ τ) × P.obj =>
            (p.1 ≫ p.2.1) ⊗ₜ[ℤ] p.2.2 - p.2.1 ⊗ₜ[ℤ] (SmoothRep.hom p.1.hom p.2.2))) := by
  have := projective_of_isEquivalence_preadditiveCoyonedaObj G π P hP
  exact SmoothRep.fullSubcategoryTensorEvaluation_surjective_and_ker P
    (isSeparator_of_isEquivalence_preadditiveCoyonedaObj G π P hP) τ

/-- Existential packaging of `rationalInertiaBlockTensorEvaluation_surjective_and_ker`,
in the shape of the conclusion of `RationalSummandTensorQuasiInverseStatement`. -/
theorem exists_tensorEvaluation_of_isEquivalence_preadditiveCoyonedaObj
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (P : RationalInertiaBlock G π) (hP : (preadditiveCoyonedaObj P).IsEquivalence)
    (τ : RationalInertiaBlock G π) :
    ∃ ev : (P ⟶ τ) ⊗[ℤ] P.obj →ₗ[ℤ] τ.obj,
      (∀ (α : P ⟶ τ) (w : P.obj), ev (α ⊗ₜ w) = SmoothRep.hom α.hom w) ∧
      Function.Surjective ev ∧
      LinearMap.ker ev = Submodule.span ℤ (Set.range
        (fun p : End P × (P ⟶ τ) × P.obj =>
          (p.1 ≫ p.2.1) ⊗ₜ[ℤ] p.2.2 - p.2.1 ⊗ₜ[ℤ] (SmoothRep.hom p.1.hom p.2.2))) :=
  ⟨rationalInertiaBlockTensorEvaluation G π P τ,
    fun α w => rationalInertiaBlockTensorEvaluation_tmul G π α w,
    rationalInertiaBlockTensorEvaluation_surjective_and_ker G π P hP τ⟩

end Block

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- The Theorem of Renard VI.4.1 implies its quasi-inverse statement (VI.4.1.4),
with the same quantifiers, premises and universes. -/
theorem rationalSummandTensorQuasiInverse_of_homEquivalence
    (hThm : RationalSummandHomEquivalenceStatement.{uF, uV}) :
    RationalSummandTensorQuasiInverseStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  obtain ⟨hmem, hequiv⟩ := hThm F G hG T i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ j hj
  refine ⟨hmem, ?_⟩
  intro P τ
  exact exists_tensorEvaluation_of_isEquivalence_preadditiveCoyonedaObj G _ P hequiv τ

/-- The Proposition of Renard VI.4.1 implies the quasi-inverse statement
(VI.4.1.4), through the Theorem. -/
theorem rationalSummandTensorQuasiInverse_of_smallProgenerator
    (hProp : RationalSummandSmallProgeneratorStatement.{uF, uV}) :
    RationalSummandTensorQuasiInverseStatement.{uF, uV} :=
  rationalSummandTensorQuasiInverse_of_homEquivalence
    (rationalSummandHomEquivalence_of_smallProgenerator hProp)

end Langlands.CuspidalSupport
