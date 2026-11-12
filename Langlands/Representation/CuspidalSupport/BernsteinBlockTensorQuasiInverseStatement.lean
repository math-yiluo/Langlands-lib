import Langlands.Representation.CuspidalSupport.BernsteinBlockHomEquivalenceStatement
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # The tensor quasi-inverse of the Bernstein block equivalence (Renard VI.10.2, Theorem)

For the induced progenerator `Π_Ω` of a Bernstein block `M(G)_Ω` (VI.10.1) and
`R_Ω = End_G(Π_Ω)`, the functor `G_{Π_Ω} : M ↦ M ⊗_{R_Ω} Π_Ω` is quasi-inverse to
`F_{Π_Ω} = Hom_G(Π_Ω, ·)`: for every object `τ` of the block, the evaluation map
`Hom_G(Π_Ω, τ) ⊗_{R_Ω} Π_Ω → τ` is bijective.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.10.2, Theorem, the quasi-inverse `G_{Π_Ω} : M ↦ M ⊗_{R_Ω} Π_Ω`. In the setting
of the published `BernsteinBlockHomEquivalenceStatement`, `Π_Ω` lies in the Bernstein block
of the inertial class of `a`, and for every object `τ` of the block the evaluation map from
the balanced tensor `Hom_G(Π_Ω, τ) ⊗_{R_Ω} Π_Ω` to the space of `τ` is bijective. The balanced
tensor is the quotient of `Hom_G(Π_Ω, τ) ⊗[ℤ] Π_Ω` by the span of `(r ≫ α) ⊗ w − α ⊗ r(w)`;
the statement says that the `ℤ`-linear evaluation `α ⊗ w ↦ α(w)` is surjective with exactly
this kernel. -/
def BernsteinBlockTensorQuasiInverseStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
      haveI : IsClosedImmersion (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
        Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
      haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
        isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
      haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
        rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
        infer_instance
      letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
        rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
      ∀ ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
          (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)),
        ρ₀.IsIrreducible →
        ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup
            (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots))
            a.representation,
          Function.Injective (SmoothRep.hom j) →
          let piOmega : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
            (normalizedInductionFunctor (family.decomposition a.roots)
              (family.closedUnipotent a.roots)).obj
                (bernsteinLiteralLeviRep i ν a.roots
                  (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))
          ∃ hmem : bernsteinSaturatedBlockProperty i ν family
              (bernsteinInertialClass i ν family a) piOmega,
            let P : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a) :=
              ⟨piOmega, hmem⟩
            ∀ τ : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a),
              ∃ ev : (P ⟶ τ) ⊗[ℤ] P.obj →ₗ[ℤ] τ.obj,
                (∀ (α : P ⟶ τ) (w : P.obj), ev (α ⊗ₜ w) = SmoothRep.hom α.hom w) ∧
                Function.Surjective ev ∧
                LinearMap.ker ev = Submodule.span ℤ (Set.range
                  (fun p : End P × (P ⟶ τ) × P.obj =>
                    (p.1 ≫ p.2.1) ⊗ₜ[ℤ] p.2.2 - p.2.1 ⊗ₜ[ℤ] (SmoothRep.hom p.1.hom p.2.2)))

end Langlands.CuspidalSupport
