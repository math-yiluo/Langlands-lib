import Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Renard VI.4.1, the quasi-inverse `G_Π : M ↦ M ⊗_R V_Π` (VI.4.1.4) of the
Hom functor `F_Π = Hom_G(Π, ·)` (VI.4.1.3): for every `τ` in the block, the
evaluation map `Hom_G(Π, τ) ⊗_R V_Π → τ`, `α ⊗ w ↦ α(w)`, is bijective. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- VI.4.1, Theorem, the quasi-inverse (VI.4.1.4). In the setting of the published
VI.4.1 Theorem `RationalSummandHomEquivalenceStatement`, the compact induction
`Π = ind_{⁰G}^G ρ` lies in the inertia block, and for every object `τ` of the block
the evaluation map from the balanced tensor `Hom_G(Π, τ) ⊗_R V_Π`, `R = End(Π)`, to the
space of `τ` is bijective. The balanced tensor is the quotient of `Hom_G(Π, τ) ⊗[ℤ] V_Π`
by the span of `(r ≫ α) ⊗ w − α ⊗ r(w)`; the statement says that the `ℤ`-linear
evaluation `α ⊗ w ↦ α(w)` is surjective with exactly this kernel. -/
def RationalSummandTensorQuasiInverseStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
        π.IsIrreducible →
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π →
        ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
          ρ.IsIrreducible →
          ∀ j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π,
            Function.Injective (SmoothRep.hom j) →
            ∃ hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
                ((Induction.compactInductionFunctor (rationalCommonNormKernel G)).obj
                  (SmoothRep.toRep.obj ρ)),
              let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) := ⟨_, hmem⟩
              ∀ τ : RationalInertiaBlock G (rationalInertiaBaseLift G π),
                ∃ ev : (P ⟶ τ) ⊗[ℤ] P.obj →ₗ[ℤ] τ.obj,
                  (∀ (α : P ⟶ τ) (w : P.obj), ev (α ⊗ₜ w) = SmoothRep.hom α.hom w) ∧
                  Function.Surjective ev ∧
                  LinearMap.ker ev = Submodule.span ℤ (Set.range
                    (fun p : End P × (P ⟶ τ) × P.obj =>
                      (p.1 ≫ p.2.1) ⊗ₜ[ℤ] p.2.2 - p.2.1 ⊗ₜ[ℤ] (SmoothRep.hom p.1.hom p.2.2)))

end Langlands.CuspidalSupport
