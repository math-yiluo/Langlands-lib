import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Langlands.Global.ArthurNormOneTruncation
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicSiegelReductionStatement
import Langlands.Global.AdelicSiegelFiniteVolume

/-! # Arthur truncation as an orthogonal projection on `L²`

The Hilbert-space extension in the paragraph after Arthur 2005, Proposition 13.1. The
norm-one space is the domain of (13.1) in that section; the extension paragraph also uses
the full quotient as in Lapid 2011. Both use the existing L1 quotient Haar measures. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

/-- A pointwise operator on functions admits an orthogonal projection on `L²` agreeing
with it on all locally bounded measurable square-integrable functions, modulo a.e. equality. -/
def IsOrthogonalL2Extension {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (m : Measure X) (truncate : (X → ℂ) → X → ℂ) : Prop :=
  ∃ A : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m, IsStarProjection A ∧
    ∀ (f : X → ℂ) (hf : MemLp f 2 m), Measurable f →
      (∀ C : Set X, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f x‖ ≤ M) →
      (A (hf.toLp f) : X → ℂ) =ᵐ[m] truncate f

/-- **Arthur 2005, after Proposition 13.1, p.69**, for a suitable maximal compact `K`.
For sufficiently regular truncation parameters, `Λ^T` extends to an orthogonal projection
on the actual norm-one `L²` quotient and on the actual full-adelic `L²` quotient. -/
def TruncationOrthogonalProjectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
    ∃ (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K),
      IsMaximalCompactSubgroup F G K ∧
      (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        AdelicSiegelFactors.IsSiegelAlgebraicSetup F G T i ν T₀ j →
          AdelicSiegelFactors.IsPositiveTorusCompatible F G T i ν T₀ j K) ∧
      ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
        ∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
          IsOrthogonalL2Extension (normOneRationalQuotientHaarMeasure F G)
            (fun f q => normOneTruncation hG hi D hK hρ Tp
              (fun x => f (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x)) q.out) ∧
          IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
            (fun f q => truncation hG hi D hK hρ Tp
              (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out)

end Langlands.Global.ArthurTruncation
