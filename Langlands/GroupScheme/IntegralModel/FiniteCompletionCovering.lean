import Langlands.GroupScheme.IntegralParabolicCovering
import Langlands.GroupScheme.IntegralModel.CoefficientPoints
import Langlands.ClassField.Global.LocalUnitPowers

/-! # Parabolic-left integral coverings at finite completions of number fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralParabolicCovering

open Langlands.Global Langlands.GroupScheme.GaloisPointComparison
open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

section Completion

variable {G P : GroupScheme (Spec (CommRingCat.of (FiniteCompletion F v)))} {f : P ⟶ G}
  (M : IntegralModel (v.adicCompletionIntegers F) (FiniteCompletion F v) G)
  (N : IntegralModel (v.adicCompletionIntegers F) (FiniteCompletion F v) P) (φ : N.Hom M f)
  {Q : Over (Spec (CommRingCat.of (v.adicCompletionIntegers F)))} (q : M.group.X ⟶ Q)
  [Mono φ.hom.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  [IsProper Q.hom]

/-- The parabolic-left integral covering over the completed integers at a finite place. -/
theorem finiteCompletion_range_mul_integralPoints_eq_univ
    (hsmooth : N.IsSmooth) (hconn : N.HasConnectedSpecialFibre)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of (v.adicCompletionIntegers F))))
      (g h : T ⟶ M.group.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range φ.hom).carrier T) :
    Set.range (rationalPoints.map f) *
      (M.integralPoints : Set (rationalPoints G)) = Set.univ := by
  have := Langlands.ClassField.Global.isAdicComplete_adicCompletionIntegers v
  exact range_mul_integralPoints_eq_univ M N φ q hsmooth hconn hfib

end Completion

section Coefficient

variable {G P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G)
  (M : IntegralModel (v.adicCompletionIntegers F) (FiniteCompletion F v)
    (baseChanged F (FiniteCompletion F v) G))
  (N : IntegralModel (v.adicCompletionIntegers F) (FiniteCompletion F v)
    (baseChanged F (FiniteCompletion F v) P))
  (φ : N.Hom M ((GroupScheme.baseChange (baseMap F (FiniteCompletion F v))).map p))
  {Q : Over (Spec (CommRingCat.of (v.adicCompletionIntegers F)))} (q : M.group.X ⟶ Q)
  [Mono φ.hom.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  [IsProper Q.hom]

/-- The literal parabolic-left product on the original group's completion points. -/
theorem finiteCompletion_coefficientIntegralPoints_covering
    (hsmooth : N.IsSmooth) (hconn : N.HasConnectedSpecialFibre)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of (v.adicCompletionIntegers F))))
      (g h : T ⟶ M.group.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range φ.hom).carrier T) :
    Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) *
      (M.coefficientIntegralPoints F (FiniteCompletion F v) : Set _) = Set.univ :=
  IntegralModel.coefficientIntegralPoints_covering F (FiniteCompletion F v) M p
    (finiteCompletion_range_mul_integralPoints_eq_univ v M N φ q hsmooth hconn hfib)

/-- Every completion point is a parabolic completion point times a transported integral point. -/
theorem finiteCompletion_exists_factor
    (hsmooth : N.IsSmooth) (hconn : N.HasConnectedSpecialFibre)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of (v.adicCompletionIntegers F))))
      (g h : T ⟶ M.group.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range φ.hom).carrier T)
    (g : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :
    ∃ hk : P.affinePoints (CommAlgCat.of F (FiniteCompletion F v)) ×
        M.coefficientIntegralPoints F (FiniteCompletion F v),
      P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v)) hk.1 * hk.2 = g := by
  have hg : g ∈ Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) *
      (M.coefficientIntegralPoints F (FiniteCompletion F v) : Set _) := by
    rw [finiteCompletion_coefficientIntegralPoints_covering v p M N φ q hsmooth hconn hfib]
    trivial
  obtain ⟨_, ⟨h, rfl⟩, k, hk, hhk⟩ := hg
  exact ⟨(h, ⟨k, hk⟩), hhk⟩

/-- A chosen parabolic-left factorization of a completion point of the original group. -/
def finiteCompletionParabolicIntegralFactor
    (hsmooth : N.IsSmooth) (hconn : N.HasConnectedSpecialFibre)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of (v.adicCompletionIntegers F))))
      (g h : T ⟶ M.group.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range φ.hom).carrier T)
    (g : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :
    P.affinePoints (CommAlgCat.of F (FiniteCompletion F v)) ×
      M.coefficientIntegralPoints F (FiniteCompletion F v) :=
  (finiteCompletion_exists_factor v p M N φ q hsmooth hconn hfib g).choose

/-- The chosen completion-point factors multiply back to the given point. -/
theorem finiteCompletionParabolicIntegralFactor_spec
    (hsmooth : N.IsSmooth) (hconn : N.HasConnectedSpecialFibre)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of (v.adicCompletionIntegers F))))
      (g h : T ⟶ M.group.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range φ.hom).carrier T)
    (g : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :
    P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))
        (finiteCompletionParabolicIntegralFactor v p M N φ q hsmooth hconn hfib g).1 *
      (finiteCompletionParabolicIntegralFactor v p M N φ q hsmooth hconn hfib g).2 = g :=
  (finiteCompletion_exists_factor v p M N φ q hsmooth hconn hfib g).choose_spec

end Coefficient

end Langlands.GroupScheme.IntegralParabolicCovering
