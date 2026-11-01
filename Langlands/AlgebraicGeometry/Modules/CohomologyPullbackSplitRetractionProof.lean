import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCompositionProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackIdentityProof

/-!
# Split retraction for actual relative-cohomology pullback
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- Equal morphisms induce equal pullbacks after the prescribed coefficient
transport. -/
lemma relativeCohomologyPullback_congr (h h' : Y ⟶ X) (w : h = h')
    (M : X.left.Modules) (n : ℕ) :
    relativeCohomologyPullback h M n ≫
        (relativeCohomology Y.hom n).map
          ((Scheme.Modules.pullbackCongr
            (congrArg (fun f : Y ⟶ X => f.left) w)).hom.app M) =
      relativeCohomologyPullback h' M n := by
  subst h'
  simp [Scheme.Modules.pullbackCongr]

/-- A split pair induces the actual cohomological retraction with the
canonical split coefficient isomorphism. -/
lemma relativeCohomologyPullback_split (m : Y ⟶ X) (j : X ⟶ Y)
    (w : j ≫ m = 𝟙 X) (M : X.left.Modules) (n : ℕ) :
    relativeCohomologyPullback m M n ≫
        relativeCohomologyPullback j ((Scheme.Modules.pullback m.left).obj M) n ≫
        (relativeCohomology X.hom n).map
          ((relativeCohomologySplitCoefficientIso m j w).hom.app M) =
      𝟙 _ := by
  simp only [relativeCohomologySplitCoefficientIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.map_comp]
  rw [relativeCohomologyPullback_comp_assoc]
  rw [← Category.assoc, relativeCohomologyPullback_congr (j ≫ m) (𝟙 X) w]
  exact relativeCohomologyPullback_identity M n

/-- The split-retraction law for the published actual cohomology pullback. -/
theorem relativeCohomologyPullbackSplitRetractionStatement :
    RelativeCohomologyPullbackSplitRetractionStatement.{u} := by
  intro R X Y m j w M n
  exact relativeCohomologyPullback_split m j w M n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
