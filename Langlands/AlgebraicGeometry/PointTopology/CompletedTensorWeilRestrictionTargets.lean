import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionCoefficientIso
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionProduct
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof

/-! # Actual upper-place targets of the completed-tensor Weil decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section General

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
variable {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  (e : C ⊗[A] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[A] b) i = algebraMap B (D i) b)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

include he in
/-- The tensor decomposition's original right-factor law identifies the
actual composite spectrum map to each factor with its given `B`-structure. -/
@[reassoc (attr := simp)]
theorem tensorCoefficientSpecFactor_comp (i : ι) :
    finiteProductSpecProjection D i ≫
        (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom ≫
        Spec.algebraMap B (C ⊗[A] B) =
      Spec.algebraMap B (D i) := by
  change Spec.map (CommRingCat.ofHom (Pi.evalRingHom D i)) ≫
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B))) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun b => he b i)

/-- The actual factor target after tensor base change and coefficient
transport, before identifying it with the usual base change of `Y`. -/
abbrev tensorCoefficientFactorTarget
    (Y : Over (Spec (CommRingCat.of B))) (i : ι) :
    Over (Spec (CommRingCat.of (D i))) :=
  finiteProductFactorScheme D
    (weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e
      (ringBaseChange B (C ⊗[A] B) Y)) i

/-- The actual three successive pullbacks of `Y` identify canonically
with its ordinary base change to the factor ring. -/
def tensorCoefficientFactorTargetIso
    (Y : Over (Spec (CommRingCat.of B))) (i : ι) :
    tensorCoefficientFactorTarget A B C D e Y i ≅ ringBaseChange B (D i) Y :=
  Over.isoMk
    ((pullbackLeftPullbackSndIso (ringBaseChange B (C ⊗[A] B) Y).hom
        (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom
        (finiteProductSpecProjection D i)).trans
      ((pullbackLeftPullbackSndIso Y.hom (Spec.algebraMap B (C ⊗[A] B))
          (finiteProductSpecProjection D i ≫
            (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom)).trans
        (pullback.congrHom rfl
          (by simpa only [Category.assoc] using
            tensorCoefficientSpecFactor_comp A B C D e he i))))
    (by simp [tensorCoefficientFactorTarget, finiteProductFactorScheme,
      weilCoefficientTarget, ringBaseChange, pullback.congrHom])

/-- The target identification retains the original three projections to
`Y`, fixing its underlying map without any choice of an isomorphism. -/
@[reassoc (attr := simp)]
theorem tensorCoefficientFactorTargetIso_hom_fst
    (Y : Over (Spec (CommRingCat.of B))) (i : ι) :
    (tensorCoefficientFactorTargetIso A B C D e he Y i).hom.left ≫
        pullback.fst Y.hom (Spec.algebraMap B (D i)) =
      pullback.fst
          (weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e
            (ringBaseChange B (C ⊗[A] B) Y)).hom
          (finiteProductSpecProjection D i) ≫
        pullback.fst (ringBaseChange B (C ⊗[A] B) Y).hom
          (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom ≫
        pullback.fst Y.hom (Spec.algebraMap B (C ⊗[A] B)) := by
  simp [tensorCoefficientFactorTargetIso, ringBaseChange, pullback.congrHom,
    Category.assoc]

end General

section NumberFields

open NumberField IsDedekindDomain
open Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension InfiniteExtension NumberField.LiesOver

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- The actual completed tensor decomposition at a finite number-field
place, using the published bijectivity theorem without an extra hypothesis. -/
def finitePlaceTensorEquiv (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ((q : FinitePlacesAbove L v) → q.1.adicCompletion L) :=
  AlgEquiv.ofBijective (finiteTensorMap v) ((completedTensorComparison K L).1 v)

@[simp]
theorem finitePlaceTensorEquiv_apply (v : HeightOneSpectrum (𝓞 K))
    (z : v.adicCompletion K ⊗[K] L) :
    finitePlaceTensorEquiv K L v z = finiteTensorMap v z := rfl

/-- Every finite upper-place component has the original `L`-structure map. -/
@[simp]
theorem finitePlaceTensorEquiv_one_tmul (v : HeightOneSpectrum (𝓞 K))
    (y : L) (q : FinitePlacesAbove L v) :
    finitePlaceTensorEquiv K L v (1 ⊗ₜ[K] y) q =
      algebraMap L (q.1.adicCompletion L) y :=
  finiteTensorMap_one_tmul v y q

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- For all finite places above `v`, the actual tensor/product target is
the original scheme base changed along its actual completion embedding. -/
def finitePlaceWeilRestrictionFactorTargetIso
    (v : HeightOneSpectrum (𝓞 K)) (Y : Over (Spec (CommRingCat.of L)))
    (q : FinitePlacesAbove L v) :
    tensorCoefficientFactorTarget K L (v.adicCompletion K)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
        (finitePlaceTensorEquiv K L v) Y q ≅
      ringBaseChange L (q.1.adicCompletion L) Y :=
  tensorCoefficientFactorTargetIso K L (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (finitePlaceTensorEquiv K L v) (finitePlaceTensorEquiv_one_tmul K L v) Y q

/-- For all infinite places above `v`, the actual tensor/product target is
the original scheme base changed along its actual completion embedding. -/
def infinitePlaceWeilRestrictionFactorTargetIso
    (v : InfinitePlace K) (Y : Over (Spec (CommRingCat.of L)))
    (q : InfinitePlacesAbove L v) :
    tensorCoefficientFactorTarget K L v.Completion
        (fun q : InfinitePlacesAbove L v => q.1.Completion)
        (infiniteTensorEquiv v) Y q ≅
      ringBaseChange L q.1.Completion Y :=
  tensorCoefficientFactorTargetIso K L v.Completion
    (fun q : InfinitePlacesAbove L v => q.1.Completion)
    (infiniteTensorEquiv v) (infiniteTensorMap_one_tmul v) Y q

end NumberFields

end Langlands.AlgebraicGeometry.PointTopology
