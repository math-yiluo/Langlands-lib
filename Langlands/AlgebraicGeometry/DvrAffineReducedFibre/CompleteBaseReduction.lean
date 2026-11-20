import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FibreTests
import Langlands.AlgebraicGeometry.DvrAffineReducedFibreStatement
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Langlands.CommutativeAlgebra.CompleteDvrBaseExtension
import Langlands.CommutativeAlgebra.IntegralClosureTransfer

/-! # Reduction of the affine reduced fibre theorem to a complete base -/

noncomputable section

universe u

open IsLocalRing TensorProduct

namespace Langlands.AlgebraicGeometry

/-- The affine reduced fibre assertion for a complete DVR with algebraically
closed residue field. -/
def DvrAffineReducedFibreCompleteBaseStatement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [IsAdicComplete (maximalIdeal S) S] [IsAlgClosed (ResidueField S)]
    (D : Type u) [CommRing D] [Algebra S D],
    Module.Flat S D → Algebra.FiniteType S D →
      Algebra.Smooth (FractionRing S) (FractionRing S ⊗[S] D) →
    ∃ (T : Type u) (_ : CommRing T) (_ : IsDomain T) (_ : IsDiscreteValuationRing T)
      (_ : Algebra S T),
      Module.FaithfullyFlat S T ∧
        Module.Finite (T ⊗[S] D)
          (integralClosure (T ⊗[S] D) ((T ⊗[S] D) ⊗[T] FractionRing T)) ∧
        ∀ (F : Type u) [Field F] [Algebra T F],
          IsReduced (F ⊗[T]
            integralClosure (T ⊗[S] D) ((T ⊗[S] D) ⊗[T] FractionRing T))

/-- The complete algebraically closed residue case implies the affine reduced
fibre theorem over an arbitrary DVR. -/
theorem dvrAffineReducedFibre_of_completeBase (h : DvrAffineReducedFibreCompleteBaseStatement.{u}) :
    DvrAffineReducedFibreStatement.{u} := by
  intro R _ _ _ A _ _ hFlat hFiniteType hSmooth
  obtain ⟨S, _, _, _, _, hFaithfulS, hCompleteS, hClosedS⟩ :=
    Langlands.CommutativeAlgebra.exists_completeAlgClosedResidueDvrExtension R
  let D := S ⊗[R] A
  have hSmoothD : Algebra.Smooth (FractionRing S) (FractionRing S ⊗[S] D) :=
    DvrAffineReducedFibre.smooth_genericFibre_baseChange
      (A := A) (FaithfulSMul.algebraMap_injective R S)
  obtain ⟨T, _, _, _, _, hFaithfulT, hFiniteT, hReducedT⟩ :=
    h S D inferInstance inferInstance hSmoothD
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let source := T ⊗[S] D
  let target := T ⊗[R] A
  let e : source ≃ₐ[T] target := Algebra.TensorProduct.cancelBaseChange R S T T A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have := isLocalizationAway_fractionRing_of_dvr T (FractionRing T) hπ
  have : IsLocalization.Away (algebraMap T source π) (source ⊗[T] FractionRing T) :=
    IsLocalization.Away.tensor ..
  have : IsLocalization.Away (algebraMap T target π) (target ⊗[T] FractionRing T) :=
    IsLocalization.Away.tensor ..
  obtain ⟨hFinite, hReduced⟩ := Langlands.CommutativeAlgebra.IntegralClosureTransfer.transfer
    (L₂ := target ⊗[T] FractionRing T) (fun _ => rfl) e π hFiniteT hReducedT
  exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.FaithfullyFlat.trans R S T, hFinite, hReduced⟩

end Langlands.AlgebraicGeometry
