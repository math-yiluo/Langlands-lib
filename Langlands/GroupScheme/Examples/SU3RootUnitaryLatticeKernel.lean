import Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralModel
import Langlands.GroupScheme.Examples.SU3RootUnitaryChartKernel

/-! # Special-fibre kernels between the actual ramified unitary lattice models -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SU3Root.IsRamifiedQuadraticValuation

open BilinearCoordinate IntegralModel

variable {O K L : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {ω : AddValuation L (WithTop ℝ)}
  (hω : IsRamifiedQuadraticValuation K L ω)
  (hO : IsValuationIntegers O K ω)

/-- The vector coefficients in the transition from depth `r₂` to depth `r₁`. -/
def transitionVector (r₁ r₂ : ℝ) (i : ULift.{u} (Fin 2)) : O :=
  hω.integralUniformizer hO ^ (vecExponent r₁ r₂ i.down).toNat

omit [IsDomain O] [IsLocalRing O] [IsFractionRing O K] in
/-- The actual lattice transition matrix is diagonal. -/
theorem transitionMatrix_eq_diagonal (r₁ r₂ : ℝ) :
    hω.transitionMatrix hO r₁ r₂ = diagonalMatrix (hω.transitionVector hO r₁ r₂) := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [transitionMatrix, diagonalMatrix, transitionVector]
  · simp [transitionMatrix, diagonalMatrix, hij]

omit [IsDomain O] [IsLocalRing O] [IsFractionRing O K] in
/-- The change between ordered lattice depths is an integral diagonal change of chart. -/
theorem isChartChange_diagonal_transition {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    (hω.latticeChart hO r₂ s₂).data.IsChartChange (hω.latticeChart hO r₁ s₁).data
      (fun i j => algebraMap O K (diagonalMatrix (hω.transitionVector hO r₁ r₂) i j))
      (algebraMap O K (hω.transitionScalar hO r₁ s₁ r₂ s₂)) := by
  simpa only [hω.transitionMatrix_eq_diagonal hO] using
    hω.isChartChange_transition hO hr hs

/-- The actual homomorphism of residue coordinate groups associated with the depth change. -/
abbrev latticeResidueHom {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :=
  (hω.latticeChart hO r₂ s₂).diagonalResidueHom (hω.latticeChart hO r₁ s₁)
    (hω.transitionVector hO r₁ r₂) (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_diagonal_transition hO hr hs)

/-- The special-fibre kernel of every generic-identity extension between the actual lattice
models is the kernel of the reduced diagonal depth transition. -/
def latticeSpecialFibreKernelIso {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (hω.latticeModel hO r₂ s₂).Hom (hω.latticeModel hO r₁ s₁) (𝟙 _)) :
    kernel φ.specialFibreMap ≅ kernel (hω.latticeResidueHom hO hr hs) :=
  (hω.latticeChart hO r₂ s₂).diagonalSpecialFibreKernelIso (hω.latticeChart hO r₁ s₁)
    (hω.transitionVector hO r₁ r₂) (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_diagonal_transition hO hr hs) φ

@[reassoc (attr := simp)]
theorem latticeSpecialFibreKernelIso_hom_ι {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (hω.latticeModel hO r₂ s₂).Hom (hω.latticeModel hO r₁ s₁) (𝟙 _)) :
    (hω.latticeSpecialFibreKernelIso hO hr hs φ).hom ≫
        kernelι (hω.latticeResidueHom hO hr hs) =
      kernelι φ.specialFibreMap ≫
        (baseChangeIso (CommRingCat.ofHom (IsLocalRing.residue O))
          (hω.latticeChart hO r₂ s₂).coeff).hom :=
  (hω.latticeChart hO r₂ s₂).diagonalSpecialFibreKernelIso_hom_ι
    (hω.latticeChart hO r₁ s₁) (hω.transitionVector hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_diagonal_transition hO hr hs) φ

/-- When the scalar transition vanishes in the residue field, its actual kernel is the
bilinear coordinate group on the vanishing vector multipliers, with the scalar retained. -/
def latticeZeroSpecialFibreKernelIso {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (hω.latticeModel hO r₂ s₂).Hom (hω.latticeModel hO r₁ s₁) (𝟙 _))
    (ht : IsLocalRing.residue O (hω.transitionScalar hO r₁ s₁ r₂ s₂) = 0) :
    kernel φ.specialFibreMap ≅
      BilinearCoordinate.groupScheme (CommRingCat.of (IsLocalRing.ResidueField O))
        (kernelCoefficients
          (c := mappedCoefficients (CommRingCat.ofHom (IsLocalRing.residue O))
            (hω.latticeChart hO r₂ s₂).coeff)
          (fun i => IsLocalRing.residue O (hω.transitionVector hO r₁ r₂ i))) :=
  (hω.latticeChart hO r₂ s₂).diagonalZeroSpecialFibreKernelIso
    (hω.latticeChart hO r₁ s₁) (hω.transitionVector hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_diagonal_transition hO hr hs) φ ht

/-- When the scalar transition has nonzero residue, its actual kernel is the vector group
on precisely the vanishing vector multipliers. -/
def latticeNonzeroSpecialFibreKernelIso {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (hω.latticeModel hO r₂ s₂).Hom (hω.latticeModel hO r₁ s₁) (𝟙 _))
    (ht : IsLocalRing.residue O (hω.transitionScalar hO r₁ s₁ r₂ s₂) ≠ 0) :
    kernel φ.specialFibreMap ≅
      VectorGroup.groupScheme (CommRingCat.of (IsLocalRing.ResidueField O))
        (Fintype.card (kernelIndices
          (fun i => IsLocalRing.residue O (hω.transitionVector hO r₁ r₂ i)))) :=
  (hω.latticeChart hO r₂ s₂).diagonalNonzeroSpecialFibreKernelIso
    (hω.latticeChart hO r₁ s₁) (hω.transitionVector hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_diagonal_transition hO hr hs) φ ht

/-- **KP Lemma C.4.4 for the actual ramified unitary lattice models.** Every extension of the
generic identity between coordinatewise ordered depths has a smooth, connected and
unipotent scheme-theoretic special-fibre kernel. -/
theorem lattice_specialFibre_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (hω.latticeModel hO r₂ s₂).Hom (hω.latticeModel hO r₁ s₁) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  (hω.latticeChart hO r₂ s₂).diagonal_specialFibre_kernel_properties
    (hω.latticeChart hO r₁ s₁) (hω.transitionVector hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_diagonal_transition hO hr hs) φ

variable {M N : IntegralModel O K (unitaryParameterGroup K L)}

/-- The kernel comparison is independent of compatible presentations of the lattice models. -/
def latticePresentationKernelIso {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (e : M.Iso (hω.latticeModel hO r₂ s₂) (CategoryTheory.Iso.refl _))
    (d : N.Iso (hω.latticeModel hO r₁ s₁) (CategoryTheory.Iso.refl _))
    (φ : M.Hom N (𝟙 (unitaryParameterGroup K L))) :
    kernel φ.specialFibreMap ≅ kernel (hω.latticeResidueHom hO hr hs) :=
  (hω.latticeChart hO r₂ s₂).diagonalPresentationKernelIso
    (hω.latticeChart hO r₁ s₁) (hω.transitionVector hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_diagonal_transition hO hr hs) e d φ

/-- All three kernel properties hold for every compatible alternative presentation and every
extension of the generic identity between the ordered lattice depths. -/
theorem lattice_presentation_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (e : M.Iso (hω.latticeModel hO r₂ s₂) (CategoryTheory.Iso.refl _))
    (d : N.Iso (hω.latticeModel hO r₁ s₁) (CategoryTheory.Iso.refl _))
    (φ : M.Hom N (𝟙 (unitaryParameterGroup K L))) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  (hω.latticeChart hO r₂ s₂).diagonal_presentation_kernel_properties
    (hω.latticeChart hO r₁ s₁) (hω.transitionVector hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_diagonal_transition hO hr hs) e d φ

end Langlands.GroupScheme.SU3Root.IsRamifiedQuadraticValuation
