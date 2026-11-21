import Langlands.Shimura.PEL.HarrisTaylorCMDvrAction
import Langlands.Shimura.PEL.HarrisTaylorCMDeterminantLocality
import Langlands.AbelianScheme.RationalIsoRelativeDimensionProof
import Langlands.AlgebraicGeometry.AffineStalkModelNeighbourhood
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Reflection of the normalized Harris conditions over a discrete valuation ring -/

noncomputable section

open CategoryTheory AlgebraicGeometry Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra Langlands.AlgebraicGeometry
open Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))

set_option maxHeartbeats 800000 in
private theorem harrisTaylorDeterminant_of_dominant {S T : Scheme.{0}}
    (β : S ⟶ Spec (.of F)) (b : T ⟶ S) [IsSchemeTheoreticallyDominant b] [QuasiCompact b]
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    (h : D.HarrisTaylorCMRationalLieDeterminantCondition C (b ≫ β)
      ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i)) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C β B i := by
  let hΦ := isCMSection_harrisCMSection E (algebraMap L F) τ₀
  let s := D.harrisTaylorReflexStructure C β
  have hdet := (D.harrisTaylorCMRationalLieDeterminantCondition_iff C (b ≫ β)
    ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i)).mp h
  rw [D.harrisTaylorReflexStructure_comp C β b] at hdet
  apply (D.harrisTaylorCMRationalLieDeterminantCondition_iff C β B i).mpr
  intro ι _ a U I _ e W
  change D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a W
  have hW := hdet ι a (b ⁻¹ᵁ U) I (lieBaseChangeChart b B e)
    (Over.mk ((TopologicalSpace.Opens.map b.base).map W.hom))
  unfold HarrisRationalLieDeterminantConditionAt at hW ⊢
  apply MvPolynomial.map_injective (b.app W.left).hom (b.app_injective W.left)
  rw [lieRationalSectionDeterminant_baseChange_of_naturality s b B _
    (lieBaseChangeNaturalityStatements S).1 e a W,
    D.harrisReflexSectionDeterminant_pullback C hΦ s b a W.left]
  exact hW

private theorem hasRelativeDimension_of_field_pullback {S : Scheme.{0}} [ConnectedSpace S]
    {K : Type} [Field K] (b : Spec (.of K) ⟶ S) (B : AbelianScheme S)
    {g : ℕ} (h : ((baseChange b).obj B).HasRelativeDimension g) :
    B.HasRelativeDimension g := by
  let : ConnectedSpace B.X.left :=
    GeometricallyConnected.connectedSpace B.X.hom B.X.hom.isOpenMap
  obtain ⟨m, hm⟩ := smoothConnectedRelativeDimension _ _ B.X.hom B.smooth inferInstance
  let BK := (baseChange b).obj B
  let : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let : ConnectedSpace BK.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton BK.X.hom
  have hmK : BK.HasRelativeDimension m := hasRelativeDimension_baseChange B m hm b
  have he := RationalIsoRelativeDimension.relDim_unique_of_field (K := K) BK.X.hom hmK h
  exact he ▸ hm

set_option maxHeartbeats 800000 in
private theorem normalization_of_dominant_field_pullback {S : Scheme.{0}} [ConnectedSpace S]
    {K : Type} [Field K] (β : S ⟶ Spec (.of F)) (b : Spec (.of K) ⟶ S)
    [IsSchemeTheoreticallyDominant b] [QuasiCompact b]
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    (h : D.HarrisTaylorCMDeterminantDimensionCondition C (b ≫ β)
      ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i)) :
    D.HarrisTaylorCMDeterminantDimensionCondition C β B i :=
  ⟨harrisTaylorDeterminant_of_dominant D C β b B i h.1,
    hasRelativeDimension_of_field_pullback b B h.2⟩

variable {V : Type} [CommRing V] [IsDomain V]
  (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]

local notation "j" => Spec.algebraMap V K

set_option maxHeartbeats 800000 in
/-- The actual normalized determinant and geometric dimension over a domain
are detected on the actual generic fibre. -/
theorem harrisTaylorCMDvrNormalization (β : Spec (.of V) ⟶ Spec (.of F))
    (B : AbelianScheme (Spec (.of V))) (i : A →ₐ[ℚ] End0 B)
    (h : D.HarrisTaylorCMDeterminantDimensionCondition C (j ≫ β)
      ((baseChange j).obj B) ((rationalBaseChangeEnd j B).comp i)) :
    D.HarrisTaylorCMDeterminantDimensionCondition C β B i := by
  have : IsDominant (Spec.algebraMap V K) :=
    isDominant_specMap_of_injective (algebraMap V K) (IsFractionRing.injective V K)
  have : IsSchemeTheoreticallyDominant (Spec.algebraMap V K) :=
    IsSchemeTheoreticallyDominant.of_isDominant (Spec.algebraMap V K)
  have : ConnectedSpace (Spec (.of V)) := inferInstanceAs (ConnectedSpace (PrimeSpectrum V))
  have : QuasiCompact (Spec.algebraMap V K) := inferInstance
  have hnorm := normalization_of_dominant_field_pullback D C (S := Spec (.of V)) (K := K) β
    (Spec.algebraMap V K) B i
  exact hnorm h

variable [IsDiscreteValuationRing V]

set_option maxHeartbeats 800000 in
/-- Extend the rational action on a good model together with the reflected
normalized determinant and dimension conditions. -/
def extendDvrNormalizedAction (β : Spec (.of V) ⟶ Spec (.of F))
    (B : AbelianScheme (Spec (.of V))) (i : A →ₐ[ℚ] End0 ((baseChange j).obj B))
    (h : D.HarrisTaylorCMDeterminantDimensionCondition C (j ≫ β) ((baseChange j).obj B) i) :
    {i₀ : A →ₐ[ℚ] End0 B // D.HarrisTaylorCMDeterminantDimensionCondition C β B i₀} := by
  have hi₀ := rationalBaseChangeEnd_extendDvrRationalAction (V := V) (A := A) K B i
  refine ⟨_, harrisTaylorCMDvrNormalization D C (V := V) K β B
    (extendDvrRationalAction (V := V) (A := A) K B i) ?_⟩
  exact hi₀.symm ▸ h

end Langlands.Shimura.CentralSimpleUnitaryData
