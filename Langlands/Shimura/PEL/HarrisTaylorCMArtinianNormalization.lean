import Langlands.Shimura.PEL.HarrisTaylorCMArtinianDeterminantReflection
import Langlands.AbelianScheme.RationalIsoRelativeDimensionProof

/-! # Reflection of the normalized joint condition on an equivariant Artinian lift -/

noncomputable section

open CategoryTheory AlgebraicGeometry Langlands.AbelianScheme
open IsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

private theorem hasRelativeDimension_of_artinianPullback
    {R R₀ : Type} [CommRing R] [CommRing R₀] [IsLocalRing R] [IsLocalRing R₀]
    [IsArtinianRing R] {B : AbelianScheme (Spec (.of R))} (g : ℕ) (φ : R →+* R₀)
    (h : ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj B).HasRelativeDimension g) :
    B.HasRelativeDimension g := by
  let : Subsingleton (Spec (CommRingCat.of R)) := inferInstanceAs (Subsingleton (PrimeSpectrum R))
  let : ConnectedSpace B.X.left := GeometricallyConnected.connectedSpace_of_subsingleton B.X.hom
  obtain ⟨m, hm⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    _ _ B.X.hom B.smooth inferInstance
  let q := Spec.map (CommRingCat.ofHom (residue R₀))
  let B₀ := (baseChange (Spec.map (CommRingCat.ofHom φ))).obj B
  let A₀ := (baseChange q).obj B₀
  have hmg : A₀.HasRelativeDimension m :=
    hasRelativeDimension_baseChange B₀ m (hasRelativeDimension_baseChange B m hm _) q
  have hgg : A₀.HasRelativeDimension g := hasRelativeDimension_baseChange B₀ g h q
  let : ConnectedSpace A₀.X.left := GeometricallyConnected.connectedSpace_of_subsingleton A₀.X.hom
  have eq := RationalIsoRelativeDimension.relDim_unique_of_field A₀.X.hom hmg hgg
  exact eq ▸ hm

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

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

open Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

/-- A rational equivariant comparison to the reduction is enough to certify
both normalized conditions on the actual thicker representative. -/
def HarrisTaylorCMArtinianNormalizationStatement : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R] [IsLocalRing R₀]
    [IsArtinianRing R] [IsArtinianRing R₀] (φ : R →+* R₀), Function.Surjective φ →
    ∀ (β : Spec (.of R) ⟶ Spec (.of F))
      (X : RationalAlgebraAction (Spec (.of R)) A) (Y : RationalAlgebraAction (Spec (.of R₀)) A),
      let b := Spec.map (CommRingCat.ofHom φ)
      Nonempty ((RationalAlgebraAction.pullback b).obj X ≅ Y) →
      D.HarrisTaylorCMDeterminantDimensionCondition C (b ≫ β) Y.abelianScheme Y.action →
      D.HarrisTaylorCMDeterminantDimensionCondition C β X.abelianScheme X.action

/-- The determinant and the dimension both reflect along the original Artinian test. -/
theorem harrisTaylorCMArtinianNormalization :
    D.HarrisTaylorCMArtinianNormalizationStatement C := by
  intro R R₀ _ _ _ _ _ _ φ hφ β X Y b he hY
  obtain ⟨e⟩ := he
  have hclass := RationalAlgebraAction.classOf_eq_iff.mpr (Nonempty.intro e)
  have hdet : D.HarrisTaylorCMDeterminantPullbackCondition C β X.abelianScheme X.action b := by
    change D.HarrisTaylorCMDeterminantClassCondition C (b ≫ β)
      (RationalAlgebraAction.classOf ((RationalAlgebraAction.pullback b).obj X))
    rw [hclass]
    exact (D.harrisTaylorCMDeterminantClassCondition_classOf C (b ≫ β) Y).mpr hY.1
  refine ⟨D.harrisTaylorCMArtinianDeterminantReflection C R R₀ φ hφ β
    X.abelianScheme X.action hdet, ?_⟩
  let g := Module.finrank ℚ E * n ^ 2
  have hdim : ((baseChange b).obj X.abelianScheme).HasRelativeDimension g :=
    (rationalIsoRelativeDimension _ _ _ (RationalAlgebraAction.underlyingIso e) g).mpr hY.2
  exact hasRelativeDimension_of_artinianPullback g φ hdim

end Langlands.Shimura.CentralSimpleUnitaryData
