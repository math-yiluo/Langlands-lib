import Langlands.Automorphic.HilbertPlaceRealization
import Langlands.Representation.Archimedean.GeneralLinear

/-! # Irreducible Hilbert closures for real and complex place operators -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct

namespace Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion

open Langlands.Global ArchimedeanGL RankinSelbergGlobal Langlands.Archimedean
open HilbertCoefficientComparison
universe u uV uX
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem continuous_toUnits {𝕜 : Type} [RCLike 𝕜] (n : ℕ) :
    Continuous (Unitary.toUnits : Matrix.unitaryGroup (Fin n) 𝕜 →
      (Matrix (Fin n) (Fin n) 𝕜)ˣ) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, (continuous_star.comp continuous_subtype_val).congr fun _ => rfl⟩

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX}
  {ρ : Representation ℂ (FiniteAdelicGL F n) V}
  {κ : Representation ℂ (standardInfiniteCompact F n) V} {D : X → Module.End ℂ V}
  {b : OperatorUnitaryFormCore ρ κ D} (B : AdelicCompletion b)

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ

variable (hcont : IsContinuousRepresentation B.action)
  (hinner : ∀ g (x y : b.HilbertCompletion), Inner.inner ℂ (B.action g x) (B.action g y) = Inner.inner ℂ x y)
  (hs : ∀ v, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n)
    (B.action.comp (OperatorDeterminantSlice.infiniteCoordinateInclusion F n)) (b.toHilbert v))

include hcont hinner hs in
/-- At a real place the actual restriction of a completion realizes each
irreducible admissible subspace on its invariant Hilbert closure. -/
theorem realPlaceHilbertRealization (w : RP)
    (d : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hd : ∀ Y : RM, ∀ v, B.differential
      (envelopingGenerator F n (complexify F n (realPlaceLieInclusion F n w Y))) v = d (1 ⊗ₜ[ℝ] Y) v)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector (κ.comp (realPlaceCompactInclusion F n w).toMonoidHom) v)
    (W : Submodule ℂ V)
    (hirr : PlaceComponent.IsIrreducible (κ.comp (realPlaceCompactInclusion F n w).toMonoidHom) d W)
    (hadm : PlaceComponent.IsAdmissible (κ.comp (realPlaceCompactInclusion F n w).toMonoidHom) W) :
    IsPlaceHilbertRealization (placeAction B.action (realPlaceGL F n w)) b.toHilbert
      (Unitary.toUnits : RK →* RMˣ) (κ.comp (realPlaceCompactInclusion F n w).toMonoidHom) d
      (B.realPlaceClosureCompatibility w d hd) W hirr.2.1 := by
  let : MeasurableSpace RK := borel RK
  let : BorelSpace RK := ⟨rfl⟩
  have hι := contMDiff_realPlaceGL w (n := n)
  have hs' v := isSmoothVector_placeAction B.action (realPlaceGL F n w) hι (hs v)
  have hD := placeAction_realGeneratorCompatibility B.action (realPlaceGL F n w) b.toHilbert
    B.differential B.coefficients (realPlaceMatrix w) (realPlaceLieInclusion F n w)
    (fun g => (realPlaceGL_val w g).symm)
    (fun f => analyticAt_realPlaceRestriction w (coordinateExtension F n f))
    (fderiv_realPlaceRestriction w) hs'
  exact isPlaceHilbertRealization_of_ambient _ _ _ _ _ (B.realPlaceClosureCompatibility w d hd) W hirr.2.1
    (continuous_toUnits n) b.toHilbert_injective
    (isContinuousRepresentation_placeAction B.action _ hι.continuous hcont)
    (fun _ => hinner _) hfin hs'
    (fun Y v => (congrArg b.toHilbert (hd Y v)).symm.trans (hD Y v)) hirr hadm

include hcont hinner hs in
/-- At a complex place the comparison uses smooth real orbits and both real
matrix directions in the complexified Lie algebra. -/
theorem complexPlaceHilbertRealization (w : CP)
    (d : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hd : ∀ Y : CM, ∀ v, B.differential
      (envelopingGenerator F n (complexify F n (complexPlaceLieInclusion F n w Y))) v = d (1 ⊗ₜ[ℝ] Y) v)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector (κ.comp (complexPlaceCompactInclusion F n w).toMonoidHom) v)
    (W : Submodule ℂ V)
    (hirr : PlaceComponent.IsIrreducible (κ.comp (complexPlaceCompactInclusion F n w).toMonoidHom) d W)
    (hadm : PlaceComponent.IsAdmissible (κ.comp (complexPlaceCompactInclusion F n w).toMonoidHom) W) :
    IsPlaceHilbertRealization (placeAction B.action (complexPlaceGL F n w)) b.toHilbert
      (Unitary.toUnits : CK →* CMˣ) (κ.comp (complexPlaceCompactInclusion F n w).toMonoidHom) d
      (B.complexPlaceClosureCompatibility w d hd) W hirr.2.1 := by
  let : MeasurableSpace CK := borel CK
  let : BorelSpace CK := ⟨rfl⟩
  have hι := contMDiff_complexPlaceGL w (n := n)
  have hs' v := isSmoothVector_placeAction B.action (complexPlaceGL F n w) hι (hs v)
  have hD := placeAction_realGeneratorCompatibility B.action (complexPlaceGL F n w) b.toHilbert
    B.differential B.coefficients (complexPlaceMatrix w) (complexPlaceLieInclusion F n w)
    (fun g => (complexPlaceGL_val w g).symm)
    (fun f => analyticAt_complexPlaceRestriction w (coordinateExtension F n f))
    (fderiv_complexPlaceRestriction w) hs'
  exact isPlaceHilbertRealization_of_ambient _ _ _ _ _ (B.complexPlaceClosureCompatibility w d hd) W hirr.2.1
    (continuous_toUnits n) b.toHilbert_injective
    (isContinuousRepresentation_placeAction B.action _ hι.continuous hcont)
    (fun _ => hinner _) hfin hs'
    (fun Y v => (congrArg b.toHilbert (hd Y v)).symm.trans (hD Y v)) hirr hadm

/-- Every irreducible admissible algebraic component at the real place is
realized by the restricted group action on the closure of its image. -/
def SupportsRealPlaceHilbertRealization (w : RP)
    (d : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  let κw := κ.comp (realPlaceCompactInclusion F n w).toMonoidHom
  ∀ W : Submodule ℂ V, PlaceComponent.IsIrreducible κw d W →
    PlaceComponent.IsAdmissible κw W →
    HasPlaceHilbertRealization (placeAction B.action (realPlaceGL F n w)) b.toHilbert
      (Unitary.toUnits : RK →* RMˣ) κw d W

/-- The corresponding realization property at the complex place. -/
def SupportsComplexPlaceHilbertRealization (w : CP)
    (d : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  let κw := κ.comp (complexPlaceCompactInclusion F n w).toMonoidHom
  ∀ W : Submodule ℂ V, PlaceComponent.IsIrreducible κw d W →
    PlaceComponent.IsAdmissible κw W →
    HasPlaceHilbertRealization (placeAction B.action (complexPlaceGL F n w)) b.toHilbert
      (Unitary.toUnits : CK →* CMˣ) κw d W

include hcont hinner hs in
theorem supportsRealPlaceHilbertRealization (w : RP)
    (d : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hd : ∀ Y : RM, ∀ v, B.differential
      (envelopingGenerator F n (complexify F n (realPlaceLieInclusion F n w Y))) v = d (1 ⊗ₜ[ℝ] Y) v)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector (κ.comp (realPlaceCompactInclusion F n w).toMonoidHom) v) :
    B.SupportsRealPlaceHilbertRealization w d := by
  intro W hirr hadm
  exact ⟨B.realPlaceClosureCompatibility w d hd, hirr.2.1,
    B.realPlaceHilbertRealization hcont hinner hs w d hd hfin W hirr hadm⟩

include hcont hinner hs in
theorem supportsComplexPlaceHilbertRealization (w : CP)
    (d : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hd : ∀ Y : CM, ∀ v, B.differential
      (envelopingGenerator F n (complexify F n (complexPlaceLieInclusion F n w Y))) v = d (1 ⊗ₜ[ℝ] Y) v)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector (κ.comp (complexPlaceCompactInclusion F n w).toMonoidHom) v) :
    B.SupportsComplexPlaceHilbertRealization w d := by
  intro W hirr hadm
  exact ⟨B.complexPlaceClosureCompatibility w d hd, hirr.2.1,
    B.complexPlaceHilbertRealization hcont hinner hs w d hd hfin W hirr hadm⟩

end Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion
