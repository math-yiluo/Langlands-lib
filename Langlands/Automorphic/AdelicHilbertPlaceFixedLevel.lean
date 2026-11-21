import Langlands.Automorphic.HilbertPlaceRealizationData
import Langlands.Automorphic.HilbertPlaceFixedLevel
import Langlands.Global.ArchimedeanPlaceSplitting
import Langlands.Representation.Archimedean.UnitaryCompactAdmissibility

/-! # Fixed-level smooth place embeddings for an adelic Hilbert completion -/

noncomputable section
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000
set_option Elab.async false

namespace Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion

open Langlands.Archimedean SmoothInvariantSubspace
open Langlands.Global ArchimedeanGL RankinSelbergGlobal OperatorDeterminantSlice
open HilbertCoefficientComparison
universe u uV uX uG uK uA
attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

/-- The restrictions along the finite and infinite inclusions commute. -/
theorem coordinateActions_commute
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (R : AdelicGL F n →* (H →L[ℂ] H))
    (g : ArchimedeanGL F n) (l : FiniteAdelicGL F n) (x : H) :
    (R.comp (infiniteCoordinateInclusion F n)) g
        ((R.comp (AdelicGL.ofFinite F n).toMonoidHom) l x) =
      (R.comp (AdelicGL.ofFinite F n).toMonoidHom) l
        ((R.comp (infiniteCoordinateInclusion F n)) g x) := by
  let a := (archimedeanGLCoordinates F n).symm g
  let ga := AdelicGL.ofInfinite F n a
  let gf := AdelicGL.ofFinite F n l
  have he := congrArg (fun y : AdelicGL F n => R y x) (AdelicGL.ofInfinite_commute F n a l)
  change R (ga * gf) x = R (gf * ga) x at he
  rw [map_mul, map_mul] at he
  exact he

variable
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
local notation "R∞" => B.action.comp (infiniteCoordinateInclusion F n)
local notation "Rf" => B.action.comp (ContinuousMonoidHom.toMonoidHom (AdelicGL.ofFinite F n))

private theorem hasPlaceFixedSmoothRealization
    {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
    {K : Type uK} [Group K] [TopologicalSpace K] (i : G →* ArchimedeanGL F n)
    (iK : K →* G) (hiK : Continuous iK) (k : Representation ℂ K V)
    (d : (ℂ ⊗[ℝ] A) →ₗ⁅ℂ⁆ Module.End ℂ V) (W : Submodule ℂ V) (hne : W ≠ ⊥)
    (hR : HasPlaceHilbertRealization (placeAction B.action i) b.toHilbert iK k d W)
    (hinner : ∀ g (x y : b.HilbertCompletion),
      Inner.inner ℂ (B.action g x) (B.action g y) = Inner.inner ℂ x y)
    (hs : ∀ v, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n)
      (B.action.comp (infiniteCoordinateInclusion F n)) (b.toHilbert v))
    (U : Subgroup (FiniteAdelicGL F n)) (hU : ∀ l : U, ∀ v : W, ρ (l : FiniteAdelicGL F n) v = v)
    (p : ArchimedeanGL F n →* G) (c : ArchimedeanGL F n → ArchimedeanGL F n)
    (hcentral : ∀ g h, Commute (c g) (i h)) (hsplit : ∀ g, c g * i (p g) = g)
    (hc : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ArchimedeanMatrix F n) ∞ c)
    (hp : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, A) ∞ (p : ArchimedeanGL F n → G)) :
    HasPlaceFixedSmoothRealization (𝔞 := ArchimedeanMatrix F n) (B.action.comp
      (infiniteCoordinateInclusion F n)) (B.action.comp (AdelicGL.ofFinite F n).toMonoidHom)
      i b.toHilbert iK k d (coordinateActions_commute B.action) U W := by
  apply hasPlaceFixedSmoothRealization_of_ambient R∞ Rf i b.toHilbert iK k d
    (coordinateActions_commute B.action) U W hR hiK hne ?_ (fun v => hs v)
    (fun g => hinner (infiniteCoordinateInclusion F n g)) p c hcentral hsplit hc hp
  intro v l
  change B.action (AdelicGL.ofFinite F n (l : FiniteAdelicGL F n)) (b.toHilbert v) = b.toHilbert v
  calc
    _ = b.completedFiniteOperator l (b.toHilbert v) := B.boundedCompatibility.1 l _
    _ = b.toHilbert (ρ (l : FiniteAdelicGL F n) v) := b.completedFiniteOperator_toHilbert l v
    _ = b.toHilbert v := congrArg b.toHilbert (hU l v)

/-- Fixed-level comparison using the actual real-place and finite adelic actions. -/
def SupportsRealPlaceFixedSmoothRealization (w : RP)
    (d : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  let k := κ.comp (realPlaceCompactInclusion F n w).toMonoidHom
  ∀ (U : Subgroup (FiniteAdelicGL F n)) (W : Submodule ℂ V),
    PlaceComponent.IsIrreducible k d W → PlaceComponent.IsAdmissible k W →
    (∀ l : U, ∀ v : W, ρ (l : FiniteAdelicGL F n) v = v) →
      HasPlaceFixedSmoothRealization (𝔞 := ArchimedeanMatrix F n) R∞ Rf
        (realPlaceGL F n w) b.toHilbert (Unitary.toUnits : RK →* RMˣ) k d
        (coordinateActions_commute B.action) U W

/-- Fixed-level comparison using the actual complex-place and finite adelic actions. -/
def SupportsComplexPlaceFixedSmoothRealization (w : CP)
    (d : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  let k := κ.comp (complexPlaceCompactInclusion F n w).toMonoidHom
  ∀ (U : Subgroup (FiniteAdelicGL F n)) (W : Submodule ℂ V),
    PlaceComponent.IsIrreducible k d W → PlaceComponent.IsAdmissible k W →
    (∀ l : U, ∀ v : W, ρ (l : FiniteAdelicGL F n) v = v) →
      HasPlaceFixedSmoothRealization (𝔞 := ArchimedeanMatrix F n) R∞ Rf
        (complexPlaceGL F n w) b.toHilbert (Unitary.toUnits : CK →* CMˣ) k d
        (coordinateActions_commute B.action) U W

variable (hinner : ∀ g (x y : b.HilbertCompletion),
    Inner.inner ℂ (B.action g x) (B.action g y) = Inner.inner ℂ x y)
  (hs : ∀ v, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n)
    (B.action.comp (infiniteCoordinateInclusion F n)) (b.toHilbert v))

include hinner hs in
theorem supportsRealPlaceFixedSmoothRealization (w : RP)
    (d : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hR : B.SupportsRealPlaceHilbertRealization w d) :
    B.SupportsRealPlaceFixedSmoothRealization w d := by
  intro U W hirr hadm hU
  exact B.hasPlaceFixedSmoothRealization (realPlaceGL F n w) Unitary.toUnits
    (continuous_subtype_val.comp (continuous_matrixUnitaryToCompact ℝ n))
    _ d W hirr.1 (hR W hirr hadm) hinner hs U hU
    (realPlaceGLProjection w) (realPlaceGLComplement w)
    (realPlaceGLComplement_commute w) (realPlaceGLComplement_split w)
    (contMDiff_realPlaceGLComplement w) (contMDiff_realPlaceGLProjection w)

include hinner hs in
theorem supportsComplexPlaceFixedSmoothRealization (w : CP)
    (d : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hR : B.SupportsComplexPlaceHilbertRealization w d) :
    B.SupportsComplexPlaceFixedSmoothRealization w d := by
  intro U W hirr hadm hU
  exact B.hasPlaceFixedSmoothRealization (complexPlaceGL F n w) Unitary.toUnits
    (continuous_subtype_val.comp (continuous_matrixUnitaryToCompact ℂ n))
    _ d W hirr.1 (hR W hirr hadm) hinner hs U hU
    (complexPlaceGLProjection w) (complexPlaceGLComplement w)
    (complexPlaceGLComplement_commute w) (complexPlaceGLComplement_split w)
    (contMDiff_complexPlaceGLComplement w) (contMDiff_complexPlaceGLProjection w)

end Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion
