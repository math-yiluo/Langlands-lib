import Langlands.Automorphic.FiniteVectors
import Langlands.Global.ArchimedeanComplexification
import Langlands.Representation.Archimedean.CompactSmoothFiniteDensity
import Langlands.Representation.Archimedean.SmoothFixedSubspace
import Langlands.Representation.Unitary.CompactIsometricAverage
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Compact-finite derivative density at a fixed adelic level -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000

open scoped Classical Manifold ContDiff Matrix.Norms.Operator
open MeasureTheory

namespace Langlands.Automorphic.CuspidalFixedSmoothDensity

open Langlands.Global Langlands.Archimedean Langlands.Archimedean.SmoothInvariantSubspace

universe u v

section CompactCoordinates

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

/-- The published complexification acting on its finite standard coordinate space. -/
def compactComplexRepresentation (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    Representation ℂ (standardInfiniteCompact F n) (ArchimedeanComplexIndex F n → ℂ) :=
  (Matrix.toLinAlgEquiv'.toMonoidHom.comp (Units.coeHom _)).comp
    ((infiniteAdelicComplexGL F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype)

theorem compactComplexRepresentation_injective :
    Function.Injective (compactComplexRepresentation F n) :=
  Matrix.toLinAlgEquiv'.injective.comp
    (Units.val_injective.comp
      ((isClosedEmbedding_infiniteAdelicComplexGL F n).injective.comp Subtype.val_injective))

theorem continuous_compactComplexRepresentation_orbit (v : ArchimedeanComplexIndex F n → ℂ) :
    Continuous (fun k => compactComplexRepresentation F n k v) := by
  have hm : Continuous (fun k : standardInfiniteCompact F n =>
      (infiniteAdelicComplexGL F n (k : InfiniteAdelicGL F n)).val) :=
    Units.continuous_val.comp ((infiniteAdelicComplexGL F n).continuous.comp continuous_subtype_val)
  apply continuous_pi
  intro i
  change Continuous (fun k : standardInfiniteCompact F n =>
    Matrix.toLinAlgEquiv' (infiniteAdelicComplexGL F n (k : InfiniteAdelicGL F n)).val v i)
  simp only [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ =>
    (((continuous_apply j).comp (continuous_apply i)).comp hm).mul continuous_const

/-- Inclusion of the original standard compact into the mixed manifold coordinates. -/
def compactCoordinates (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    standardInfiniteCompact F n →ₜ* ArchimedeanGL F n where
  __ := (archimedeanGLCoordinates F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype
  continuous_toFun := (archimedeanGLCoordinates F n).continuous.comp continuous_subtype_val

end CompactCoordinates

section FixedSubspaceDensity

universe uA uG uH uL uK uι

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {L : Type uL} [Group L] {K : Type uK} [Group K] [TopologicalSpace K]
  [IsTopologicalGroup K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (σ : L →* (H →L[ℂ] H)) (J : Subgroup L) (π : G →* (H →L[ℂ] H))
  (hcomm : ∀ g l x, π g (σ l x) = σ l (π g x))
  (iK : K →ₜ* G) (κ : Representation ℂ K H)

local notation "I" => 𝓘(ℝ, A)
local notation "πJ" => fixedRestriction σ J π hcomm
local notation "κJ" => CompactSmoothFiniteDensity.restrictedRepresentation πJ iK

include hcomm in
private theorem dense_compactFinite_ambientFixed
    (hκ : ∀ k x, π (iK k) x = κ k x)
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    {ι : Type uι} [Fintype ι] (τ : Representation ℂ K (ι → ℂ))
    (hτ : ∀ v, Continuous (fun k => τ k v)) (hinj : Function.Injective τ) :
    Dense {w : ambientFixedSmoothSubspace σ J π I |
      FiniteVectors.IsFiniteVector κ
        (DerivativeSmoothVectors.toSmooth I π (w : DerivativeSmoothVectors I π) : H)} := by
  let e := fixedDerivativeEquiv σ J π hcomm I
  let jK : Representation.IntertwiningMap κJ κ :=
    { toLinearMap := (fixedSubspace σ J).subtype
      isIntertwining' k := LinearMap.ext fun x => hκ k x }
  have hd : Dense {w : DerivativeSmoothVectors I πJ |
    FiniteVectors.IsFiniteVector κJ (DerivativeSmoothVectors.toSmooth I πJ w : fixedSubspace σ J)} :=
    CompactSmoothFiniteDensity.dense_finiteSmoothVectors πJ iK μ τ hτ hinj
  refine (e.surjective.denseRange.dense_image e.continuous hd).mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact (show FiniteVectors.IsFiniteVector κJ
    (DerivativeSmoothVectors.toSmooth I πJ w : fixedSubspace σ J) from hw).map jK

end FixedSubspaceDensity

section Restrictions

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : AdelicGL F n →* (H →L[ℂ] H))

/-- The supplied action restricted to the original finite adelic factor. -/
abbrev finiteHilbertAction : FiniteAdelicGL F n →* (H →L[ℂ] H) :=
  U.comp (AdelicGL.ofFinite F n).toMonoidHom

/-- The supplied action restricted to the infinite adelic factor in mixed coordinates. -/
abbrev infiniteHilbertAction : ArchimedeanGL F n →* (H →L[ℂ] H) :=
  U.comp ((AdelicGL.ofInfinite F n).toMonoidHom.comp
    (archimedeanGLCoordinates F n).symm.toMonoidHom)

/-- The coordinate action restricts to the original compact inclusion. -/
theorem infiniteHilbertAction_compactCoordinates_apply (k : standardInfiniteCompact F n) (x : H) :
    infiniteHilbertAction F n U (compactCoordinates F n k) x =
      U (AdelicGL.ofInfinite F n k.val) x :=
  congrArg (fun a : InfiniteAdelicGL F n => U (AdelicGL.ofInfinite F n a) x)
    ((archimedeanGLCoordinates F n).symm_apply_apply k.val)

private theorem archimedean_commute_finite (g : ArchimedeanGL F n)
    (d : FiniteAdelicGL F n) (w : H) :
    infiniteHilbertAction F n U g (finiteHilbertAction F n U d w) =
      finiteHilbertAction F n U d (infiniteHilbertAction F n U g w) := by
  let a := AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm g)
  let k := AdelicGL.ofFinite F n d
  change U a (U k w) = U k (U a w)
  simp only [← mul_apply_eq_comp, ← map_mul]
  exact congrArg (fun z : AdelicGL F n => U z w)
    (AdelicGL.ofFinite_commute_ofInfinite F n d
      ((archimedeanGLCoordinates F n).symm g)).eq.symm

local notation "σ" => finiteHilbertAction F n U
local notation "π" => infiniteHilbertAction F n U
local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F n)

variable [CompleteSpace H]

/-- Compact-finite smooth vectors are dense in the ambient fixed subspace. -/
theorem dense_compactFinite_fixedSmooth
    (κ : Representation ℂ (standardInfiniteCompact F n) H)
    (hκ : ∀ (k : standardInfiniteCompact F n) (x : H), π (compactCoordinates F n k) x = κ k x)
    (J : Subgroup (FiniteAdelicGL F n)) :
    Dense {w : ambientFixedSmoothSubspace σ J π I |
      FiniteVectors.IsFiniteVector κ (DerivativeSmoothVectors.toSmooth I π
        (w : DerivativeSmoothVectors I π) : H)} := by
  let K : Type u := standardInfiniteCompact F n
  let : T2Space (NumberField.InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let iK : K →ₜ* ArchimedeanGL F n := compactCoordinates F n
  let μ : Measure K := Analysis.compactProbabilityHaar K
  let τ : Representation ℂ K (ArchimedeanComplexIndex F n → ℂ) :=
    compactComplexRepresentation F n
  have hτ : ∀ v, Continuous (fun k => τ k v) :=
    continuous_compactComplexRepresentation_orbit (F := F) (n := n)
  have hinj : Function.Injective τ := compactComplexRepresentation_injective (F := F) (n := n)
  exact dense_compactFinite_ambientFixed
    (A := ArchimedeanMatrix F n) (G := ArchimedeanGL F n) (H := H)
    (L := FiniteAdelicGL F n) (K := K) σ J π (archimedean_commute_finite F n U) iK κ hκ
    μ (ι := ArchimedeanComplexIndex F n) τ hτ hinj

end Restrictions

end Langlands.Automorphic.CuspidalFixedSmoothDensity
