import Langlands.Global.AdelicEisensteinLinearConvergence
import Langlands.Global.AdelicEisensteinDifferential
import Langlands.Global.EisensteinScalarOperatorAction
import Langlands.Automorphic.GroupSchemeManifoldSmooth

/-! # Operator identities for convergent Eisenstein values -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open AdelicGroupPoints GeneralLinearGroupPoints InfiniteAdelicGroupPoints

section ConvergenceDomain

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)

local notation "Points" => AdelicGroupPoints F G
local notation "Values" => LinearMap.range (finitePlotSmoothEvaluation F G)

/-- The convergent domain with smooth, rational-invariant Eisenstein outputs. -/
def smoothConvergenceSections : Submodule ℂ (Points → ℂ) :=
  (Submodule.comap (hK.eisensteinSeriesLinear lam) Values).map
    (hK.compactMajorantSections lam).subtype

theorem mem_smoothConvergenceSections (φ : Points → ℂ) :
    φ ∈ smoothConvergenceSections F G hK lam ↔
      φ ∈ hK.compactMajorantSections lam ∧ hK.eisensteinSeries φ lam ∈ Values := by
  constructor
  · rintro ⟨⟨ψ, hψ⟩, hvalue, rfl⟩
    exact ⟨hψ, hvalue⟩
  · rintro ⟨hφ, hvalue⟩
    exact ⟨⟨φ, hφ⟩, hvalue, rfl⟩

/-- Linear Eisenstein evaluation in the range of the actual smooth form carrier. -/
def smoothEisensteinSeries : smoothConvergenceSections F G hK lam →ₗ[ℂ] Values where
  toFun φ := ⟨hK.eisensteinSeries φ.val lam,
    ((mem_smoothConvergenceSections F G hK lam φ.val).mp φ.property).2⟩
  map_add' φ ψ := by
    apply Subtype.ext
    exact (hK.eisensteinSeriesLinear lam).map_add
      ⟨φ.val, ((mem_smoothConvergenceSections F G hK lam φ.val).mp φ.property).1⟩
      ⟨ψ.val, ((mem_smoothConvergenceSections F G hK lam ψ.val).mp ψ.property).1⟩
  map_smul' z φ := by
    apply Subtype.ext
    exact (hK.eisensteinSeriesLinear lam).map_smul z
      ⟨φ.val, ((mem_smoothConvergenceSections F G hK lam φ.val).mp φ.property).1⟩

end ConvergenceDomain

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance convergentOperatorsGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local notation "Adeles" => AdelicGroupPoints F GLG
local notation "scalarValue" => finitePlotSmoothEvaluation F GLG

local notation "Forms" => FinitePlotSmoothRationalFunctions F GLG

/-- A deformed finite translation of the inducing section becomes the old
finite right translation on the convergent Eisenstein value. -/
theorem scalarAutomorphicOperator_eisensteinSeries_finite
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GLG}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)
    (φ ψ : Adeles → ℂ)
    (b : FiniteAdelicGroupPoints F GLG)
    (f : Forms) (hf : scalarValue f = hK.eisensteinSeries φ lam)
    (hψ : ψ = hK.parameterRightAction lam (ofFinite F GLG b) φ) :
    scalarAutomorphicOperator F n (finiteOperator F n (finiteHomeomorph F n b))
      (hK.eisensteinSeries φ lam) = hK.eisensteinSeries ψ lam := by
  funext x
  rw [← hf, scalarAutomorphicOperator_finite, hf, hψ, hK.eisensteinSeries_parameterRightAction]

/-- An infinite compact translation lying in the Iwasawa compact needs no
height factor on the inducing section. -/
theorem scalarAutomorphicOperator_eisensteinSeries_compact
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GLG}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)
    (φ ψ : Adeles → ℂ)
    [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
    (k : standardInfiniteCompact F n)
    (hk : ofInfinite F GLG ((infiniteHomeomorph F n).symm k.val) ∈ K)
    (f : Forms) (hf : scalarValue f = hK.eisensteinSeries φ lam)
    (hψ : ψ = fun x : Adeles => φ (x * ofInfinite F GLG ((infiniteHomeomorph F n).symm k.val))) :
    scalarAutomorphicOperator F n (compactOperator F n k)
      (hK.eisensteinSeries φ lam) = hK.eisensteinSeries ψ lam := by
  let a := ofInfinite F GLG ((infiniteHomeomorph F n).symm k.val)
  have htranslate : ψ = hK.parameterRightAction lam a φ :=
    hψ.trans (funext fun x => (hK.parameterRightAction_compact lam a hk φ x).symm)
  funext x
  rw [← hf, scalarAutomorphicOperator_compact, hf, htranslate, hK.eisensteinSeries_parameterRightAction]

/-- Summable compact majorants for the twisted terms and their first
derivatives identify the real invariant derivative with the convergent sum
on the deformed section. -/
theorem scalarAutomorphicOperator_eisensteinSeries_realDirectional
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GLG}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)
    (φ ψ : Adeles → ℂ)
    {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) (X : smoothModel F d)
    (f : Forms) (hf : scalarValue f = hK.eisensteinSeries φ lam)
    (hφ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F GLG hsmooth
      ∀ b : FiniteAdelicGroupPoints F GLG,
        ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
          (fun a => hK.parameterTwist φ lam (pair F GLG a b)))
    (hmajor : φ ∈ hK.compactMajorantSections lam)
    (hderiv : ∀ Y : smoothModel F d, hK.parameterDirectionalSection hsmooth lam Y φ ∈
      hK.compactMajorantSections lam)
    (hψ : ψ = hK.parameterDirectionalSection hsmooth lam X φ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F GLG hsmooth
    scalarAutomorphicOperator F n
      (differentialOperator F n (ArchimedeanGL.envelopingGenerator F n
        (ArchimedeanGL.complexify F n (infiniteRealLieAlgebraEquiv F n hsmooth X))))
      (hK.eisensteinSeries φ lam) = hK.eisensteinSeries ψ lam := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  have hE (b : FiniteAdelicGroupPoints F GLG) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
        (fun a => hK.eisensteinSeries φ lam (pair F GLG a b)) := by
    rw [← hf]
    exact (isPlotSmooth_iff_contMDiff F GLG hsmooth _).mp (finitePlotSmoothSlice F GLG b f).property
  funext g
  obtain ⟨a, b, rfl⟩ : ∃ a b, g = pair F GLG a b := ⟨_, _, (pair_projections F GLG g).symm⟩
  rw [← hf, scalarAutomorphicOperator_realDirectional, hf, hψ]
  let := hsmooth
  let : Smooth (GLG).X.hom := SmoothOfRelativeDimension.smooth d (GLG).X.hom
  exact hK.directionalValue_eisensteinSeries hsmooth lam φ hφ hE hmajor hderiv X a b

end Langlands.Global.EisensteinJet
