import Langlands.Automorphic.CuspidalWhittakerBandSobolevEstimate
import Langlands.Automorphic.OperatorCompactSobolevProof
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerIdentityEvaluation
import Langlands.Global.RankinSelberg.CuspidalBandMixedWhittaker
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerPlaces
import Langlands.Global.RankinSelberg.WhittakerPairedHilbert
import Langlands.Representation.Archimedean.UnitaryWhittakerMultiplicityOneProof

/-! # Comparing actual Whittaker evaluations on two local embeddings -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Automorphic ArchimedeanGL InfinitePlaceFamily OperatorDeterminantSlice CuspidalFixedSmoothDensity
open HilbertCoefficientComparison Langlands.Archimedean SmoothInvariantSubspace MixedSmooth
open Langlands.HarmonicAnalysis Langlands.HarishChandraSchwartz Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.Global.CuspidalPairFunctionalEquation

universe u uV uZ uE

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup

section AbstractCompletion

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (U : AdelicGL F (r + 1) →* (E →L[ℂ] E)) (j : Z →ₗ[ℂ] E)

local notation "n" => r + 1
local notation "σ" => finiteHilbertAction F n U
local notation "π" => infiniteHilbertAction F n U
local notation "comm" => hilbertCoordinateActions_commute F n U
local notation "Mixed" => Vectors (A := ArchimedeanMatrix F n) σ π comm

set_option maxHeartbeats 45000 in
private theorem compare_at_place
    (hj : Function.Injective j) (hcont : IsContinuousRepresentation U)
    (hunit : ∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y)
    (hsmooth : ∀ v : Z, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n) π (j v))
    (D : EnvelopingAlgebra F n → Z → Z)
    (hcoeff : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j D)
    (jY : Z →ₗ[ℂ] Mixed) (hjY : ∀ v, (jY v).val.val = j v)
    (ψ : UnitaryAdditiveCharacter (Adeles F)) (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (ℓ : Mixed →ₗ[ℂ] ℂ) (hℓ : IsMixedWhittakerFunctional (r := r) ψ.complex σ π comm ℓ)
    (eval : Z → ℂ) (heval : ∀ v, ℓ (jY v) = eval v)
    (i : Index F) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (k : Representation ℂ (Compact n i) V) (d : Lie n i →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hirr : IsIrreducibleGKModule k d) (hadm : IsAdmissibleGKModule k)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector k v)
    (A : Bool → V →ₗ[ℂ] Z) (hinj : Function.Injective (A false))
    (hAK : ∀ t l v, j (A t (k l v)) = U (AdelicGL.ofInfinite F n (compactInclusion n i l).val) (j (A t v)))
    (hAD : ∀ t X v, A t (d X v) = D (envelopingGenerator F n (lieInclusion n i X)) (A t v))
    (hfixed : ∀ t, ∃ J : CompactOpenSubgroup (FiniteAdelicGL F n),
      ∀ v, j (A t v) ∈ fixedSubspace σ J.toSubgroup)
    (hn : ∃ v, eval (A false v) ≠ 0) :
    ∃ s : ℂ, ∀ v, eval (A true v) = s * eval (A false v) := by
  have hn' : ∃ v, ℓ (jY (A false v)) ≠ 0 := by
    obtain ⟨v, hv⟩ := hn
    exact ⟨v, fun h => hv ((heval _).symm.trans h)⟩
  suffices h : ∃ s : ℂ, ∀ v, ℓ (jY (A true v)) = s * ℓ (jY (A false v)) by
    obtain ⟨s, hs⟩ := h
    exact ⟨s, fun v => ((heval _).symm.trans (hs v)).trans (congrArg (s * ·) (heval _))⟩
  cases i with
  | inl w =>
    obtain ⟨a, ha⟩ := exists_isRealAdditiveComponent ψ hψ w
    have compact_eq (l : Matrix.unitaryGroup (Fin n) ℝ) :
        (archimedeanGLCoordinates F n).symm (realPlaceGL F n w (Unitary.toUnits l)) =
          (compactInclusion n (.inl w) l).val :=
      (congrArg (archimedeanGLCoordinates F n).symm (ArchimedeanGL.realPlaceGL_unitary w l)).trans
        ((archimedeanGLCoordinates F n).symm_apply_apply _)
    refine proportional_mixedWhittaker_of_realEmbeddings U j unitaryWhittakerMultiplicityOne.{uE}.1
      hj hcont hunit hsmooth D hcoeff w k d hirr hadm hfin A hinj ?_ ?_ hfixed jY hjY
      (realScaledCharacter a) ℓ hℓ.1 (mixedWhittaker_realPlace σ π comm ψ ℓ hℓ w a ha) hn'
    · intro t l v
      exact (hAK t l v).trans (congrArg (fun g => U (AdelicGL.ofInfinite F n g) (j (A t v)))
        (compact_eq l).symm)
    · intro t X v
      exact (hAD t (1 ⊗ₜ[ℝ] X) v).trans
        (congrArg (fun X₀ => D (envelopingGenerator F n X₀) (A t v))
          ((realPlaceComplexLieInclusion_tmul F n w 1 X).trans (complexify_apply F n _).symm))
  | inr w =>
    obtain ⟨a, ha⟩ := exists_isComplexAdditiveComponent ψ hψ w
    have compact_eq (l : Matrix.unitaryGroup (Fin n) ℂ) :
        (archimedeanGLCoordinates F n).symm (complexPlaceGL F n w (Unitary.toUnits l)) =
          (compactInclusion n (.inr w) l).val :=
      (congrArg (archimedeanGLCoordinates F n).symm (ArchimedeanGL.complexPlaceGL_unitary w l)).trans
        ((archimedeanGLCoordinates F n).symm_apply_apply _)
    refine proportional_mixedWhittaker_of_complexEmbeddings U j unitaryWhittakerMultiplicityOne.{uE}.2
      hj hcont hunit hsmooth D hcoeff w k d hirr hadm hfin A hinj ?_ ?_ hfixed jY hjY
      (complexScaledCharacter a) ℓ hℓ.1 (mixedWhittaker_complexPlace σ π comm ψ ℓ hℓ w a ha) hn'
    · intro t l v
      exact (hAK t l v).trans (congrArg (fun g => U (AdelicGL.ofInfinite F n g) (j (A t v)))
        (compact_eq l).symm)
    · intro t X v
      exact (hAD t (1 ⊗ₜ[ℝ] X) v).trans
        (congrArg (fun X₀ => D (envelopingGenerator F n X₀) (A t v))
          ((complexPlaceComplexLieInclusion_tmul F n w 1 X).trans (complexify_apply F n _).symm))

end AbstractCompletion

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

local notation "n" => r + 1

set_option maxHeartbeats 100000 in
private theorem with_bandWhittakerModel
    (hT : HasUnitaryCentralCharacter T)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ) {Q : Prop}
    (useModel : ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (U : AdelicGL F n →* (E →L[ℂ] E)) (j : T.Space →ₗ[ℂ] E),
      Function.Injective j → IsContinuousRepresentation U →
      (∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y) →
      (∀ v : T.Space, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n)
        (infiniteHilbertAction F n U) (j v)) →
      JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j (fun a v => T.realization.envelopingAction a v) →
      (∀ k v, U (AdelicGL.ofInfinite F n k.val) (j v) = j (T.realization.compactRepresentation k v)) →
      (∀ g v, U (AdelicGL.ofFinite F n g) (j v) = j (T.realization.finiteRepresentation g v)) →
      ∀ (jY : T.Space →ₗ[ℂ] Vectors (A := ArchimedeanMatrix F n)
        (finiteHilbertAction F n U) (infiniteHilbertAction F n U) (hilbertCoordinateActions_commute F n U)),
        (∀ v, (jY v).val.val = j v) →
      ∀ ℓ, IsMixedWhittakerFunctional (r := r) χ
        (finiteHilbertAction F n U) (infiniteHilbertAction F n U) (hilbertCoordinateActions_commute F n U) ℓ →
        (∀ v, ℓ (jY v) = cuspWhittaker F T χ v 1) → Q) : Q := by
  obtain ⟨central, hcentral, hTcentral⟩ := hT
  let hL2 := memLp_cuspidal_toQuotient_band F T
  obtain ⟨b, hb⟩ : ∃ b : T.realization.UnitaryForm, ComputesBandInnerProduct T.realization b :=
    ⟨unitaryForm F n T.realization (Nat.succ_ne_zero r) T.cuspidal central hcentral hTcentral hL2,
      unitaryForm_inner F n T.realization (Nat.succ_ne_zero r) T.cuspidal central hcentral hTcentral hL2⟩
  let B := adelicCompletion T central hcentral hTcentral b hb
  let U := B.action
  let π := infiniteHilbertAction F n U
  let jY := (toHilbertMixed T central hcentral hTcentral b hb).toLinearMap
  have hbound := cuspWhittakerBandBound_of_compactSobolev F T operatorCompactSobolev central hcentral hTcentral hL2 χ hχ
  obtain ⟨ℓ, hℓ, hval, _⟩ := hasMixedWhittakerModel_of_bandBound F r T central hcentral hTcentral b hb χ hχ hL2 hbound
  have hval₁ (v : T.Space) : ℓ (jY v) = cuspWhittaker F T χ v 1 := by
    simpa only [map_one, Module.End.one_apply, ArchimedeanWhittakerEvaluation.adelicPoint_one] using hval v 1 1
  have hcont := jointlyContinuous_adelicHilbertRepresentation T cuspidalHilbertOrbitCoefficient central hcentral hTcentral b hb
  have hunit := (adelicHilbertRepresentation_realizes T cuspidalHilbertOrbitCoefficient central hcentral hTcentral b hb).2
  have hsmooth (v : T.Space) : Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n)
      π (b.toHilbert v) := (jY v).val.property
  have hK (k : standardInfiniteCompact F n) (v : T.Space) :
      U (AdelicGL.ofInfinite F n k.val) (b.toHilbert v) = b.toHilbert (T.realization.compactRepresentation k v) :=
    (B.boundedCompatibility.2 k _).trans (b.completedCompactOperator_toHilbert k v)
  have hF (g : FiniteAdelicGL F n) (v : T.Space) :
      U (AdelicGL.ofFinite F n g) (b.toHilbert v) = b.toHilbert (T.realization.finiteRepresentation g v) :=
    (B.boundedCompatibility.1 g _).trans (b.completedFiniteOperator_toHilbert g v)
  exact @useModel b.HilbertCompletion _ _ _ U b.toHilbert b.toHilbert_injective hcont hunit hsmooth
    B.coefficients hK hF jY (fun _ => rfl) ℓ hℓ hval₁

set_option maxHeartbeats 60000 in
/-- For a unitary cuspidal central character, the actual identity evaluations on two
embeddings of the same admissible irreducible place module are proportional. The
reference evaluation is assumed nonzero on that module. -/
theorem proportional_cuspWhittaker_one_of_placeEmbeddings
    (hT : HasUnitaryCentralCharacter T)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    (i : Index F) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (k : Representation ℂ (Compact n i) V) (d : Lie n i →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hirr : IsIrreducibleGKModule k d) (hadm : IsAdmissibleGKModule k)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector k v)
    (A : Bool → V →ₗ[ℂ] T.Space) (hinj : Function.Injective (A false))
    (hAK : ∀ t l v, A t (k l v) = T.realization.placeCompactFamily i l (A t v))
    (hAD : ∀ t X v, A t (d X v) = T.realization.placeLieFamily i X (A t v))
    (hfix : ∀ t, ∃ B : CompactOpenSubgroup (FiniteAdelicGL F n),
      ∀ (g : B.toSubgroup) v, T.realization.finiteRepresentation g.val (A t v) = A t v)
    (hne : ∃ v, cuspWhittaker F T χ (A false v) 1 ≠ 0) :
    ∃ s : ℂ, ∀ v, cuspWhittaker F T χ (A true v) 1 = s * cuspWhittaker F T χ (A false v) 1 := by
  refine with_bandWhittakerModel T hT χ hχ (fun E _ _ _ U j hj hcont hunit hsmooth
    hcoeff hK hF jY hjY ℓ hℓ hval => ?_)
  let χ₀ := UnitaryAdditiveCharacter.ofComplex χ hχ.1 hχ.2.1 hχ.2.2.2
  have hdiag (x : F) : χ₀ (diagonal F x) = 1 := Subtype.ext (hχ.2.2.1 x)
  refine compare_at_place U j hj hcont hunit hsmooth _ hcoeff jY hjY χ₀ hdiag ℓ hℓ
    (fun v => cuspWhittaker F T χ v 1) hval i k d hirr hadm hfin A hinj ?_ hAD ?_ hne
  · intro t l v
    exact (congrArg j (hAK t l v)).trans (hK (compactInclusion n i l) (A t v)).symm
  · intro t
    exact (hfix t).elim (fun J hJ => ⟨J, fun v g =>
      (hF g.val (A t v)).trans (congrArg j (hJ g v))⟩)

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
