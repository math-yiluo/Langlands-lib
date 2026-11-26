import Langlands.Automorphic.AdelicHilbertCoordinateActions
import Langlands.Automorphic.HilbertPlaceGenerators
import Langlands.Global.ArchimedeanPlaceSplitting
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerPlaces
import Langlands.Representation.Archimedean.HilbertPlaceSmooth
import Langlands.Representation.Archimedean.MixedFixedSmoothMap
import Langlands.Representation.Archimedean.UnitaryCompactAdmissibility
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # A common Hilbert realization for two archimedean Whittaker restrictions -/

noncomputable section

open NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Automorphic ArchimedeanGL HilbertCoefficientComparison OperatorDeterminantSlice
open Langlands.Archimedean DerivativeSmoothVectors SmoothInvariantSubspace MixedSmooth
open Langlands.HarmonicAnalysis Langlands.HarishChandraSchwartz CuspidalFixedSmoothDensity

universe u uV uZ uE

attribute [local instance 100] LieRing.ofAssociativeRing

section Diagonal

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "H₂" => WithLp 2 (E × E)

private def pairedAction {G : Type*} [Monoid G] (U : G →* (E →L[ℂ] E)) :
    G →* (H₂ →L[ℂ] H₂) where
  toFun g := (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
    (((U g).comp (WithLp.fstL 2 ℂ E E)).prod ((U g).comp (WithLp.sndL 2 ℂ E E)))
  map_one' := by
    ext1 x
    apply (WithLp.equiv 2 (E × E)).injective
    change (U 1 x.ofLp.1, U 1 x.ofLp.2) = x.ofLp
    rw [map_one]
    rfl
  map_mul' g h := by
    ext1 x
    apply (WithLp.equiv 2 (E × E)).injective
    change (U (g * h) x.ofLp.1, U (g * h) x.ofLp.2) =
      (U g (U h x.ofLp.1), U g (U h x.ofLp.2))
    rw [map_mul]
    rfl

private theorem pairedAction_continuous {G : Type*} [Group G] [TopologicalSpace G]
    (U : G →* (E →L[ℂ] E)) (hU : IsContinuousRepresentation U) :
    IsContinuousRepresentation (pairedAction U) := by
  let π₀ : H₂ →L[ℂ] E := WithLp.fstL 2 ℂ E E
  let π₁ : H₂ →L[ℂ] E := WithLp.sndL 2 ℂ E E
  have h₀ : Continuous (fun x : G × H₂ => U x.1 (π₀ x.2)) :=
    hU.comp (continuous_fst.prodMk (π₀.continuous.comp continuous_snd))
  have h₁ : Continuous (fun x : G × H₂ => U x.1 (π₁ x.2)) :=
    hU.comp (continuous_fst.prodMk (π₁.continuous.comp continuous_snd))
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.continuous.comp (h₀.prodMk h₁)

private theorem pairedAction_inner {G : Type*} [Monoid G]
    (U : G →* (E →L[ℂ] E)) (hU : ∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y)
    (g : G) (x y : H₂) : inner ℂ (pairedAction U g x) (pairedAction U g y) = inner ℂ x y := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  exact congrArg₂ (· + ·) (hU g x.ofLp.1 y.ofLp.1) (hU g x.ofLp.2 y.ofLp.2)

variable {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]

private def pairedEmbedding (j : Z →ₗ[ℂ] E) : Z × Z →ₗ[ℂ] H₂ :=
  (WithLp.linearEquiv 2 ℂ (E × E)).symm.toLinearMap.comp (j.prodMap j)

private theorem pairedEmbedding_injective (j : Z →ₗ[ℂ] E) (hj : Function.Injective j) :
    Function.Injective (pairedEmbedding j) := by
  intro x y h
  have he := congrArg WithLp.ofLp h
  exact Prod.ext (hj (congrArg Prod.fst he)) (hj (congrArg Prod.snd he))

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

private theorem pairedCoefficients
    (U : AdelicGL F n →* (E →L[ℂ] E)) (j : Z →ₗ[ℂ] E)
    (D : EnvelopingAlgebra F n → Z → Z)
    (hcoeff : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j D) :
    JointFiniteCoefficientLifts (pairedAction U) (AdelicGL.ofInfinite F n) (pairedEmbedding j)
      (fun (a : EnvelopingAlgebra F n) (z : Z × Z) => (D a z.1, D a z.2)) := by
  intro w
  obtain ⟨C₀, h₀, hD₀, hfin₀⟩ := hcoeff w.ofLp.1
  obtain ⟨C₁, h₁, hD₁, hfin₁⟩ := hcoeff w.ofLp.2
  refine ⟨C₀.comp (LinearMap.fst ℂ Z Z) + C₁.comp (LinearMap.snd ℂ Z Z), ?_, ?_, ?_⟩
  · intro z g
    change (C₀ z.1).val g + (C₁ z.2).val g = _
    rw [h₀, h₁, WithLp.prod_inner_apply]
    rfl
  · intro a z
    change C₀ (D a z.1) + C₁ (D a z.2) = envelopingAction F n a (C₀ z.1 + C₁ z.2)
    rw [map_add, hD₀, hD₁]
  · intro z
    exact (jointFiniteFunctions F n).add_mem (hfin₀ z.1) (hfin₁ z.2)

private theorem pairedEmbedding_smooth
    (U : AdelicGL F n →* (E →L[ℂ] E)) (j : Z →ₗ[ℂ] E)
    (hs : ∀ z, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n)
      (infiniteHilbertAction F n U) (j z)) (z : Z × Z) :
    Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n)
      (infiniteHilbertAction F n (pairedAction U)) (pairedEmbedding j z) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ E E
  exact (e.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.contMDiff.comp
    ((hs z.1).prodMk_space (hs z.2))

end Diagonal

section Comparison

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}
  {𝕜 : Type} [RCLike 𝕜] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "n" => r + 1
local notation "M" => Matrix (Fin n) (Fin n) 𝕜
local notation "K" => Matrix.unitaryGroup (Fin n) 𝕜
local notation "I" => 𝓘(ℝ, M)
local notation "J∞" => 𝓘(ℝ, ArchimedeanMatrix F n)
local notation "H₂" => WithLp 2 (E × E)

variable (U : AdelicGL F (r + 1) →* (E →L[ℂ] E)) (j : Z →ₗ[ℂ] E)
  (ι : (Matrix (Fin (r + 1)) (Fin (r + 1)) 𝕜)ˣ →* ArchimedeanGL F (r + 1))

local notation "σ" => finiteHilbertAction F n U
local notation "π" => infiniteHilbertAction F n U
local notation "hm" => hilbertCoordinateActions_commute F n U
local notation "Y" => Vectors (A := ArchimedeanMatrix F n) σ π hm
local notation "P∞" => placeAction (pairedAction U) ι
local notation "toK" => (Unitary.toUnits : K →* Mˣ)

/-- The closure of the paired algebraic image is one irreducible local Hilbert
realization. Its two projections preserve the algebraic embeddings, so a mixed
functional with local Whittaker covariance pulls back through both projections
and can be compared by unitary Whittaker uniqueness. -/
private theorem proportional_mixedWhittaker_of_pairedEmbeddings
    (hUnique : UnitaryWhittakerMultiplicityOneOver.{uE} 𝕜)
    (hj : Function.Injective j) (hcont : IsContinuousRepresentation U)
    (hunit : ∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y)
    (hs : ∀ z, Langlands.Archimedean.IsSmoothVector J∞ π (j z))
    (D : EnvelopingAlgebra F n → Z → Z)
    (hcoeff : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j D)
    (hι : ContMDiff I J∞ ∞ ι)
    (a : M → ArchimedeanMatrix F n) (L : M → RealLieAlgebra F n)
    (ha : ∀ g : Mˣ, a (g : M) = (ι g : ArchimedeanMatrix F n))
    (han : ∀ (f : SmoothFunctions F n) (g : Mˣ),
      AnalyticAt ℝ (coordinateExtension F n f) (ι g : ArchimedeanMatrix F n) →
        AnalyticAt ℝ (coordinateExtension F n f ∘ a) (g : M))
    (hder : ∀ (f : SmoothFunctions F n) (g : Mˣ) (X : M),
      fderiv ℝ (coordinateExtension F n f ∘ a) (g : M) ((g : M) * X) =
        (smoothDifferential F n (L X) f).val ((archimedeanGLCoordinates F n).symm (ι g)))
    (p : ArchimedeanGL F n →* Mˣ) (c : ArchimedeanGL F n → ArchimedeanGL F n)
    (hcentral : ∀ g h, Commute (c g) (ι h)) (hsplit : ∀ g, c g * ι (p g) = g)
    (hc : ContMDiff J∞ J∞ ∞ c) (hp : ContMDiff J∞ I ∞ (p : ArchimedeanGL F n → Mˣ))
    (κ : Representation ℂ K V) (d : (ℂ ⊗[ℝ] M) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hirr : IsIrreducibleGKModule κ d) (hadm : IsAdmissibleGKModule κ)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector κ v)
    (A : Bool → V →ₗ[ℂ] Z) (hA : Function.Injective (A false))
    (hAK : ∀ t k v, j (A t (κ k v)) = placeAction U ι (toK k) (j (A t v)))
    (hAD : ∀ t X v, A t (d (1 ⊗ₜ[ℝ] X) v) = D (envelopingGenerator F n (complexify F n (L X))) (A t v))
    (hfix : ∀ t, ∃ B : CompactOpenSubgroup (FiniteAdelicGL F n),
        ∀ v, j (A t v) ∈ fixedSubspace σ B.toSubgroup)
    (jY : Z →ₗ[ℂ] Y) (hjY : ∀ z, (jY z).val.val = j z)
    (ψv : UnitaryAdditiveCharacter 𝕜)
    (ℓ : Y →ₗ[ℂ] ℂ) (hℓ : IsContinuousAtEachLevel σ π hm ℓ)
    (hwhit : ∀ x : Langlands.GeneralLinear.upperUnipotent n 𝕜, ∀ v : Y,
      ℓ (archimedeanRepresentation σ π hm (ι x.val) v) =
        (Langlands.Whittaker.standardCharacter ψv r x : ℂ) * ℓ v)
    (hne : ∃ v, ℓ (jY (A false v)) ≠ 0) :
    ∃ s : ℂ, ∀ v, ℓ (jY (A true v)) = s * ℓ (jY (A false v)) := by
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  have hiK : Continuous toK :=
    continuous_subtype_val.comp (continuous_matrixUnitaryToCompact 𝕜 n)
  let pair := (A false).prod (A true)
  let j₂ := pairedEmbedding j
  let D₂ (a : EnvelopingAlgebra F n) (z : Z × Z) := (D a z.1, D a z.2)
  let e := j₂.comp pair
  let W := LinearMap.range pair
  let C := (LinearMap.range e).topologicalClosure
  let : CompleteSpace C := (LinearMap.range e).isClosed_topologicalClosure.completeSpace_coe
  have hK (k : K) (v : V) : e (κ k v) = P∞ (toK k) (e v) := by
    apply (WithLp.equiv 2 (E × E)).injective
    exact Prod.ext (hAK false k v) (hAK true k v)
  have hD (X : M) (v : V) : pair (d (1 ⊗ₜ[ℝ] X) v) =
      D₂ (envelopingGenerator F n (complexify F n (L X))) (pair v) :=
    Prod.ext (hAD false X v) (hAD true X v)
  have hcoeff₂ := pairedCoefficients U j D hcoeff
  have hstable : ∀ g (x : C), P∞ g x ∈ C := by
    have he : LinearMap.range e = W.map j₂ := LinearMap.range_comp pair j₂
    have hp := preservesImageClosure_of_coefficients (pairedAction U) j₂ W D₂ hcoeff₂
      ι a L ha han hder (fun X z hz => by
        obtain ⟨v, rfl⟩ := hz
        exact ⟨d (1 ⊗ₜ[ℝ] X) v, hD X v⟩)
      toK (exists_unitary_point_mem_connectedComponent (𝕜 := 𝕜) (m := Fin n)) (by
        intro k ⟨z, hz⟩
        obtain ⟨v, rfl⟩ := hz
        exact ⟨⟨pair (κ k v), LinearMap.mem_range_self pair _⟩, (hK k v).symm⟩)
    intro g x
    change P∞ g x.val ∈ (LinearMap.range e).topologicalClosure
    rw [he]
    exact hp g x (he ▸ x.property)
  have hs₂ (z : Z × Z) : Langlands.Archimedean.IsSmoothVector I P∞ (j₂ z) :=
    isSmoothVector_placeAction (pairedAction U) ι hι (pairedEmbedding_smooth U j hs z)
  have hD₂ := placeAction_realGeneratorCompatibility (pairedAction U) ι j₂ D₂
    hcoeff₂ a L ha han hder hs₂
  let R := invariantSubmoduleRepresentation P∞ C hstable
  let J := rangeClosureEmbedding e
  have hGK : IsGKHilbertRealization toK κ d R J :=
    gkHilbertClosure M Mˣ K toK hiK V κ d H₂ P∞ e hstable hirr hadm hfin
      ((pairedEmbedding_injective j hj).comp (fun _ _ h => hA (congrArg Prod.fst h)))
      (isContinuousRepresentation_placeAction (pairedAction U) ι hι.continuous
        (pairedAction_continuous U hcont))
      (fun _ => pairedAction_inner U hunit _) hK (fun v => hs₂ (pair v))
      (fun X v => (congrArg j₂ (hD X v)).trans (hD₂ X (pair v)))
  let : Nontrivial V := hirr.1
  obtain ⟨sample, hsample⟩ := exists_ne (0 : V)
  let hπ (g : ArchimedeanGL F n) := hunit (infiniteCoordinateInclusion F n g)
  let jS : V →ₗ[ℂ] Langlands.Archimedean.smoothVectors I R :=
    J.codRestrict _ hGK.2.2.2.2.2.2.2.2.1
  have hform (t : Bool) : ∃ l : Langlands.Archimedean.smoothVectors I R →ₗ[ℂ] ℂ,
      IsWhittakerFunctional I R (Langlands.GeneralLinear.upperUnipotent n 𝕜)
        (Langlands.Whittaker.standardCharacter ψv r) l ∧
      l.comp jS = ℓ.comp (jY.comp (A t)) := by
    let pr : H₂ →L[ℂ] E := if t then WithLp.sndL 2 ℂ E E else WithLp.fstL 2 ℂ E E
    let P := pr.comp C.subtypeL
    have hP (g : Mˣ) (v : C) : P (R g v) = π (ι g) (P v) := by
      cases t <;> rfl
    have hPr (v : V) : P (J v) = j (A t v) := by
      cases t <;> rfl
    obtain ⟨B, hB⟩ := hfix t
    have hPB (v : C) : P v ∈ fixedSubspace σ B.toSubgroup := by
      refine (rangeClosureEmbedding_denseRange e).induction_on v ?_ ?_
      · exact (isClosed_fixedSubspace σ B.toSubgroup).preimage P.continuous
      · intro w
        rw [hPr]
        exact hB w
    obtain ⟨N, hN⟩ := exists_fixedDerivativeMap_of_gkHilbertRealization R π σ ι p c B.toSubgroup
      toK hiK κ d J hGK hπ hm hcentral hsplit hc hp P hP hPB sample hsample
      (by rw [hPr]; exact hs (A t sample))
    obtain ⟨f, hf, he⟩ := hℓ B
    let m := ofFixedDerivativeMap σ π hm B.val R N
    have hmj (v : V) : m (jS v) = jY (A t v) := by
      apply Subtype.ext
      apply Subtype.ext
      change (m (jS v)).val.val = (jY (A t v)).val.val
      rw [ofFixedDerivativeMap_val, hN, LinearEquiv.apply_symm_apply, hjY]
      exact hPr v
    exact ⟨ℓ.comp m, isWhittakerFunctional_comp_ofFixedDerivativeMap σ π hm B.val
      R N ι P hP hN _ _ ℓ f hf he hwhit, LinearMap.ext (fun v => congrArg ℓ (hmj v))⟩
  obtain ⟨ℓ₀, hw₀, he₀⟩ := hform false
  obtain ⟨ℓ₁, hw₁, he₁⟩ := hform true
  have hn : ℓ.comp (jY.comp (A false)) ≠ 0 := by
    obtain ⟨v, hv⟩ := hne
    exact fun he => hv (LinearMap.congr_fun he v)
  obtain ⟨s, hs⟩ := proportional_whittakerRestrictions_of_unitaryUniqueness hUnique r R
    hGK.1 hGK.2.2.1 hGK.2.1 hGK.2.2.2.1 ψv ℓ₀ ℓ₁ hw₀ hw₁ jS (he₀.symm ▸ hn)
  have he := he₁.symm.trans (hs.trans (congrArg (s • ·) he₀))
  exact ⟨s, fun v => LinearMap.congr_fun he v⟩

end Comparison

section ArchimedeanPlaces

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (U : AdelicGL F (r + 1) →* (E →L[ℂ] E)) (j : Z →ₗ[ℂ] E)

local notation "n" => r + 1
local notation "σ" => finiteHilbertAction F n U
local notation "π" => infiniteHilbertAction F n U
local notation "hm" => hilbertCoordinateActions_commute F n U
local notation "Y" => Vectors (A := ArchimedeanMatrix F n) σ π hm

set_option maxHeartbeats 45000 in
/-- Compare two embeddings of the same real place module using the actual place chart. -/
theorem proportional_mixedWhittaker_of_realEmbeddings
    (hUnique : UnitaryWhittakerMultiplicityOneOver.{uE} ℝ)
    (hj : Function.Injective j) (hcont : IsContinuousRepresentation U)
    (hunit : ∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y)
    (hs : ∀ z, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n) π (j z))
    (D : EnvelopingAlgebra F n → Z → Z)
    (hcoeff : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j D)
    (w : {v : InfinitePlace F // InfinitePlace.IsReal v})
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (d : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hirr : IsIrreducibleGKModule κ d) (hadm : IsAdmissibleGKModule κ)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector κ v)
    (A : Bool → V →ₗ[ℂ] Z) (hA : Function.Injective (A false))
    (hAK : ∀ t k v, j (A t (κ k v)) = placeAction U (realPlaceGL F n w) (Unitary.toUnits k) (j (A t v)))
    (hAD : ∀ t X v, A t (d (1 ⊗ₜ[ℝ] X) v) =
      D (envelopingGenerator F n (complexify F n (realPlaceLieInclusion F n w X))) (A t v))
    (hfix : ∀ t, ∃ B : CompactOpenSubgroup (FiniteAdelicGL F n),
        ∀ v, j (A t v) ∈ fixedSubspace σ B.toSubgroup)
    (jY : Z →ₗ[ℂ] Y) (hjY : ∀ z, (jY z).val.val = j z)
    (ψv : UnitaryAdditiveCharacter ℝ)
    (ℓ : Y →ₗ[ℂ] ℂ) (hℓ : IsContinuousAtEachLevel σ π hm ℓ)
    (hwhit : ∀ x : Langlands.GeneralLinear.upperUnipotent n ℝ, ∀ v : Y,
      ℓ (archimedeanRepresentation σ π hm (realPlaceGL F n w x.val) v) =
        (Langlands.Whittaker.standardCharacter ψv r x : ℂ) * ℓ v)
    (hne : ∃ v, ℓ (jY (A false v)) ≠ 0) :
    ∃ s : ℂ, ∀ v, ℓ (jY (A true v)) = s * ℓ (jY (A false v)) := by
  exact proportional_mixedWhittaker_of_pairedEmbeddings (F := F) (r := r) (𝕜 := ℝ)
    (V := V) (Z := Z) (E := E) U j (realPlaceGL F n w)
    hUnique hj hcont hunit hs D hcoeff (contMDiff_realPlaceGL w)
    (realPlaceMatrix w) (realPlaceLieInclusion F n w)
    (fun g => (realPlaceGL_val w g).symm)
    (fun f => analyticAt_realPlaceRestriction w (coordinateExtension F n f))
    (fderiv_realPlaceRestriction w)
    (realPlaceGLProjection w) (realPlaceGLComplement w)
    (realPlaceGLComplement_commute w) (realPlaceGLComplement_split w)
    (contMDiff_realPlaceGLComplement w) (contMDiff_realPlaceGLProjection w)
    κ d hirr hadm hfin A hA hAK hAD hfix jY hjY ψv ℓ hℓ hwhit hne

set_option maxHeartbeats 45000 in
/-- Compare two embeddings of the same complex place module using the actual place chart. -/
theorem proportional_mixedWhittaker_of_complexEmbeddings
    (hUnique : UnitaryWhittakerMultiplicityOneOver.{uE} ℂ)
    (hj : Function.Injective j) (hcont : IsContinuousRepresentation U)
    (hunit : ∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y)
    (hs : ∀ z, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n) π (j z))
    (D : EnvelopingAlgebra F n → Z → Z)
    (hcoeff : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j D)
    (w : {v : InfinitePlace F // InfinitePlace.IsComplex v})
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (d : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hirr : IsIrreducibleGKModule κ d) (hadm : IsAdmissibleGKModule κ)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector κ v)
    (A : Bool → V →ₗ[ℂ] Z) (hA : Function.Injective (A false))
    (hAK : ∀ t k v, j (A t (κ k v)) = placeAction U (complexPlaceGL F n w) (Unitary.toUnits k) (j (A t v)))
    (hAD : ∀ t X v, A t (d (1 ⊗ₜ[ℝ] X) v) =
      D (envelopingGenerator F n (complexify F n (complexPlaceLieInclusion F n w X))) (A t v))
    (hfix : ∀ t, ∃ B : CompactOpenSubgroup (FiniteAdelicGL F n),
        ∀ v, j (A t v) ∈ fixedSubspace σ B.toSubgroup)
    (jY : Z →ₗ[ℂ] Y) (hjY : ∀ z, (jY z).val.val = j z)
    (ψv : UnitaryAdditiveCharacter ℂ)
    (ℓ : Y →ₗ[ℂ] ℂ) (hℓ : IsContinuousAtEachLevel σ π hm ℓ)
    (hwhit : ∀ x : Langlands.GeneralLinear.upperUnipotent n ℂ, ∀ v : Y,
      ℓ (archimedeanRepresentation σ π hm (complexPlaceGL F n w x.val) v) =
        (Langlands.Whittaker.standardCharacter ψv r x : ℂ) * ℓ v)
    (hne : ∃ v, ℓ (jY (A false v)) ≠ 0) :
    ∃ s : ℂ, ∀ v, ℓ (jY (A true v)) = s * ℓ (jY (A false v)) := by
  exact proportional_mixedWhittaker_of_pairedEmbeddings (F := F) (r := r) (𝕜 := ℂ)
    (V := V) (Z := Z) (E := E) U j (complexPlaceGL F n w)
    hUnique hj hcont hunit hs D hcoeff (contMDiff_complexPlaceGL w)
    (complexPlaceMatrix w) (complexPlaceLieInclusion F n w)
    (fun g => (complexPlaceGL_val w g).symm)
    (fun f => analyticAt_complexPlaceRestriction w (coordinateExtension F n f))
    (fderiv_complexPlaceRestriction w)
    (complexPlaceGLProjection w) (complexPlaceGLComplement w)
    (complexPlaceGLComplement_commute w) (complexPlaceGLComplement_split w)
    (contMDiff_complexPlaceGLComplement w) (contMDiff_complexPlaceGLProjection w)
    κ d hirr hadm hfin A hA hAK hAD hfix jY hjY ψv ℓ hℓ hwhit hne

end ArchimedeanPlaces

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
