import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances
import Langlands.Global.AdelicEisensteinContinuationAnchors
import Langlands.Global.AdelicEisensteinGenericInjectivityStatement

/-! # Finite-range Eisenstein injectivity on the convergence anchor filter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.EisensteinJet

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (root : ParabolicRootPresentation p l a)
  [Mono root.data.i.hom.hom.left] [Fintype (relativeWeylGroup root.data.i)]
  [Mono (CommGroupScheme.groupHom root.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus root.data.T.toGrp)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "Points" => AdelicGroupPoints F G
local notation "Parameters" => ComplexCharacterParameter F P

variable {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

set_option quotPrecheck false in
local notation "IsSection" => IsAutomorphicFunctionOn F G hsmooth hcalc
  (parabolicQuotientSubgroup F p iU l) (K.comap (ofInfinite F G).toMonoidHom) rho

include hN hrho in
set_option maxHeartbeats 700000 in
private theorem exists_pointwise_continuation
    {m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] Parameters)
    (hcont : EisensteinMeromorphicContinuationStatement.{u}) (hG : IsConnectedReductive G)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hmax : IsMaximalCompactSubgroup F G K)
    (φ : Points → ℂ) (hφ : IsSection φ) :
    ∃ (E : Parameters → Points → ℂ) (D : Set Parameters) (R : ℝ),
      (∀ t, root.IsRegularParameter hA hT R t → E t = hK.eisensteinSeries φ t) ∧
      ∀ g, IsMeromorphicInCoordinatesOn (fun t => E t g) D := by
  let : FiniteDimensional ℂ Parameters := LinearMap.finiteDimensional_of_surjective
    (V := Fin m → ℂ) (V₂ := Parameters)
    e.toLinearMap (LinearMap.range_eq_top.mpr e.surjective)
  obtain ⟨E, ⟨R, hR⟩, hlocal⟩ :=
    hcont F G P M U A p iU l a root hA hT hG hU K hK rho hN hrho hsmooth hcalc φ hmax hφ
  have hdata (t₀ : Fin m → ℂ) :
      HasLocalMeromorphicData (fun (g : Points) t => E (e t) g) t₀ := by
    obtain ⟨W, ht₀, T, L, _, f, domain, hmer, hf⟩ := hlocal m e t₀
    refine hasLocalMeromorphicData_of_isMeromorphicOn hmer
      (UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho T L) ?_ ht₀
    intro t ht g
    rw [UniformGrowthFrechetSpace.evalCLM_apply, (hf t ht).1]
  obtain ⟨domain, hdomain⟩ := exists_isMeromorphicOn_of_local hdata
  refine ⟨E, e '' domain, R, hR, fun g => isMeromorphicInCoordinatesOn_of_coordinates e ?_⟩
  rw [e.injective.preimage_image]
  exact hdomain g

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
private theorem series_injective_of_basis_relations
    {V : Type*} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (j : V →ₗ[ℂ] (Points → ℂ)) (hj : Function.Injective j)
    (b : Module.Basis (Fin k) ℂ V) (t : Parameters)
    (hspan : Submodule.span ℂ (Set.range (fun i => j (b i))) ≤ hK.compactMajorantSections t)
    (hrel : ∀ c : Fin k → ℂ,
      (∀ g, ∑ i, c i * hK.eisensteinSeries (j (b i)) t g = 0) →
      ∀ g, ∑ i, c i * j (b i) g = 0) :
    Function.Injective (fun v : V => hK.eisensteinSeries (j v) t) := by
  let j' := j.codRestrict (hK.compactMajorantSections t) fun v => by
    have heq := congrArg j (b.sum_repr v)
    rw [map_sum] at heq
    rw [← heq]
    apply hspan
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let E := (hK.eisensteinSeriesLinear t).comp j'
  change Function.Injective E
  apply LinearMap.ker_eq_bot.mp
  rw [eq_bot_iff]
  intro v hv
  have hvE : E v = 0 := hv
  have hterm (i : Fin k) (g : Points) :
      E (b i) g = hK.eisensteinSeries (j (b i)) t g := rfl
  have he (g : Points) : ∑ i, b.repr v i * hK.eisensteinSeries (j (b i)) t g = 0 := by
    have hx := congrArg (fun w => E w g) (b.sum_repr v)
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hvE, Pi.zero_apply, hterm] using hx
  have hjv : j v = 0 := by
    funext g
    have hx := congrArg (fun w => j w g) (b.sum_repr v)
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hrel (fun i => b.repr v i) he g] using hx.symm
  exact hj (hjv.trans (map_zero j).symm)

include hN hrho in
set_option maxHeartbeats 1200000 in
/-- Meromorphic continuation and generic injectivity give ordinary convergence-region
injectivity on any finite-dimensional space of actual inducing sections. -/
theorem eventually_eisensteinSeries_injective_of_genericInjectivity
    {m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] Parameters)
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hGI : EisensteinGenericInjectivityStatement.{u}) (hG : IsConnectedReductive G)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hmax : IsMaximalCompactSubgroup F G K)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (j : V →ₗ[ℂ] (Points → ℂ)) (hj : Function.Injective j) (hV : ∀ v, IsSection (j v)) :
    ∀ᶠ (t : Fin m → ℂ) in eisensteinConvergenceAnchorFilter root hA hT e,
      Function.Injective (fun v : V => hK.eisensteinSeries (j v) (e t)) := by
  classical
  let b := Module.finBasis ℂ V
  let φ (i : Fin (Module.finrank ℂ V)) := j (b i)
  have hφ (i : Fin (Module.finrank ℂ V)) : IsSection (φ i) := hV (b i)
  choose E D R hR hmer using fun i => exists_pointwise_continuation root hA hT hK
    rho hN hrho hsmooth hcalc e hcont hG hU hmax (φ i) (hφ i)
  let domain := ⋂ i, D i
  have hdomain : IsOpenDenseInCoordinates domain :=
    isOpenDenseInCoordinates_iInter (fun i => (hmer i 1).isOpenDenseInCoordinates)
  have hcommon (i : Fin (Module.finrank ℂ V)) (g : Points) :
      IsMeromorphicInCoordinatesOn (fun t => E i t g) domain :=
    (hmer i g).congr_mono hdomain (iInter_subset D i) (fun _ _ => rfl)
  obtain ⟨O, hOo, hOd, hdet⟩ := hGI F G P M U A p iU l a root hA hT hG hU K hK
    rho hsmooth hcalc hmax hrho (Fin (Module.finrank ℂ V)) φ hφ E domain hcommon
    (fun i => ⟨R i, hR i⟩) m e
  obtain ⟨R₀, hmajor⟩ := hK.exists_regular_compactMajorantSections root hA hT hG hU hmax
    rho hrho hsmooth hcalc e φ hφ
  obtain ⟨R₁, hR₁⟩ := (Set.finite_range R).bddAbove
  apply (eventually_convergenceAnchorFilter_iff _ _).mpr
  refine ⟨max R₀ R₁, O ∩ e ⁻¹' domain, hOo.inter (hdomain m e).1,
    hOd.inter_of_isOpen_left (hdomain m e).2 hOo, ?_⟩
  intro t ht
  have hreg₀ : root.IsRegularParameter hA hT R₀ (e t) :=
    fun α hα => (le_max_left _ _).trans_lt (ht.1 α hα)
  have hreg₁ (i : Fin (Module.finrank ℂ V)) : root.IsRegularParameter hA hT (R i) (e t) :=
    fun α hα => ((hR₁ (Set.mem_range_self i)).trans (le_max_right _ _)).trans_lt (ht.1 α hα)
  refine series_injective_of_basis_relations hK j hj b (e t) (hmajor t hreg₀) ?_
  intro c hc
  exact hdet t ht.2.1 ht.2.2 c fun g => by
    simpa only [hR _ _ (hreg₁ _)] using hc g

end Langlands.Global.EisensteinJet
