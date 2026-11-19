import Langlands.HarmonicAnalysis.AlgebraicIntegrand
import Langlands.HarmonicAnalysis.AlgebraicIntegral
import Langlands.Representation.Plancherel.CompactIntertwiningParameterContinuity
import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation
import Langlands.Representation.Plancherel.UnramifiedStableLimit

/-! # Polynomial integration of compact test sections -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.HarmonicAnalysis

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

section Integral

variable {Y P V M I : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [AddCommGroup V] [Module ℂ V]
  [Group M] [TopologicalSpace M] {ν : I → M →* ℝ≥0ˣ}

/-- Integrate the finite set of common values before evaluating the parameter. -/
def compactParametricIntegral (measure : Measure Y) (f : Y → P → V)
    (hlc : IsLocallyConstant f) (hc : HasCompactSupport f) : P → V :=
  AlgebraicIntegral.integral measure (compactlySupportedSimpleFunc f hlc hc)

/-- Every algebraic linear test of the integrated family equals its Bochner integral. -/
theorem compactParametricIntegral_spec (measure : Measure Y) [IsFiniteMeasureOnCompacts measure]
    (f : Y → P → V) (hlc : IsLocallyConstant f) (hc : HasCompactSupport f) (z : P)
    (ℓ : V →ₗ[ℂ] ℂ) :
    Integrable (fun x => ℓ (f x z)) measure ∧
      ℓ (compactParametricIntegral measure f hlc hc z) = ∫ x, ℓ (f x z) ∂measure := by
  let s := compactlySupportedSimpleFunc f hlc hc
  have hs := compactlySupportedSimpleFunc_finMeasSupp measure f hlc hc
  let L := ℓ.comp (LinearMap.proj z : (P → V) →ₗ[ℂ] V)
  have hm := hs.map L.map_zero
  exact ⟨hm.integrable, (AlgebraicIntegral.integral_linearMap s hs L).symm.trans
    (AlgebraicIntegral.integral_eq_bochner (s.map L) hm)⟩

/-- Integration preserves polynomiality of the samples of a uniformly locally
constant family with one compact support. -/
theorem isPolynomialOn_compactParametricIntegral (measure : Measure Y)
    {Ω : Set (unramifiedCharacters ν)} (f : Y → Ω → V)
    (hlc : IsLocallyConstant f) (hc : HasCompactSupport f)
    (hpoly : ∀ y, IsPolynomialOn Ω (f y)) :
    IsPolynomialOn Ω (compactParametricIntegral measure f hlc hc) := by
  classical
  let s := compactlySupportedSimpleFunc f hlc hc
  have he : compactParametricIntegral measure f hlc hc =
      fun z => ∑ g ∈ s.range, ((measure (s ⁻¹' {g})).toReal : ℂ) • g z := by
    funext z
    change (AlgebraicIntegral.integral measure s) z = _
    simp only [AlgebraicIntegral.integral, Finset.sum_apply, Pi.smul_apply]
  rw [he]
  apply isPolynomialOn_finset_sum _ _
  intro g hg
  obtain ⟨y, rfl⟩ := SimpleFunc.mem_range.mp hg
  exact (hpoly y).linearMap (((measure (s ⁻¹' {s y})).toReal : ℂ) • LinearMap.id)

end Integral

section Sections

open Aubert.General Induction

variable {G : Type*} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type*} (ν : I → M →* ℝ≥0ˣ) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection) (A : SmoothRep ℂ M)
  (f : CompactInductionPicture h K A)

/-- The extensions of one compact-picture section, as a family of vectors at
each ambient point. -/
def compactSectionFamily (g : G) (z : unramifiedCharacters ν) : A :=
  eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr z A).symm f) g

local notation "E" => compactSectionFamily h hU hδ K hP hK hPK ν hν hr A f

/-- One compact-picture section has a common open right stabilizer throughout
its unramified twists. -/
theorem compactSectionFamily_isLocallyConstant : IsLocallyConstant E := by
  obtain ⟨J, hJ⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  obtain ⟨p, k, rfl⟩ := hPK g
  refine ⟨(fun j : K => ((p : G) * (k : G)) * (j : G)) '' (J : Set K),
    ((isOpenMap_mul_left _).comp K.isOpen.isOpenMap_subtype_val) _ J.isOpen,
    ⟨1, J.one_mem, by simp⟩, ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  funext z
  change E (((p : G) * (k : G)) * (j : G)) z = E ((p : G) * (k : G)) z
  rw [mul_assoc]
  have he := congrArg (fun F : EquivariantFunctions (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A) => F.1 k) (hJ ⟨j, hj⟩)
  change eval _ _ f (k * j) = eval _ _ f k at he
  let T : A →ₗ[ℂ] A := inducingRepresentation h hU
    (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)) p
  have hT (x : K) : E ((p : G) * (x : G)) z = T (eval _ _ f x) :=
    unramifiedLeviInductionCompactEquiv_symm_mul h hU hδ K hP hK hPK ν hν hr z A f p x
  exact (hT (k * j)).trans ((congrArg T he).trans (hT k).symm)

/-- At a fixed point the support of the compact section is independent of the
unramified character. -/
theorem compactSectionFamily_eq_zero_iff (g : G) (z z' : unramifiedCharacters ν) :
    E g z = 0 ↔ E g z' = 0 := by
  obtain ⟨m, v, hm⟩ := unramifiedCompactExtension_eval_factor h hU hδ K hP hK hPK ν hν hr A f g
  have hE (χ : unramifiedCharacters ν) : E g χ = (χ.val m : ℂ) • v := hm χ
  simp only [hE, smul_eq_zero, Units.ne_zero, false_or]

theorem compactSectionFamily_hasCompactSupport {Y : Type*} [TopologicalSpace Y]
    (e : Y → G) (z₀ : unramifiedCharacters ν)
    (hc : HasCompactSupport (fun y => E (e y) z₀)) :
    HasCompactSupport (E ∘ e) := by
  have he (y : Y) : (E ∘ e) y = 0 ↔ E (e y) z₀ = 0 := by
    constructor
    · exact fun hzero => congrFun hzero z₀
    · intro hzero
      funext z
      exact (compactSectionFamily_eq_zero_iff h hU hδ K hP hK hPK ν hν hr A f (e y) z z₀).2
        hzero
  have hs : Function.support (E ∘ e) = Function.support (fun y => E (e y) z₀) :=
    Set.ext fun y => not_congr (he y)
  change IsCompact (closure (Function.support (E ∘ e)))
  rw [hs]
  exact hc

end Sections

section Identity

open GroupScheme

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L)) (hL : IsConnectedReductive L)
  {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]
  {Ω D : Set (unramifiedCharacters (G := rationalPoints L)
    (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W}

include hp hL in
/-- If a linear image of one input agrees with a polynomial family on a
nonempty open part of the original domain, it agrees throughout the selected
regular region. -/
theorem continuedOperator_map_eq_polynomial_of_eqOn
    (p : RationalOperatorContinuationData Ω A)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (E : W →ₗ[ℂ] X) (v : V)
    (B : unramifiedCharacters (G := rationalPoints L)
      (fun ψ => (rationalNormCharacters L ψ).toMul) → X)
    (hB : IsPolynomialOn Set.univ (fun z => B z.val))
    (hEB : ∀ z (hz : z ∈ D), E (A ⟨z, hDΩ hz⟩ v) = B z) (z : p.regularRegion) :
    E (p.continuedOperator z v) = B z.val := by
  have hpoly := ((p.polynomial v).linearMap E).sub (hB.regular_smul p.denominator)
  have he := rationalUnramifiedPolynomial_eq_zero_of_isOpen L hp hL hD hne
    (show D ⊆ Set.univ from Set.subset_univ _)
    (fun w => E (p.numerator w.val v) - p.denominator.val w.val • B w.val) hpoly (by
      intro w hw
      change E (p.numerator w v) - p.denominator.val w • B w = 0
      rw [LinearMap.congr_fun (p.clears ⟨w, hDΩ hw⟩) v, LinearMap.smul_apply]
      change E (p.denominator.val w • A ⟨w, hDΩ hw⟩ v) - p.denominator.val w • B w = 0
      rw [map_smul, hEB w hw, sub_self])
    ⟨z.val, Set.mem_univ _⟩
  change E (p.numerator z.val v) - p.denominator.val z.val • B z.val = 0 at he
  change E ((p.denominator.val z.val)⁻¹ • p.numerator z.val v) = B z.val
  rw [map_smul, sub_eq_zero.mp he, smul_smul, inv_mul_cancel₀ z.property, one_smul]

end Identity

end Langlands.Plancherel
