import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Smooth.SmallRealizationProof

/-!
# Finite-dimensional fixed vectors of irreducible compact-coefficient representations

Bernstein--Zelevinsky (1976), the irreducible case of Corollary 2.41, page 26, for an
arbitrary topological group `G` with a left Haar measure: an irreducible smooth complex
representation all of whose smooth-dual coefficients have compact support has
finite-dimensional fixed vectors under every open subgroup with compact underlying set.
The proof follows the first step of the proof of 2.40 a) ⇒ b), averages functionals over
the compact open subgroup and uses only left invariance of the Haar measure.
-/

noncomputable section

namespace Langlands.CompactCoefficientClass

open MeasureTheory Hecke
open HarmonicAnalysis (SchwartzBruhat)

universe uG uV

section Coefficient

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem apply_eq_of_mem_fixedVectors {ρ : Representation ℂ G V} {K : Subgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ K) {k : G} (hk : k ∈ K) : ρ k v = v :=
  hv ⟨k, hk⟩

/-- The inverse coefficient `g ↦ ℓ (ρ g⁻¹ v)` of a smooth vector is locally constant. -/
theorem inverseCoefficient_locallyConstant (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (ℓ : Module.Dual ℂ V) (v : V) : IsLocallyConstant (fun g : G => ℓ (ρ g⁻¹ v)) :=
  ((orbitMap_locallyConstant ρ (hρ v)).comp_continuous continuous_inv).comp ℓ

/-- The inverse coefficient against a smooth dual vector has compact support. -/
theorem inverseCoefficient_hasCompactSupport {ρ : Representation ℂ G V}
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (v : V) :
    HasCompactSupport (fun g : G => ℓ (ρ g⁻¹ v)) :=
  (hc v ℓ hℓ).comp_homeomorph (Homeomorph.inv G)

/-- The inverse coefficients `g ↦ ℓ (ρ g⁻¹ v)` against a smooth dual vector, as test
functions depending linearly on `v`. -/
def inverseCoefficient (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) : V →ₗ[ℂ] SchwartzBruhat G where
  toFun v := ⟨fun g => ℓ (ρ g⁻¹ v), inverseCoefficient_locallyConstant ρ hρ ℓ v,
    inverseCoefficient_hasCompactSupport hc hℓ v⟩
  map_add' v w := by
    apply Subtype.ext
    funext g
    simp
  map_smul' c v := by
    apply Subtype.ext
    funext g
    simp

variable {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}
  {hc : HasCompactSmoothDualCoefficients ρ} {ℓ : Module.Dual ℂ V}
  {hℓ : IsSmoothVector ρ.dual ℓ}

@[simp]
theorem inverseCoefficient_apply (v : V) (g : G) :
    inverseCoefficient ρ hρ hc ℓ hℓ v g = ℓ (ρ g⁻¹ v) := rfl

/-- Translating the vector translates the inverse coefficient on the left. -/
theorem inverseCoefficient_apply_rho (h : G) (v : V) :
    inverseCoefficient ρ hρ hc ℓ hℓ (ρ h v) =
      TestFunction.leftTranslate h (inverseCoefficient ρ hρ hc ℓ hℓ v) := by
  apply Subtype.ext
  funext g
  change ℓ (ρ g⁻¹ (ρ h v)) = ℓ (ρ (h⁻¹ * g)⁻¹ v)
  rw [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

/-- For a `K`-invariant functional and a `K`-fixed vector the inverse coefficient is
bi-`K`-invariant. -/
theorem inverseCoefficient_mem_biInvariant {K : Subgroup G}
    (hℓK : ∀ k ∈ K, ∀ y, ℓ (ρ k y) = ℓ y) {v : V} (hv : v ∈ fixedVectors ρ K) :
    inverseCoefficient ρ hρ hc ℓ hℓ v ∈ TestFunction.biInvariant K K := by
  constructor
  · intro k x
    change ℓ (ρ ((k : G) * x)⁻¹ v) = ℓ (ρ x⁻¹ v)
    rw [mul_inv_rev, map_mul, Module.End.mul_apply,
      apply_eq_of_mem_fixedVectors hv (K.inv_mem k.property)]
  · intro k x
    change ℓ (ρ (x * (k : G))⁻¹ v) = ℓ (ρ x⁻¹ v)
    rw [mul_inv_rev, map_mul, Module.End.mul_apply, hℓK _ (K.inv_mem k.property)]

end Coefficient

section DualAverage

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (N : OpenSubgroup G) (hN : IsCompact (N : Set G))

include hρ hN in
theorem dualAverage_integrable (ℓ : Module.Dual ℂ V) (y : V) :
    IntegrableOn (fun k => ℓ (ρ k⁻¹ y)) (N : Set G) μ :=
  ContinuousOn.integrableOn_compact' hN N.isOpen.measurableSet
    (inverseCoefficient_locallyConstant ρ hρ ℓ y).continuous.continuousOn

/-- The normalized average `y ↦ μ(N)⁻¹ ∫_N ℓ (ρ k⁻¹ y) dk` of a functional over `N`. -/
def dualAverage (ℓ : Module.Dual ℂ V) : Module.Dual ℂ V where
  toFun y := (μ.real (N : Set G) : ℂ)⁻¹ * ∫ k in (N : Set G), ℓ (ρ k⁻¹ y) ∂μ
  map_add' y z := by
    simp only [map_add]
    rw [integral_add (dualAverage_integrable μ ρ hρ N hN ℓ y)
      (dualAverage_integrable μ ρ hρ N hN ℓ z), mul_add]
  map_smul' c y := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rw [integral_const_mul]
    ring

theorem dualAverage_apply (ℓ : Module.Dual ℂ V) (y : V) :
    dualAverage μ ρ hρ N hN ℓ y =
      (μ.real (N : Set G) : ℂ)⁻¹ * ∫ k in (N : Set G), ℓ (ρ k⁻¹ y) ∂μ := rfl

/-- On `N`-fixed vectors the average agrees with the original functional. -/
theorem dualAverage_apply_of_fixed (ℓ : Module.Dual ℂ V) {y : V}
    (hy : y ∈ fixedVectors ρ N.toSubgroup) : dualAverage μ ρ hρ N hN ℓ y = ℓ y := by
  rw [dualAverage_apply, setIntegral_congr_fun (g := fun _ => ℓ y) N.isOpen.measurableSet
    (fun k hk => by
      simp only
      rw [apply_eq_of_mem_fixedVectors hy (N.toSubgroup.inv_mem hk)]),
    setIntegral_const, Complex.real_smul,
    inv_mul_cancel_left₀ (HeckeAlgebra.compactOpen_complex_mass_ne_zero μ N hN)]

/-- The average is invariant under `N`. -/
theorem dualAverage_apply_rho (ℓ : Module.Dual ℂ V) {n : G} (hn : n ∈ N) (y : V) :
    dualAverage μ ρ hρ N hN ℓ (ρ n y) = dualAverage μ ρ hρ N hN ℓ y := by
  rw [dualAverage_apply, dualAverage_apply,
    ← integral_indicator N.isOpen.measurableSet, ← integral_indicator N.isOpen.measurableSet,
    ← integral_mul_left_eq_self (μ := μ)
      ((N : Set G).indicator fun k => ℓ (ρ k⁻¹ (ρ n y))) n]
  congr 2
  funext x
  by_cases hx : x ∈ (N : Set G)
  · have hnx : n * x ∈ (N : Set G) := N.toSubgroup.mul_mem hn hx
    rw [Set.indicator_of_mem hnx, Set.indicator_of_mem hx, mul_inv_rev, map_mul,
      Module.End.mul_apply, ← Module.End.mul_apply (ρ n⁻¹), ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  · have hnx : n * x ∉ (N : Set G) := fun h => hx (by
      simpa using N.toSubgroup.mul_mem (N.toSubgroup.inv_mem hn) h)
    rw [Set.indicator_of_notMem hnx, Set.indicator_of_notMem hx]

/-- The average is a smooth vector of the algebraic dual action. -/
theorem dualAverage_isSmoothVector (ℓ : Module.Dual ℂ V) :
    IsSmoothVector ρ.dual (dualAverage μ ρ hρ N hN ℓ) := by
  refine ⟨N, fun k => ?_⟩
  apply LinearMap.ext
  intro y
  change dualAverage μ ρ hρ N hN ℓ (ρ ((k : G)⁻¹) y) = dualAverage μ ρ hρ N hN ℓ y
  exact dualAverage_apply_rho μ ρ hρ N hN ℓ (N.toSubgroup.inv_mem k.property) y

/-- An `N`-invariant functional is unchanged by the projection onto `N`-fixed vectors. -/
theorem apply_heckeAction_normalizedIndicator {Λ : Module.Dual ℂ V}
    (hΛ : ∀ k ∈ N, ∀ y, Λ (ρ k y) = Λ y) (y : V) :
    Λ (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ N hN) y) = Λ y := by
  rw [heckeAction_apply, integratedAction_dual]
  have hpt : (fun g => (HeckeAlgebra.toTestFunction μ
      (HeckeAlgebra.normalizedIndicator μ N hN)) g * Λ (ρ g y)) =
      (N : Set G).indicator fun _ => (μ.real (N : Set G) : ℂ)⁻¹ * Λ y := by
    funext g
    change HeckeAlgebra.normalizedIndicator μ N hN g * Λ (ρ g y) = _
    rw [HeckeAlgebra.normalizedIndicator_apply]
    by_cases hg : g ∈ (N : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, hΛ g hg, mul_one]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero, zero_mul]
  rw [hpt, integral_indicator N.isOpen.measurableSet, setIntegral_const, Complex.real_smul,
    mul_inv_cancel_left₀ (HeckeAlgebra.compactOpen_complex_mass_ne_zero μ N hN)]

end DualAverage

section FixedExtension

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (N : OpenSubgroup G) (hN : IsCompact (N : Set G))

/-- The smooth extension `y ↦ μ(N)⁻¹ ∫_N ℓ (P_N (ρ k⁻¹ y)) dk` of a functional `ℓ` on the
`N`-fixed vectors. -/
def fixedExtension (ℓ : Module.Dual ℂ (fixedVectors ρ N.toSubgroup)) : Module.Dual ℂ V :=
  dualAverage μ ρ hρ N hN (ℓ ∘ₗ fixedProjection μ ρ hρ N hN)

/-- The extension of `ℓ` is `ℓ ∘ P_N`. -/
theorem fixedExtension_apply (ℓ : Module.Dual ℂ (fixedVectors ρ N.toSubgroup)) (y : V) :
    fixedExtension μ ρ hρ N hN ℓ y = ℓ (fixedProjection μ ρ hρ N hN y) := by
  have hinv : ∀ k ∈ N, ∀ z, fixedExtension μ ρ hρ N hN ℓ (ρ k z) =
      fixedExtension μ ρ hρ N hN ℓ z :=
    fun k hk z => dualAverage_apply_rho μ ρ hρ N hN _ hk z
  rw [← apply_heckeAction_normalizedIndicator μ ρ hρ N hN hinv y,
    ← fixedProjection_apply μ ρ hρ N hN y, fixedExtension,
    dualAverage_apply_of_fixed μ ρ hρ N hN _ (fixedProjection μ ρ hρ N hN y).property,
    LinearMap.comp_apply, fixedProjection_fixed]

theorem fixedExtension_isSmoothVector (ℓ : Module.Dual ℂ (fixedVectors ρ N.toSubgroup)) :
    IsSmoothVector ρ.dual (fixedExtension μ ρ hρ N hN ℓ) :=
  dualAverage_isSmoothVector μ ρ hρ N hN _

include μ hρ hN in
/-- Bernstein--Zelevinsky (1976), Corollary 2.41 for irreducible representations: an
irreducible smooth representation with compact smooth-dual coefficients has
finite-dimensional fixed vectors under every compact open subgroup. -/
theorem finiteDimensional_fixedVectors (hirr : ρ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients ρ) :
    FiniteDimensional ℂ (fixedVectors ρ N.toSubgroup) := by
  classical
  by_cases h0 : fixedVectors ρ N.toSubgroup = ⊥
  · rw [h0]
    infer_instance
  obtain ⟨ξ, hξN, hξ0⟩ := (Submodule.ne_bot_iff _).mp h0
  let P := fixedProjection μ ρ hρ N hN
  let u : G → fixedVectors ρ N.toSubgroup := fun g => P (ρ g ξ)
  have hspan : Submodule.span ℂ (Set.range u) = ⊤ := by
    have hrange : Set.range u = P '' Set.range (fun g => ρ g ξ) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, span_range_orbit_eq_top hirr hξ0, Submodule.map_top,
      LinearMap.range_eq_top]
    intro v
    exact ⟨v, fixedProjection_fixed μ ρ hρ N hN v⟩
  obtain ⟨b, hbu, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range u)
  let B : Module.Basis b ℂ (fixedVectors ρ N.toSubgroup) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  let Λ := fixedExtension μ ρ hρ N hN B.sumCoords
  have hsupp : HasCompactSupport (matrixCoefficient ρ Λ ξ) :=
    hc ξ Λ (fixedExtension_isSmoothVector μ ρ hρ N hN _)
  have hcoef : ∀ g, matrixCoefficient ρ Λ ξ g = B.sumCoords (u g) := fun g =>
    fixedExtension_apply μ ρ hρ N hN _ _
  have hu : IsLocallyConstant u := (orbitMap_locallyConstant ρ (hρ ξ)).comp P
  let _ : TopologicalSpace (fixedVectors ρ N.toSubgroup) := ⊥
  have : DiscreteTopology (fixedVectors ρ N.toSubgroup) := ⟨rfl⟩
  have hfin : (u '' tsupport (matrixCoefficient ρ Λ ξ)).Finite :=
    (hsupp.isCompact.image hu.continuous).finite_of_discrete
  have hbfin : b.Finite := by
    refine hfin.subset fun x hx => ?_
    obtain ⟨g, rfl⟩ := hbu hx
    refine ⟨g, subset_tsupport _ ?_, rfl⟩
    rw [Function.mem_support, hcoef]
    have hB : B ⟨u g, hx⟩ = u g := Module.Basis.mk_apply hbli _ _
    rw [← hB, B.sumCoords_self_apply]
    exact one_ne_zero
  have : Finite b := hbfin.to_subtype
  exact Module.Finite.of_basis B

end FixedExtension

end Langlands.CompactCoefficientClass
