import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof

/-!
# Lifting property of compact irreducible admissible representations

An invariant Hermitian form, built by integrating one compactly supported
coefficient against Haar measure, produces an equivariant map into any smooth
representation from the integrated Hecke action. Schur's lemma for admissible
irreducible representations makes the composite with a surjection a nonzero
scalar, which yields lifts along every surjection.
-/

noncomputable section

namespace Langlands.CompactSplitting

open MeasureTheory HarmonicAnalysis ComplexConjugate

universe uG uV uW uU

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {U : Type uU} [AddCommGroup U] [Module ℂ U]

section Coefficients

/-- The coefficient `x ↦ ℓ (ρ x⁻¹ v)` with inverted argument. -/
def invCoeff (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V) (v : V) : G → ℂ :=
  fun x => ℓ (ρ x⁻¹ v)

theorem invCoeff_isLocallyConstant (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (ℓ : Module.Dual ℂ V) (v : V) : IsLocallyConstant (invCoeff ρ ℓ v) :=
  ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp ℓ).comp_continuous continuous_inv

theorem invCoeff_continuous (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (ℓ : Module.Dual ℂ V) (v : V) : Continuous (invCoeff ρ ℓ v) :=
  (invCoeff_isLocallyConstant ρ hρ ℓ v).continuous

theorem invCoeff_hasCompactSupport (ρ : Representation ℂ G V)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (v : V) : HasCompactSupport (invCoeff ρ ℓ v) :=
  (hc v ℓ hℓ).comp_homeomorph (Homeomorph.inv G)

/-- The linear map `w ↦ (x ↦ ℓ (ρ x⁻¹ w))` into actual test functions. -/
def testMap (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) : V →ₗ[ℂ] SchwartzBruhat G where
  toFun w := ⟨invCoeff ρ ℓ w, invCoeff_isLocallyConstant ρ hρ ℓ w,
    invCoeff_hasCompactSupport ρ hc hℓ w⟩
  map_add' v w := by
    apply Hecke.TestFunction.ext
    intro x
    change ℓ (ρ x⁻¹ (v + w)) = ℓ (ρ x⁻¹ v) + ℓ (ρ x⁻¹ w)
    rw [map_add, map_add]
  map_smul' c w := by
    apply Hecke.TestFunction.ext
    intro x
    change ℓ (ρ x⁻¹ (c • w)) = c * ℓ (ρ x⁻¹ w)
    rw [map_smul, map_smul, smul_eq_mul]

theorem testMap_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (w : V) (x : G) :
    testMap ρ hρ hc ℓ hℓ w x = ℓ (ρ x⁻¹ w) := rfl

theorem testMap_translate (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (g : G) (w : V) :
    testMap ρ hρ hc ℓ hℓ (ρ g w) =
      Hecke.TestFunction.leftTranslate g (testMap ρ hρ hc ℓ hℓ w) := by
  apply Hecke.TestFunction.ext
  intro x
  rw [Hecke.TestFunction.leftTranslate_apply, testMap_apply, testMap_apply,
    mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

end Coefficients

section Integration

variable [MeasurableSpace G] [BorelSpace G]

/-- The equivariant map `w ↦ ∫ ℓ (ρ x⁻¹ w) σ(x) a dμ(x)`, computed by the
actual integrated Hecke action of `σ`. -/
def liftMap (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (a : W) : ρ.IntertwiningMap σ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ
    { toFun := fun w => Hecke.integratedAction μ σ hσ (testMap ρ hρ hc ℓ hℓ w) a
      map_add' := fun v w => by
        rw [map_add, map_add, LinearMap.add_apply]
      map_smul' := fun c w => by
        rw [map_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
    (fun g w => by
      change Hecke.integratedAction μ σ hσ (testMap ρ hρ hc ℓ hℓ (ρ g w)) a =
        σ g (Hecke.integratedAction μ σ hσ (testMap ρ hρ hc ℓ hℓ w) a)
      rw [testMap_translate]
      exact Hecke.integratedAction_leftTranslate μ σ hσ g _ a)

theorem liftMap_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (a : W) (w : V) :
    liftMap μ ρ hρ hc ℓ hℓ σ hσ a w =
      Hecke.integratedAction μ σ hσ (testMap ρ hρ hc ℓ hℓ w) a := rfl

/-- Intertwiners commute with the construction in the base vector. -/
theorem liftMap_natural (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    {τ : Representation ℂ G U} (hτ : IsSmooth τ) (p : σ.IntertwiningMap τ)
    (a : W) (w : V) :
    p (liftMap μ ρ hρ hc ℓ hℓ σ hσ a w) = liftMap μ ρ hρ hc ℓ hℓ τ hτ (p a) w :=
  Hecke.integratedAction_intertwiner μ hσ hτ p _ a

/-- The Hermitian form `⟨v, w⟩ = ∫ ℓ (ρ x⁻¹ v) * conj (ℓ (ρ x⁻¹ w)) dμ(x)`. -/
def form (μ : Measure G) (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (v w : V) : ℂ :=
  ∫ x, invCoeff ρ ℓ v x * conj (invCoeff ρ ℓ w x) ∂μ

theorem form_integrable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (v w : V) :
    Integrable (fun x => invCoeff ρ ℓ v x * conj (invCoeff ρ ℓ w x)) μ :=
  ((invCoeff_continuous ρ hρ ℓ v).mul
    (Complex.continuous_conj.comp (invCoeff_continuous ρ hρ ℓ w))).integrable_of_hasCompactSupport
    (invCoeff_hasCompactSupport ρ hc hℓ v).mul_right

/-- The form is linear in its first variable. -/
def formLeft (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (w : V) : Module.Dual ℂ V where
  toFun v := form μ ρ ℓ v w
  map_add' u v := by
    unfold form
    rw [← integral_add (form_integrable μ ρ hρ hc hℓ u w)
      (form_integrable μ ρ hρ hc hℓ v w)]
    congr 1
    funext x
    simp only [invCoeff, map_add, add_mul]
  map_smul' c v := by
    unfold form
    rw [smul_eq_mul, RingHom.id_apply, ← integral_const_mul]
    congr 1
    funext x
    simp only [invCoeff, map_smul, smul_eq_mul, mul_assoc]

theorem formLeft_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (w v : V) :
    formLeft μ ρ hρ hc hℓ w v = form μ ρ ℓ v w := rfl

theorem form_invariant (μ : Measure G) [μ.IsMulLeftInvariant]
    (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V) (g : G) (v w : V) :
    form μ ρ ℓ (ρ g v) (ρ g w) = form μ ρ ℓ v w := by
  unfold form
  rw [← integral_mul_left_eq_self
    (fun x => invCoeff ρ ℓ (ρ g v) x * conj (invCoeff ρ ℓ (ρ g w) x)) g]
  congr 1
  funext x
  simp only [invCoeff, mul_inv_rev, map_mul, Module.End.mul_apply,
    Representation.inv_self_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem form_conj (μ : Measure G) (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (v w : V) : conj (form μ ρ ℓ v w) = form μ ρ ℓ w v := by
  unfold form
  rw [← integral_conj]
  congr 1
  funext x
  rw [map_mul, Complex.conj_conj, mul_comm]

omit [Group G] [IsTopologicalGroup G] in
/-- A continuous compactly supported function that is nonzero somewhere has
nonzero `L²` integral against an open-positive measure. -/
theorem integral_mul_conj_ne_zero (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {F : G → ℂ} (hF : Continuous F) (hc : HasCompactSupport F)
    {x : G} (hx : F x ≠ 0) : ∫ y, F y * conj (F y) ∂μ ≠ 0 := by
  have h : (fun y => F y * conj (F y)) = fun y => ((Complex.normSq (F y) : ℝ) : ℂ) := by
    funext y
    exact Complex.mul_conj (F y)
  rw [h, integral_complex_ofReal, Complex.ofReal_ne_zero]
  apply ne_of_gt
  exact (Complex.continuous_normSq.comp hF).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hc.comp_left Complex.normSq_zero) (fun y => Complex.normSq_nonneg (F y))
    (by simpa [Complex.normSq_eq_zero] using hx)

theorem form_self_ne_zero (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) {v : V} (hv : ℓ v ≠ 0) : form μ ρ ℓ v v ≠ 0 := by
  apply integral_mul_conj_ne_zero μ (invCoeff_continuous ρ hρ ℓ v)
    (invCoeff_hasCompactSupport ρ hc hℓ v) (x := 1)
  simpa [invCoeff] using hv

/-- The functional `⟨·, v⟩` is smooth for the algebraic dual action. -/
theorem formLeft_isSmoothVector (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (v : V) :
    IsSmoothVector ρ.dual (formLeft μ ρ hρ hc hℓ v) := by
  obtain ⟨K, hK⟩ := hρ v
  refine ⟨K, fun k => ?_⟩
  apply LinearMap.ext
  intro u
  have hk : ρ (k : G) v = v := hK k
  change form μ ρ ℓ (ρ (k : G)⁻¹ u) v = form μ ρ ℓ u v
  rw [← form_invariant μ ρ ℓ (k : G) (ρ (k : G)⁻¹ u) v, Representation.self_inv_apply, hk]

end Integration

section Lifting

/-- If compact open subgroups are cofinal among open subgroups, every nonzero
vector of a smooth representation is detected by a smooth functional. -/
theorem exists_smooth_functional_ne_zero
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) {v : V} (hv : v ≠ 0) :
    ∃ ℓ : Module.Dual ℂ V, IsSmoothVector ρ.dual ℓ ∧ ℓ v ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  apply smoothBidual_injective_of_compact_cofinal hcof ρ hρ
  rw [map_zero]
  apply Subtype.ext
  apply LinearMap.ext
  intro ℓ
  exact h ℓ.val ℓ.property

variable [MeasurableSpace G] [BorelSpace G]

/-- Lifting along surjections: every intertwiner from a compact irreducible
admissible representation to the target of a surjective intertwiner of smooth
representations factors through it. -/
theorem exists_lift (μ : Measure G) [μ.IsHaarMeasure]
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients ρ)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) {τ : Representation ℂ G U}
    (hτ : IsSmooth τ) (p : σ.IntertwiningMap τ) (hp : Function.Surjective p)
    (φ : ρ.IntertwiningMap τ) :
    ∃ s : ρ.IntertwiningMap σ, p.comp s = φ := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀, hℓ₀v⟩ := exists_smooth_functional_ne_zero hcof ρ hρ.1 hv₀
  set ℓB := formLeft μ ρ hρ.1 hc hℓ₀ v₀ with hℓBdef
  have hℓB : IsSmoothVector ρ.dual ℓB := formLeft_isSmoothVector μ ρ hρ.1 hc hℓ₀ v₀
  set T := liftMap μ ρ hρ.1 hc ℓB hℓB ρ hρ.1 v₀ with hTdef
  obtain ⟨c, hcT, -⟩ := admissibleSchur_scalarEndomorphism ρ hρ hirr T
  have hTc (w : V) : T w = c • w := by
    rw [hcT]
    rfl
  have hc0 : c ≠ 0 := by
    intro hc0
    have hzero : ℓB (T v₀) = 0 := by rw [hTc, hc0, zero_smul, map_zero]
    rw [hTdef, liftMap_apply, Hecke.integratedAction_dual] at hzero
    let F : G → ℂ := fun x => ℓB (ρ x v₀)
    have hF : Continuous F :=
      ((Hecke.orbitMap_locallyConstant ρ (hρ.1 v₀)).comp ℓB).continuous
    have hFc : HasCompactSupport F := hc v₀ ℓB hℓB
    have hF1 : F 1 ≠ 0 := by
      change form μ ρ ℓ₀ (ρ 1 v₀) v₀ ≠ 0
      rw [map_one, Module.End.one_apply]
      exact form_self_ne_zero μ ρ hρ.1 hc hℓ₀ hℓ₀v
    apply integral_mul_conj_ne_zero μ hF hFc hF1
    rw [← hzero]
    congr 1
    funext x
    rw [testMap_apply, mul_comm]
    congr 1
    change conj (form μ ρ ℓ₀ (ρ x v₀) v₀) = form μ ρ ℓ₀ (ρ x⁻¹ v₀) v₀
    rw [form_conj, ← form_invariant μ ρ ℓ₀ x⁻¹ v₀ (ρ x v₀),
      Representation.inv_self_apply]
  obtain ⟨a₀, ha₀⟩ := hp (φ v₀)
  refine ⟨c⁻¹ • liftMap μ ρ hρ.1 hc ℓB hℓB σ hσ a₀, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  change p (c⁻¹ • liftMap μ ρ hρ.1 hc ℓB hℓB σ hσ a₀ w) = φ w
  rw [map_smul, liftMap_natural μ ρ hρ.1 hc ℓB hℓB hσ hτ p, ha₀, liftMap_apply,
    ← Hecke.integratedAction_intertwiner μ hρ.1 hτ φ, ← liftMap_apply, ← hTdef, hTc,
    map_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- Every surjection of smooth representations onto a compact irreducible
admissible representation splits. -/
theorem exists_section (μ : Measure G) [μ.IsHaarMeasure]
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients ρ)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (p : σ.IntertwiningMap ρ)
    (hp : Function.Surjective p) :
    ∃ s : ρ.IntertwiningMap σ, p.comp s = Representation.IntertwiningMap.id ρ :=
  exists_lift μ hcof ρ hρ hirr hc hσ hρ.1 p hp (Representation.IntertwiningMap.id ρ)

end Lifting

end Langlands.CompactSplitting
