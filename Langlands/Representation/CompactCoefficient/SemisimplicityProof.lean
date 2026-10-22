import Langlands.Representation.CompactCoefficient.SemisimplicityStatement
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Representation.SubrepresentationLattice

/-!
# Semisimplicity of smooth representations with compact coefficients

This proves `Langlands.CompactCoefficientSemisimplicityStatement`. The proof
uses only a left Haar measure. For a vector `a₀` outside a subrepresentation
`M`, a smooth functional `ℓ` vanishing on `M` produces the intertwiner
`a ↦ ∫ ℓ(ρ(g⁻¹)a) ρ(g)a₁ dg`; a positivity computation shows that it does not
map into `M`. A Zorn argument then shows that the irreducible
subrepresentations span.
-/

noncomputable section

namespace Langlands

open MeasureTheory HarmonicAnalysis

namespace CompactCoefficientSemisimplicity

universe uG uV

section Averaging

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Averaging over a compact open subgroup is unchanged by translating the
input by an element of that subgroup. -/
theorem averageMap_apply_rho (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (k : K) (v : V) :
    Compact.averageMap ρ hρ K hK (ρ k v) = Compact.averageMap ρ hρ K hK v := by
  have h : Compact.orbit (ρ.comp K.toSubgroup.subtype) (ρ k v) =
      Compact.orbit (ρ.comp K.toSubgroup.subtype) v := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨g * k, ?_⟩
      simp [map_mul, Module.End.mul_apply]
    · rintro ⟨g, rfl⟩
      refine ⟨g * k⁻¹, ?_⟩
      simp [← Module.End.mul_apply, ← map_mul]
  change Compact.orbitMean _ (ρ k v) = Compact.orbitMean _ v
  unfold Compact.orbitMean
  rw [h]

/-- Averaging over a compact open subgroup preserves every subrepresentation. -/
theorem averageMap_mem (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (N : Subrepresentation ρ)
    {v : V} (hv : v ∈ N) : Compact.averageMap ρ hρ K hK v ∈ N := by
  change (Nat.card (Compact.orbit (ρ.comp K.toSubgroup.subtype) v) : ℂ)⁻¹ •
    ∑ᶠ x : Compact.orbit (ρ.comp K.toSubgroup.subtype) v, x.val ∈ N.toSubmodule
  apply N.toSubmodule.smul_mem
  apply finsum_induction (p := fun w => w ∈ N.toSubmodule)
  · exact N.toSubmodule.zero_mem
  · intro a b ha hb
    exact N.toSubmodule.add_mem ha hb
  · rintro ⟨x, g, rfl⟩
    exact N.apply_mem_toSubmodule _ hv

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- A vector outside a subrepresentation is detected by a smooth functional
vanishing on that subrepresentation. -/
theorem exists_smooth_dual_separating (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (N : Subrepresentation ρ) {a : V} (ha : a ∉ N) :
    ∃ ℓ : Module.Dual ℂ V, IsSmoothVector ρ.dual ℓ ∧ (∀ v ∈ N, ℓ v = 0) ∧ ℓ a ≠ 0 := by
  obtain ⟨U, hU⟩ := hρ a
  obtain ⟨K, hKU, hK, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ U
  have haK : a ∈ fixedVectors ρ K.toSubgroup := fun k => hU ⟨k, hKU k.property⟩
  obtain ⟨l, hla, hlN⟩ := Submodule.exists_le_ker_of_notMem (p := N.toSubmodule) ha
  refine ⟨l.comp (Compact.averageMap ρ hρ K hK), ⟨K, ?_⟩, ?_, ?_⟩
  · intro k
    apply LinearMap.ext
    intro v
    change l (Compact.averageMap ρ hρ K hK (ρ ((k : G)⁻¹) v)) =
      l (Compact.averageMap ρ hρ K hK v)
    rw [show ((k : G)⁻¹) = ((k⁻¹ : K) : G) from rfl, averageMap_apply_rho]
  · intro v hv
    exact hlN (averageMap_mem ρ hρ K hK N hv)
  · change l (Compact.averageMap ρ hρ K hK a) ≠ 0
    rw [Compact.averageMap_id ρ hρ K hK a haK]
    exact hla

end Averaging

section Coefficients

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The matrix coefficient `g ↦ ℓ (ρ g v)` of a smooth functional, as a test
function; it is linear in `v`. -/
def coefficientTest (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) : V →ₗ[ℂ] SchwartzBruhat G where
  toFun v := ⟨fun g => ℓ (ρ g v), (Hecke.orbitMap_locallyConstant ρ (hρ v)).comp ℓ,
    hc v ℓ hℓ⟩
  map_add' v w := by
    apply Hecke.TestFunction.ext
    intro g
    simp
  map_smul' c v := by
    apply Hecke.TestFunction.ext
    intro g
    simp

@[simp]
theorem coefficientTest_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (v : V) (g : G) :
    coefficientTest ρ hρ hc hℓ v g = ℓ (ρ g v) := rfl

omit [Group G] [IsTopologicalGroup G] in
/-- Pointwise complex conjugate of a test function. -/
def conjTest (f : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨fun g => starRingEnd ℂ (f g), f.locallyConstant.comp _,
    f.hasCompactSupport.comp_left (map_zero _)⟩

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem conjTest_apply (f : SchwartzBruhat G) (g : G) :
    conjTest f g = starRingEnd ℂ (f g) := rfl

variable [MeasurableSpace G] [BorelSpace G]

/-- The integrated action preserves every subrepresentation. -/
theorem integratedAction_mem (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (N : Subrepresentation ρ)
    (f : SchwartzBruhat G) {v : V} (hv : v ∈ N) :
    Hecke.integratedAction μ ρ hρ f v ∈ N := by
  by_contra h
  obtain ⟨L, hL, hLN⟩ := Submodule.exists_le_ker_of_notMem (p := N.toSubmodule) h
  apply hL
  rw [Hecke.integratedAction_dual]
  have hz : ∀ g, f g * L (ρ g v) = 0 := fun g => by
    rw [hLN (N.apply_mem_toSubmodule g hv), mul_zero]
  simp [hz]

omit [Group G] [IsTopologicalGroup G] in
/-- A continuous compactly supported function `F` with `∫ conj F * F = 0`
vanishes identically. -/
theorem eq_zero_of_integral_conj_mul_self (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {F : G → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (h : ∫ g, starRingEnd ℂ (F g) * F g ∂μ = 0) (x : G) : F x = 0 := by
  have hreal : ∫ g, ‖F g‖ ^ 2 ∂μ = 0 := by
    have h' : ∫ g, ((‖F g‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
      rw [← h]
      congr 1
      funext g
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [integral_complex_ofReal] at h'
    exact_mod_cast h'
  by_contra hx
  have hpos : 0 < ∫ g, ‖F g‖ ^ 2 ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
      ((continuous_norm.comp hF).pow 2)
      (hFc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
      (fun g => by positivity) (by simpa using hx)
  exact hpos.ne' hreal

end Coefficients

section Separation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- The intertwiner `v ↦ ∫ ℓ(ρ(g⁻¹)v) ρ(g)b dg`. -/
def coefficientIntertwiner (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (b : V) : ρ.IntertwiningMap ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ
    { toFun := fun v => Hecke.integratedAction μ ρ hρ
        (Hecke.TestFunction.inversion (coefficientTest ρ hρ hc hℓ v)) b
      map_add' := fun v w => by simp
      map_smul' := fun c v => by simp }
    (fun h v => by
      change Hecke.integratedAction μ ρ hρ
          (Hecke.TestFunction.inversion (coefficientTest ρ hρ hc hℓ (ρ h v))) b =
        ρ h (Hecke.integratedAction μ ρ hρ
          (Hecke.TestFunction.inversion (coefficientTest ρ hρ hc hℓ v)) b)
      rw [← Hecke.integratedAction_leftTranslate]
      congr 2
      apply Hecke.TestFunction.ext
      intro g
      simp [map_mul, Module.End.mul_apply, mul_inv_rev])

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem coefficientIntertwiner_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) {ℓ : Module.Dual ℂ V}
    (hℓ : IsSmoothVector ρ.dual ℓ) (b v : V) :
    coefficientIntertwiner μ ρ hρ hc hℓ b v = Hecke.integratedAction μ ρ hρ
      (Hecke.TestFunction.inversion (coefficientTest ρ hρ hc hℓ v)) b := rfl

/-- For a vector `a₀` outside a subrepresentation `M`, there is an intertwiner
killing `M` and a vector `a₁` in the subrepresentation generated by `a₀` whose
image is not in `M`. -/
theorem exists_intertwiner_separating (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) (M : Subrepresentation ρ) {a₀ : V}
    (ha₀ : a₀ ∉ M) :
    ∃ (S : ρ.IntertwiningMap ρ) (a₁ : V), (∀ v ∈ M, S v = 0) ∧
      (∀ N : Subrepresentation ρ, a₀ ∈ N → a₁ ∈ N) ∧ S a₁ ∉ M := by
  obtain ⟨ℓ, hℓ, hℓM, hℓa⟩ := exists_smooth_dual_separating ρ hρ M ha₀
  set c := coefficientTest ρ hρ hc hℓ a₀ with hc_def
  set a₁ := Hecke.integratedAction μ ρ hρ (conjTest c) a₀ with ha₁_def
  -- `ℓ (ρ g a₁) = ∫ conj (c y) * c (g * y) dy`
  have hcoef : ∀ g : G, ℓ (ρ g a₁) = ∫ y, starRingEnd ℂ (c y) * c (g * y) ∂μ := by
    intro g
    rw [ha₁_def, show ℓ (ρ g (Hecke.integratedAction μ ρ hρ (conjTest c) a₀)) =
      (ℓ ∘ₗ ρ g) (Hecke.integratedAction μ ρ hρ (conjTest c) a₀) from rfl,
      Hecke.integratedAction_dual]
    congr 1
    funext y
    simp [hc_def, map_mul, Module.End.mul_apply]
  have hsymm : ∀ g : G, ℓ (ρ g⁻¹ a₁) = starRingEnd ℂ (ℓ (ρ g a₁)) := by
    intro g
    rw [hcoef, hcoef, ← integral_conj]
    rw [← integral_mul_left_eq_self
      (fun y => starRingEnd ℂ (starRingEnd ℂ (c y) * c (g * y))) g⁻¹]
    congr 1
    funext y
    simp [mul_comm]
  refine ⟨coefficientIntertwiner μ ρ hρ hc hℓ a₁, a₁, ?_, ?_, ?_⟩
  · intro v hv
    rw [coefficientIntertwiner_apply]
    have h0 : coefficientTest ρ hρ hc hℓ v = 0 := by
      apply Hecke.TestFunction.ext
      intro g
      exact hℓM _ (M.apply_mem_toSubmodule g hv)
    rw [h0, map_zero, map_zero, LinearMap.zero_apply]
  · intro N hN
    exact integratedAction_mem μ ρ hρ N (conjTest c) hN
  · intro hmem
    have hzero : ℓ (coefficientIntertwiner μ ρ hρ hc hℓ a₁ a₁) = 0 := hℓM _ hmem
    rw [coefficientIntertwiner_apply, Hecke.integratedAction_dual] at hzero
    have hint : ∫ g, starRingEnd ℂ (ℓ (ρ g a₁)) * ℓ (ρ g a₁) ∂μ = 0 := by
      rw [← hzero]
      congr 1
      funext g
      simp [hsymm]
    have hF := eq_zero_of_integral_conj_mul_self μ
      (coefficientTest ρ hρ hc hℓ a₁).continuous
      (coefficientTest ρ hρ hc hℓ a₁).hasCompactSupport hint 1
    change ℓ (ρ 1 a₁) = 0 at hF
    rw [hcoef] at hF
    simp only [one_mul] at hF
    have hc0 := eq_zero_of_integral_conj_mul_self μ c.continuous c.hasCompactSupport hF 1
    apply hℓa
    simpa [hc_def] using hc0

end Separation

section Lattice

variable {k : Type*} {G : Type*} {W : Type*} [Field k] [Monoid G]
  [AddCommGroup W] [Module k W]

/-- If every vector outside a subrepresentation `M` is separated from `M` by an
intertwiner as in `exists_intertwiner_separating`, then the irreducible
subrepresentations span. -/
theorem sSup_atoms_eq_top_of_separating {ρ : Representation k G W}
    (h : ∀ (M : Subrepresentation ρ) (a₀ : W), a₀ ∉ M →
      ∃ (S : ρ.IntertwiningMap ρ) (a₁ : W), (∀ v ∈ M, S v = 0) ∧
        (∀ N : Subrepresentation ρ, a₀ ∈ N → a₁ ∈ N) ∧ S a₁ ∉ M) :
    sSup {A : Subrepresentation ρ | IsAtom A} = ⊤ := by
  set s := sSup {A : Subrepresentation ρ | IsAtom A} with hs_def
  by_contra hs
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : W, a₀ ∉ s := by
    by_contra hall
    push Not at hall
    exact hs (eq_top_iff.mpr fun a _ => hall a)
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ {N : Subrepresentation ρ | s ≤ N ∧ a₀ ∉ N}
    (fun c hcP hchain y hy => by
      refine ⟨sSup c, ⟨(hcP hy).1.trans (le_sSup hy), ?_⟩, fun z hz => le_sSup hz⟩
      intro hmem
      change a₀ ∈ ⨆ N ∈ c, N.toSubmodule at hmem
      rw [← sSup_image, Submodule.mem_sSup_of_directed
        (Set.Nonempty.image Subrepresentation.toSubmodule ⟨y, hy⟩)
        (IsChain.directedOn (hchain.image_of_map_rel _ _ Subrepresentation.toSubmodule
          fun _ _ hle => hle))] at hmem
      obtain ⟨_, ⟨N, hN, rfl⟩, hN'⟩ := hmem
      exact (hcP hN).2 hN') s ⟨le_rfl, ha₀⟩
  obtain ⟨S, a₁, hSM, ha₁, hSa₁⟩ := h M a₀ hM.1.2
  let Z : Subrepresentation ρ := sInf {N | a₀ ∈ N}
  have hZ : ∀ z ∈ Z, ∀ N : Subrepresentation ρ, a₀ ∈ N → z ∈ N := by
    intro z hz N hN
    have hz' : z ∈ ⨅ N ∈ {N : Subrepresentation ρ | a₀ ∈ N}, N.toSubmodule := hz
    simp only [Submodule.mem_iInf] at hz'
    exact hz' N hN
  have ha₁Z : a₁ ∈ Z := by
    change a₁ ∈ ⨅ N ∈ {N : Subrepresentation ρ | a₀ ∈ N}, N.toSubmodule
    simp only [Submodule.mem_iInf]
    exact fun N hN => ha₁ N hN
  let I : Subrepresentation ρ :=
    ⟨Z.toSubmodule.map S.toLinearMap, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨ρ g v, Z.apply_mem_toSubmodule g hv, S.isIntertwining ρ ρ g v⟩⟩
  have hSa₁I : S a₁ ∈ I := ⟨a₁, ha₁Z, rfl⟩
  have hSa₁0 : S a₁ ≠ 0 := fun h0 => hSa₁ (h0 ▸ M.toSubmodule.zero_mem)
  have hI : IsAtom I := by
    refine ⟨fun hbot => hSa₁0 ?_, fun J hJ => ?_⟩
    · have : S a₁ ∈ (⊥ : Subrepresentation ρ) := hbot ▸ hSa₁I
      exact (Submodule.mem_bot k).mp this
    · let N : Subrepresentation ρ :=
        ⟨J.toSubmodule.comap S.toLinearMap, by
          intro g v hv
          change S (ρ g v) ∈ J.toSubmodule
          rw [S.isIntertwining ρ ρ g v]
          exact J.apply_mem_toSubmodule g hv⟩
      have hMN : M ≤ N := fun v hv => by
        change S v ∈ J.toSubmodule
        rw [hSM v hv]
        exact J.toSubmodule.zero_mem
      by_cases ha₀N : a₀ ∈ N
      · exfalso
        apply hJ.not_ge
        rintro _ ⟨z, hz, rfl⟩
        exact hZ z hz N ha₀N
      · have hNM : N ≤ M := hM.2 ⟨hM.1.1.trans hMN, ha₀N⟩ hMN
        apply eq_bot_iff.mpr
        intro x hx
        obtain ⟨z, hz, rfl⟩ := hJ.le hx
        have hzN : z ∈ N := hx
        change S z ∈ (⊥ : Submodule k W)
        rw [hSM z (hNM hzN)]
        exact (⊥ : Submodule k W).zero_mem
  have hIs : I ≤ s := le_sSup (show I ∈ {A : Subrepresentation ρ | IsAtom A} from hI)
  exact hSa₁ (hM.1.1 (hIs hSa₁I))

/-- Transfer of `sSup atoms = ⊤` through the subrepresentation-submodule order
isomorphism. -/
theorem isSemisimpleRepresentation_of_sSup_atoms_eq_top {ρ : Representation k G W}
    (h : sSup {A : Subrepresentation ρ | IsAtom A} = ⊤) :
    ρ.IsSemisimpleRepresentation := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    isSemisimpleModule_iff]
  apply complementedLattice_of_sSup_atoms_eq_top
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have himg : e '' {A : Subrepresentation ρ | IsAtom A} = {x | IsAtom x} := by
    ext x
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact (e.isAtom_iff A).mpr hA
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      exact (e.symm.isAtom_iff x).mpr hx
  rw [← himg, sSup_image, ← e.map_sSup, h, e.map_top]

end Lattice

/-- A smooth complex representation whose smooth-dual coefficients all have
compact support is semisimple. Only a left Haar measure is used. -/
theorem isSemisimpleRepresentation_of_compactCoefficients
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) :
    ρ.IsSemisimpleRepresentation :=
  isSemisimpleRepresentation_of_sSup_atoms_eq_top
    (sSup_atoms_eq_top_of_separating fun M _ ha₀ =>
      exists_intertwiner_separating μ ρ hρ hc M ha₀)

end CompactCoefficientSemisimplicity

/-- Bernstein--Zelevinsky (1976), Theorem 2.44(b), last sentence: every smooth
complex representation with compact smooth-dual coefficients is semisimple. -/
theorem compactCoefficientSemisimplicity
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [Measure.Regular μ]
    [Measure.IsMulRightInvariant μ] :
    CompactCoefficientSemisimplicityStatement.{uG, uV} G μ := fun A hA =>
  CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
    μ A.representation A.isSmooth hA

end Langlands
