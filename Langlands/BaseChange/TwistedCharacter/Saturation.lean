import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof
import Langlands.Representation.Character.ModularConjugationProof

/-! # Twisted character values on twisted conjugacy saturations

For a monoid endomorphism `θ` of a topological group `G`, twisted conjugation by `x` is the
homeomorphism `y ↦ x y θ(x)⁻¹`. When an endomorphism `A` of an admissible representation `ρ`
satisfies `A ∘ ρ(g) = ρ(θ g) ∘ A`, the twisted distribution `φ ↦ tr(ρ(φ) ∘ A)` transforms under
twisted conjugation of test functions by the same modular factor as the Haar integral. Hence a
local twisted character value on an open window holds on the union of all twisted conjugates of
the window, and a twisted character value at `g` is also one at every twisted conjugate of `g`.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.HarmonicAnalysis Langlands.JacquetLanglands

universe uG uV

section TwistedConjugation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Twisted conjugation `y ↦ x * y * (θ x)⁻¹` by `x`, as a homeomorphism of `G`. -/
def twistedConjugationHomeomorph (θ : G →* G) (x : G) : G ≃ₜ G :=
  (Homeomorph.mulLeft x).trans (Homeomorph.mulRight (θ x)⁻¹)

@[simp]
theorem twistedConjugationHomeomorph_apply (θ : G →* G) (x y : G) :
    twistedConjugationHomeomorph θ x y = x * y * (θ x)⁻¹ := rfl

/-- The union of all twisted conjugates `x U θ(x)⁻¹` of a set `U`. -/
def twistedConjugacySaturation (θ : G →* G) (U : Set G) : Set G :=
  ⋃ x : G, twistedConjugationHomeomorph θ x '' U

theorem isOpen_twistedConjugacySaturation (θ : G →* G) {U : Set G} (hU : IsOpen U) :
    IsOpen (twistedConjugacySaturation θ U) :=
  isOpen_iUnion fun x => (twistedConjugationHomeomorph θ x).isOpenMap _ hU

theorem subset_twistedConjugacySaturation (θ : G →* G) (U : Set G) :
    U ⊆ twistedConjugacySaturation θ U := fun y hy =>
  Set.mem_iUnion.2 ⟨1, y, hy, by simp⟩

theorem twistedConj_mem_twistedConjugacySaturation (θ : G →* G) {U : Set G} {y : G}
    (hy : y ∈ U) (x : G) : x * y * (θ x)⁻¹ ∈ twistedConjugacySaturation θ U :=
  Set.mem_iUnion.2 ⟨x, y, hy, rfl⟩

end TwistedConjugation

section Distribution

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (μ : Measure G) [μ.IsHaarMeasure]
  (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)

/-- Twisted conjugation of a test function conjugates the integrated action, with Renard's
modular factor of `θ x`. -/
theorem integratedAction_twistedConjugation (θ : G →* G) (x : G) (f : SchwartzBruhat G)
    (v : V) :
    Hecke.integratedAction μ ρ hρ.1
        (Hecke.TestFunction.pullback (twistedConjugationHomeomorph θ x) f) v =
      ((Distribution.renardModular (θ x) : ℝ) : ℂ) •
        ρ x⁻¹ (Hecke.integratedAction μ ρ hρ.1 f (ρ (θ x) v)) := by
  apply Module.eval_apply_injective ℂ
  apply LinearMap.ext
  intro L
  change L (Hecke.integratedAction μ ρ hρ.1
      (Hecke.TestFunction.pullback (twistedConjugationHomeomorph θ x) f) v) = _
  rw [map_smul]
  change L (Hecke.integratedAction μ ρ hρ.1
      (Hecke.TestFunction.pullback (twistedConjugationHomeomorph θ x) f) v) =
    ((Distribution.renardModular (θ x) : ℝ) : ℂ) *
      (L.comp (ρ x⁻¹)) (Hecke.integratedAction μ ρ hρ.1 f (ρ (θ x) v))
  rw [Hecke.integratedAction_dual, Hecke.integratedAction_dual]
  have ht := (Distribution.RenardModular.translation G μ).2
    (Character.scalarActionTest ρ hρ.1 f (ρ (θ x) v) (L.comp (ρ x⁻¹))) (θ x) x
  have hpt : ∀ y : G, (Character.scalarActionTest ρ hρ.1 f (ρ (θ x) v) (L.comp (ρ x⁻¹)))
      (x * y * (θ x)⁻¹) =
      (Hecke.TestFunction.pullback (twistedConjugationHomeomorph θ x) f) y * L (ρ y v) := by
    intro y
    rw [Character.scalarActionTest_apply, Hecke.TestFunction.pullback_apply,
      twistedConjugationHomeomorph_apply]
    congr 1
    change L (ρ x⁻¹ (ρ (x * y * (θ x)⁻¹) (ρ (θ x) v))) = L (ρ y v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  simp_rw [hpt] at ht
  rw [ht, Distribution.ofMeasure_apply]
  rfl

/-- A twisted distribution for an endomorphism `A` with `A ∘ ρ(g) = ρ(θ g) ∘ A` changes
under twisted conjugation of the test function by Renard's modular factor of `θ x`. -/
theorem twistedDistribution_twistedConjugation (θ : G →* G) (A : Module.End ℂ V)
    (hA : ∀ g : G, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (x : G) (f : SchwartzBruhat G) :
    twistedDistribution μ ρ hρ A
        (Hecke.TestFunction.pullback (twistedConjugationHomeomorph θ x) f) =
      ((Distribution.renardModular (θ x) : ℝ) : ℂ) * twistedDistribution μ ρ hρ A f := by
  let E : V ≃ₗ[ℂ] V :=
    { ρ x⁻¹ with
      invFun := ρ x
      left_inv := ρ.self_inv_apply x
      right_inv := ρ.inv_self_apply x }
  let T := Character.finiteRankIntegratedAction μ ρ hρ f
  let T' := Character.finiteRankIntegratedAction μ ρ hρ
    (Hecke.TestFunction.pullback (twistedConjugationHomeomorph θ x) f)
  have he : (⟨T'.val.comp A, T'.property.comp_right A⟩ : finiteRankEnd V) =
      ((Distribution.renardModular (θ x) : ℝ) : ℂ) •
        FiniteRankEnd.conjugate E ⟨T.val.comp A, T.property.comp_right A⟩ := by
    apply Subtype.ext
    ext v
    change Hecke.integratedAction μ ρ hρ.1
        (Hecke.TestFunction.pullback (twistedConjugationHomeomorph θ x) f) (A v) =
      ((Distribution.renardModular (θ x) : ℝ) : ℂ) •
        ρ x⁻¹ (Hecke.integratedAction μ ρ hρ.1 f (A (ρ x v)))
    rw [integratedAction_twistedConjugation μ ρ hρ]
    have hAx : A (ρ x v) = ρ (θ x) (A v) := LinearMap.congr_fun (hA x) v
    rw [hAx]
  rw [twistedDistribution_apply, twistedDistribution_apply]
  change FiniteRankEnd.trace (⟨T'.val.comp A, T'.property.comp_right A⟩ : finiteRankEnd V) = _
  rw [he, map_smul, FiniteRankEnd.trace_conjugate, smul_eq_mul]

variable {θ : G →* G} {A : Module.End ℂ V} {a : ℂ}

private theorem evaluate_twistedConjugate (hA : ∀ g : G, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A)
    {U : Set G}
    (hvalue : ∀ f : SchwartzBruhat G, Function.support f ⊆ U →
      twistedDistribution μ ρ hρ A f = a * ∫ y, f y ∂μ)
    (x : G) (f : SchwartzBruhat G)
    (hf : Function.support f ⊆ twistedConjugationHomeomorph θ x '' U) :
    twistedDistribution μ ρ hρ A f = a * ∫ y, f y ∂μ := by
  let e := twistedConjugationHomeomorph θ x
  have hpull : Function.support (Hecke.TestFunction.pullback e f) ⊆ U := by
    intro y hy
    have hy' : e y ∈ Function.support f := hy
    obtain ⟨z, hz, heq⟩ := hf hy'
    exact e.injective heq ▸ hz
  have hcharacter := twistedDistribution_twistedConjugation μ ρ hρ θ A hA x f
  have hintegral : (∫ y, Hecke.TestFunction.pullback e f y ∂μ) =
      ((Distribution.renardModular (θ x) : ℝ) : ℂ) * ∫ y, f y ∂μ := by
    have h := (Distribution.RenardModular.translation G μ).2 f (θ x) x
    rw [Distribution.ofMeasure_apply] at h
    exact h
  have hfactor : ((Distribution.renardModular (θ x) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.2 (by
      exact_mod_cast ((Distribution.RenardModular.regularity G).1 (θ x)).ne')
  have h := hvalue _ hpull
  rw [hcharacter, hintegral, mul_left_comm a] at h
  exact mul_left_cancel₀ hfactor h

/-- A local twisted value on an open window `U` holds for every test function supported in
the twisted conjugacy saturation of `U`. -/
theorem twistedDistribution_eq_of_support_twistedConjugacySaturation
    (hA : ∀ g : G, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) {U : Set G} (hU : IsOpen U)
    (hvalue : ∀ f : SchwartzBruhat G, Function.support f ⊆ U →
      twistedDistribution μ ρ hρ A f = a * ∫ y, f y ∂μ)
    (f : SchwartzBruhat G) (hf : Function.support f ⊆ twistedConjugacySaturation θ U) :
    twistedDistribution μ ρ hρ A f = a * ∫ y, f y ∂μ := by
  classical
  let D := twistedDistribution μ ρ hρ A - a • Distribution.ofMeasure μ
  have hD : D ∈ Distribution.supportedOn (twistedConjugacySaturation θ U)ᶜ := by
    apply Distribution.openRestrictionLocality
    intro y hy
    obtain ⟨x, hxy⟩ := Set.mem_iUnion.1 (not_not.mp hy)
    let U' := twistedConjugationHomeomorph θ x '' U
    have hU' : IsOpen U' := (twistedConjugationHomeomorph θ x).isOpenMap _ hU
    refine ⟨U', hU', hxy, ?_⟩
    apply LinearMap.ext
    intro φ
    rw [Distribution.restrictOpen_apply]
    have hsupp : Function.support (SchwartzBruhat.extendZero hU' φ) ⊆ U' := by
      intro z hz
      by_contra hz'
      exact hz (SchwartzBruhat.extendZero_apply_of_not_mem hU' φ hz')
    have hz := evaluate_twistedConjugate μ ρ hρ hA hvalue x _ hsupp
    change twistedDistribution μ ρ hρ A _ - a * Distribution.ofMeasure μ _ = 0
    rw [Distribution.ofMeasure_apply, hz, sub_self]
  have h := hD f (fun y hy => by
    by_contra hfy
    exact hy (hf hfy))
  change twistedDistribution μ ρ hρ A f - a * Distribution.ofMeasure μ f = 0 at h
  rw [Distribution.ofMeasure_apply, sub_eq_zero] at h
  exact h

end Distribution

section Values

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ} {θ : G →* G} {A : Module.End ℂ V}

/-- A twisted character value at `g` comes, for each Haar measure, with an open window around
`g` whose twisted conjugacy saturation also carries the value. -/
theorem HasTwistedCharacterValue.exists_saturation (hA : ∀ g : G, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A)
    {g : G} {c : ℂ} (h : HasTwistedCharacterValue ρ hρ A g c) :
    letI : MeasurableSpace G := borel G
    haveI : BorelSpace G := ⟨rfl⟩
    ∀ (μ : Measure G) [μ.IsHaarMeasure], ∃ U : Set G, IsOpen U ∧ g ∈ U ∧
      ∀ f : SchwartzBruhat G, Function.support f ⊆ twistedConjugacySaturation θ U →
        twistedDistribution μ ρ hρ A f = c * ∫ y, f y ∂μ := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  obtain ⟨U, hU, hg, hf⟩ := h μ
  exact ⟨U, hU, hg, twistedDistribution_eq_of_support_twistedConjugacySaturation
    μ ρ hρ hA hU hf⟩

/-- Twisted character values are invariant under twisted conjugation of the point. -/
theorem HasTwistedCharacterValue.twistedConj (hA : ∀ g : G, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A)
    {g : G} {c : ℂ} (h : HasTwistedCharacterValue ρ hρ A g c) (x : G) :
    HasTwistedCharacterValue ρ hρ A (x * g * (θ x)⁻¹) c := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  obtain ⟨U, hU, hg, hf⟩ := h.exists_saturation hA μ
  exact ⟨twistedConjugacySaturation θ U, isOpen_twistedConjugacySaturation θ hU,
    twistedConj_mem_twistedConjugacySaturation θ hg x, hf⟩

end Values

end Langlands.BaseChange
