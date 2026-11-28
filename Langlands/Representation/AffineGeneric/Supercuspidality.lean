import Langlands.Representation.AffineGeneric.TestFunction
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Character.Basic
import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.LevelZero.Indicator
import Langlands.Representation.OrbitSpan

/-!
# Representations detected by a test function `1_{I⁺} · ψ(λ_r)` are supercuspidal

Let `f = 1_{I⁺} · ψ(λ_r)` be the test function of `TestFunction` for a uniformizer `ϖ`,
a nontrivial additive character `ψ` and all `r_i ≠ 0`. If the distribution character of an
irreducible admissible representation `π` does not vanish at `f`, then `π(f) ≠ 0`. A nonzero
vector `v₀` in the image of `π(f)`
transforms under `I⁺` by the character `z ↦ ψ(λ_r(z⁻¹))`. For each proper block unipotent
radical `U` and `x ∈ GL_{m+1}(F)`, some `u ∈ U` has `x u x⁻¹ ∈ I⁺` with `ψ(λ_r(x u x⁻¹)) ≠ 1`,
so for every conjugate of `U` each translate of `v₀` is an eigenvector of an element of
that conjugate with eigenvalue different from `1`. Its class in the corresponding Jacquet
quotient is zero. The translates of `v₀` span `π`, so these Jacquet quotients are zero and
`π` is supercuspidal.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero GeneralLinear HarmonicAnalysis

universe u uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {m : ℕ}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A block shape whose parabolic is proper has at least two blocks. -/
theorem two_le_length_of_parabolic_ne_top {n : ℕ} (B : BlockShape n)
    (hB : B.parabolic F ≠ ⊤) : 2 ≤ B.length := by
  by_contra h
  apply hB
  refine eq_top_iff.mpr fun g _ => (B.mem_parabolic_iff F g).mpr fun i j _ _ hji => ?_
  exfalso
  have hi := i.isLt
  have hj := j.isLt
  have : (j : ℕ) < i := hji
  omega

variable {ϖ : Fˣ} (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ)
  (ψ : AddChar (Residue F) ℂ) (r : Fin (m + 1) → Residue F)

include hϖ in
/-- For a uniformizer `ϖ`, left translation by `z ∈ I⁺` multiplies the test function
`1_{I⁺} · ψ(λ_r)` by `ψ(λ_r(z⁻¹))`. -/
theorem leftTranslate_affineGenericTest {z : GeneralLinear (m + 1) F}
    (hz : z ∈ iwahoriRadical m) :
    Hecke.TestFunction.leftTranslate z (affineGenericTest ϖ ψ r) =
      ψ (affineForm ϖ r z⁻¹) • affineGenericTest ϖ ψ r := by
  ext x
  rw [Hecke.TestFunction.leftTranslate_apply, affineGenericTest_apply,
    testFunction_mul_left ψ r hϖ (inv_mem hz)]
  rfl

section Character

variable [MeasurableSpace (GeneralLinear (m + 1) F)] [BorelSpace (GeneralLinear (m + 1) F)]
  [T2Space (GeneralLinear (m + 1) F)] [LocallyCompactSpace (GeneralLinear (m + 1) F)]
  [TotallyDisconnectedSpace (GeneralLinear (m + 1) F)]

include hϖ in
/-- **Supercuspidality.** For a uniformizer `ϖ`, nontrivial `ψ` and all `r_i ≠ 0`, an
irreducible admissible representation whose distribution character does not vanish at the
test function `1_{I⁺} · ψ(λ_r)` is supercuspidal. -/
theorem isSupercuspidal_of_distribution_ne_zero (hψ : ψ ≠ 1) (hr : ∀ i, r i ≠ 0)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (m + 1) F) W) (hπ : IsAdmissible π)
    (hirr : π.IsIrreducible) (μ : Measure (GeneralLinear (m + 1) F)) [μ.IsHaarMeasure]
    (hdist : Character.distribution μ π hπ (affineGenericTest ϖ ψ r) ≠ 0) :
    GeneralLinear.IsSupercuspidal π := by
  let φ := affineGenericTest ϖ ψ r
  let T := Hecke.integratedAction μ π hπ.1
  obtain ⟨w, hw⟩ : ∃ w, T φ w ≠ 0 := by
    by_contra h
    push Not at h
    apply hdist
    have h0 : Character.finiteRankIntegratedAction μ π hπ φ = 0 :=
      Subtype.ext (LinearMap.ext h)
    rw [Character.distribution_apply, h0, map_zero]
  set v := T φ w with hv
  -- `v` is an eigenvector of `I⁺`.
  have heig : ∀ z ∈ iwahoriRadical m, π z v = ψ (affineForm ϖ r z⁻¹) • v := by
    intro z hz
    rw [hv, ← Hecke.integratedAction_leftTranslate μ π hπ.1 z φ w,
      leftTranslate_affineGenericTest hϖ ψ r hz, map_smul, LinearMap.smul_apply]
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (DFunLike.ext _ _ fun s => by rw [h s, AddChar.one_apply])
  refine ⟨hπ, fun B hB g => ?_⟩
  let N := B.conjugateUnipotent g
  refine coinvariants_subsingleton_of_span π N _ (span_range_orbit_eq_top hirr hw) ?_
  rintro _ ⟨h, rfl⟩
  obtain ⟨u0, hu0, hz, hlam⟩ := exists_unipotent_affineForm_eq hϖ r hr t (h⁻¹ * g) B
    (two_le_length_of_parabolic_ne_top B hB)
  set z := h⁻¹ * g * u0 * (h⁻¹ * g)⁻¹ with hzdef
  have hn : (g * u0 * g⁻¹)⁻¹ ∈ N := by
    refine N.inv_mem ⟨u0, hu0, ?_⟩
    rfl
  have hact : π (g * u0 * g⁻¹)⁻¹ (π h v) = ψ t • π h v := by
    have he : (g * u0 * g⁻¹)⁻¹ * h = h * z⁻¹ := by
      rw [hzdef]
      group
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply,
      heig z⁻¹ (inv_mem hz), inv_inv, hlam, map_smul]
  rw [SetLike.mem_coe, ← Jacquet.mk_eq_zero]
  have hmk := Jacquet.mk_apply_subgroup π N ⟨_, hn⟩ (π h v)
  change Jacquet.mk π N (π (g * u0 * g⁻¹)⁻¹ (π h v)) = _ at hmk
  rw [hact, map_smul] at hmk
  have h0 : (ψ t - 1) • Jacquet.mk π N (π h v) = 0 := by
    rw [sub_smul, one_smul, hmk, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr ht)

end Character

end Langlands.AffineGeneric
