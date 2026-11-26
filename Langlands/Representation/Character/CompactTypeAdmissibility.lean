import Langlands.Representation.Character.Basic
import Langlands.HarmonicAnalysis.Distribution.Subspace
import Langlands.Analysis.Local.CompactFactorizationHaar
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.OrbitSpan
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Mathlib.LinearAlgebra.Trace

/-! # Compact-type admissibility of irreducible characters -/

noncomputable section

namespace Langlands.Character

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Set Function Topology

section Compact

variable {K X : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [AddCommGroup X] [Module ℂ X] (τ : Representation ℂ K X) (hτ : IsSmooth τ)

private def coefficientTest (ℓ : Module.Dual ℂ X) : X →ₗ[ℂ] SchwartzBruhat K where
  toFun x := ⟨fun k => ℓ (τ k x), (Hecke.orbitMap_locallyConstant τ (hτ x)).comp ℓ,
    HasCompactSupport.of_compactSpace _⟩
  map_add' x y := Hecke.TestFunction.ext fun k => by simp
  map_smul' c x := Hecke.TestFunction.ext fun k => by simp

private theorem coefficientTest_apply (ℓ : Module.Dual ℂ X) (x : X) (k : K) :
    coefficientTest τ hτ ℓ x k = ℓ (τ k x) := rfl

variable [FiniteDimensional ℂ X]

/-- The ordinary trace of a finite-dimensional smooth compact-group representation as a test. -/
def compactTraceTest : SchwartzBruhat K := by
  classical
  let b := Module.finBasis ℂ X
  exact ∑ i, coefficientTest τ hτ (b.coord i) (b i)

@[simp]
theorem compactTraceTest_apply (k : K) : compactTraceTest τ hτ k = LinearMap.trace ℂ X (τ k) := by
  classical
  let b := Module.finBasis ℂ X
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp [compactTraceTest, b, Matrix.trace, LinearMap.toMatrix_apply, coefficientTest_apply]

end Compact

section Admissibility

variable {G V X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
  (K₀ K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The intersection of the test subgroup with the conjugate of the level subgroup, in test
subgroup coordinates. -/
def conjugateIntersection (g : G) : OpenSubgroup K :=
  K₀.comap ((MulAut.conj g⁻¹).toMonoidHom.comp K.toSubgroup.subtype)
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G]
  [BorelSpace G] in
private theorem conjugateIntersection_mem (g : G) (k : K) :
    k ∈ conjugateIntersection K₀ K g ↔ g⁻¹ * k.val * g ∈ K₀ := by
  change g⁻¹ * k.val * g⁻¹⁻¹ ∈ K₀ ↔ _
  rw [inv_inv]

/-- Extend the compact trace test by zero on the indicated left coset. -/
def compactTraceCosetTest (τ : Representation ℂ K X) (hτ : IsSmooth τ) (y : G) :
    SchwartzBruhat G :=
  letI : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  Hecke.TestFunction.leftTranslate y (SchwartzBruhat.extendZero K.isOpen (compactTraceTest τ hτ))

variable (ν : Measure G) [ν.IsHaarMeasure]
  (π : Representation ℂ G V) (hπ : IsAdmissible π)

/-- Nonvanishing of the character on a translated compact trace test detects fixed vectors
of that compact type on the intersection with a conjugate of a nonzero fixed-vector level. -/
def CompactTypeAdmissibilityStatement (τ : Representation ℂ K X) (hτ : IsSmooth τ) : Prop :=
  π.IsIrreducible → fixedVectors π K₀.toSubgroup ≠ ⊥ →
  ∀ y : G, distribution ν π hπ (compactTraceCosetTest K hK τ hτ y) ≠ 0 →
    ∃ g : G, fixedVectors τ (conjugateIntersection K₀ K g).toSubgroup ≠ ⊥

/-- A nonzero coefficient operator acts nontrivially on an orbit of a fixed vector. Right
translation makes the resulting parameter map invariant under the intersection subgroup. -/
theorem compactTypeAdmissibility (τ : Representation ℂ K X) (hτ : IsSmooth τ) :
    CompactTypeAdmissibilityStatement K₀ K hK ν π hπ τ hτ := by
  classical
  rintro hirr h₀ y hy
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ι := K.toSubgroup.subtype
  have hι : IsOpenEmbedding ι := K.isOpen.isOpenEmbedding_subtypeVal
  let μ := ν.comap ι
  let : μ.IsHaarMeasure := IsHaarMeasure.comap (mH := inferInstance) _ hι
  let : μ.IsMulRightInvariant := CompactFactorization.isMulRightInvariant_of_compactSpace μ
  let σ := π.comp ι
  let hσ := isSmooth_comp ι hι.continuous hπ.1
  let f := compactTraceTest τ hτ
  have hA : Hecke.integratedAction ν π hπ.1 (compactTraceCosetTest K hK τ hτ y) =
      (π y).comp (Hecke.integratedAction μ σ hσ f) := by
    ext v
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro L
    rw [map_sub, sub_eq_zero, Hecke.integratedAction_dual]
    let f₀ := SchwartzBruhat.extendZero K.isOpen f
    change (∫ z, Hecke.TestFunction.leftTranslate y f₀ z * L (π z v) ∂ν) =
      (L.comp (π y)) (Hecke.integratedAction μ σ hσ f v)
    rw [Hecke.integratedAction_dual, ← integral_mul_left_eq_self
      (fun z => Hecke.TestFunction.leftTranslate y f₀ z * L (π z v)) y]
    simp only [Hecke.TestFunction.leftTranslate_apply, inv_mul_cancel_left]
    have hRange : range ι = (K : Set G) := by
      ext z
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
    calc
      _ = ∫ z in range ι, f₀ z * L (π (y * z) v) ∂ν := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        have hzK : z ∉ K := by rwa [hRange] at hz
        simp [f₀, SchwartzBruhat.extendZero_apply_of_not_mem K.isOpen f hzK]
      _ = _ := by
        rw [← hι.measurableEmbedding.map_comap, hι.measurableEmbedding.integral_map]
        simp only [map_mul, LinearMap.comp_apply, Module.End.mul_apply]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun k => by
          change f₀ (k : G) * L (π y (π k.val v)) = f k * L (π y (π k.val v))
          rw [SchwartzBruhat.extendZero_apply_of_mem K.isOpen f k.property]
          rfl
  have hAct : Hecke.integratedAction μ σ hσ f ≠ 0 := by
    intro h
    apply hy
    rw [distribution_apply]
    have hzero : finiteRankIntegratedAction ν π hπ (compactTraceCosetTest K hK τ hτ y) = 0 := by
      apply Subtype.ext
      change Hecke.integratedAction ν π hπ.1 (compactTraceCosetTest K hK τ hτ y) = 0
      rw [hA, h, LinearMap.comp_zero]
    rw [hzero, map_zero]
  let b := Module.finBasis ℂ X
  have hterm : ∃ i, Hecke.integratedAction μ σ hσ (coefficientTest τ hτ (b.coord i) (b i)) ≠ 0 := by
    by_contra! hterm
    apply hAct
    change Hecke.integratedAction μ σ hσ (∑ i, coefficientTest τ hτ (b.coord i) (b i)) = 0
    rw [_root_.map_sum]
    simp [hterm]
  obtain ⟨i, hi⟩ := hterm
  let ℓ := b.coord i
  let M := Hecke.integratedAction μ σ hσ (coefficientTest τ hτ ℓ (b i))
  obtain ⟨w, hw, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₀
  have hg : ∃ g : G, M (π g w) ≠ 0 := by
    by_contra! hg
    have hle : Submodule.span ℂ (range (fun g : G => π g w)) ≤ LinearMap.ker M :=
      Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hg g)
    rw [span_range_orbit_eq_top hirr hw₀, top_le_iff, LinearMap.ker_eq_top] at hle
    exact hi hle
  obtain ⟨g, hg⟩ := hg
  let L := conjugateIntersection K₀ K g
  have hL : IsCompact (L : Set K) := L.isClosed.isCompact
  let v := π g w
  have hv (k : L) : σ k.val v = v := by
    have hk : g⁻¹ * (k.val : G) * g ∈ K₀ :=
      (conjugateIntersection_mem K₀ K g k.val).1 k.property
    have hgroup : (k.val : G) * g = g * (g⁻¹ * (k.val : G) * g) := by group
    have hfix : π (g⁻¹ * (k.val : G) * g) w = w := hw ⟨_, hk⟩
    change π (k.val : G) (π g w) = π g w
    rw [← Module.End.mul_apply, ← map_mul, hgroup, map_mul, Module.End.mul_apply, hfix]
  let A : X →ₗ[ℂ] V := (LinearMap.applyₗ' ℂ v : Module.End ℂ V →ₗ[ℂ] V).comp
    ((Hecke.integratedAction μ σ hσ).comp (coefficientTest τ hτ ℓ))
  have hAinv (k : L) (x : X) : A (τ k.val x) = A x := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro q
    rw [map_sub, sub_eq_zero]
    change q (Hecke.integratedAction μ σ hσ (coefficientTest τ hτ ℓ (τ k.val x)) v) =
      q (Hecke.integratedAction μ σ hσ (coefficientTest τ hτ ℓ x) v)
    rw [Hecke.integratedAction_dual, Hecke.integratedAction_dual,
      ← integral_mul_right_eq_self (μ := μ) (f := fun k => coefficientTest τ hτ ℓ x k * q (σ k v)) k.val]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      simp only [coefficientTest_apply, map_mul, Module.End.mul_apply, hv k]
  let τL := τ.comp L.toSubgroup.subtype
  let b' := Compact.CharZero.orbitMean τL (b i)
  let : Finite (Compact.CharZero.orbit τL (b i)) :=
    Compact.CharZero.finite_orbit_of_smooth τ hτ L hL (b i)
  let : Finite (Compact.CharZero.orbit (Representation.trivial ℂ L V) (A (b i))) :=
    ((Set.finite_singleton (A (b i))).subset (by
      rintro _ ⟨k, rfl⟩; simp [Representation.trivial_apply])).to_subtype
  have hAb : A b' = A (b i) := by
    change A (Compact.CharZero.orbitMean τL (b i)) = _
    rw [Compact.CharZero.orbitMean_map τL (Representation.trivial ℂ L V) A
      (fun k x => hAinv k x) (b i)]
    exact Compact.CharZero.orbitMean_id _ _ fun k => Representation.trivial_apply ℂ k _
  have hb' : b' ≠ 0 := by
    intro hb'
    apply hg
    change A (b i) = 0
    rw [← hAb, hb', map_zero]
  have hfix : b' ∈ fixedVectors τ L.toSubgroup :=
    fun k => Compact.CharZero.orbitMean_invariant τL (b i) k
  exact ⟨g, fun h => hb' ((Submodule.mem_bot ℂ).mp (h ▸ hfix))⟩

end Admissibility

end Langlands.Character
