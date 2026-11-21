import Langlands.Analysis.DiscreteProductSubgroupCounting
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Global.LocalModularCharacter.PlaceGlue
import Langlands.Global.PrincipalAdelesDiscreteProof

/-! # Counting rational points in adelic conjugates of compact sets -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField Topology
open scoped CategoryTheory.MonObj RestrictedProduct

namespace Langlands.Global

section RationalMatrices

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private abbrev InfiniteEntries := Fin n → Fin n → (w : InfinitePlace F) → w.Completion
private abbrev FiniteEntries := Fin n → Fin n → FiniteAdeles F

private def splitEntries (g : AdelicGL F n) : InfiniteEntries F n × FiniteEntries F n :=
  (fun i j => (g i j).1, fun i j => (g i j).2)

private theorem splitEntries_injective : Function.Injective (splitEntries F n) := by
  intro g h he
  apply Units.ext
  ext i j
  exact Prod.ext (congrFun (congrFun (congrArg Prod.fst he) i) j)
    (congrFun (congrFun (congrArg Prod.snd he) i) j)

private def principalEntries : AddSubgroup (InfiniteEntries F n × FiniteEntries F n) where
  carrier := {p | ∀ i j, (p.1 i j, p.2 i j) ∈ principalAdeles F}
  zero_mem' := fun _ _ => (principalAdeles F).zero_mem
  add_mem' ha hb := fun i j => (principalAdeles F).add_mem (ha i j) (hb i j)
  neg_mem' ha := fun i j => (principalAdeles F).neg_mem (ha i j)

private theorem principalEntries_discrete : DiscreteTopology (principalEntries F n) := by
  refine discreteTopology_of_isOpen_singleton_zero (isOpen_induced_iff.mpr ?_)
  let U : Set (InfiniteEntries F n × FiniteEntries F n) :=
    ⋂ i : Fin n, ⋂ j : Fin n,
      (fun p => (p.1 i j, p.2 i j)) ⁻¹' principalAdelesIsolatingSet F
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    have ha : Continuous (fun p : InfiniteEntries F n × FiniteEntries F n => p.1 i j) := by
      fun_prop
    have hb : Continuous (fun p : InfiniteEntries F n × FiniteEntries F n => p.2 i j) := by
      fun_prop
    exact (isOpen_principalAdelesIsolatingSet F).preimage (ha.prodMk hb)
  refine ⟨U, hU, ?_⟩
  ext p
  constructor
  · intro hp
    have hp₀ (i j : Fin n) : (p.1.1 i j, p.1.2 i j) = (0 : Adeles F) := by
      have hpU : (p.1.1 i j, p.1.2 i j) ∈ principalAdelesIsolatingSet F :=
        Set.mem_iInter.mp (Set.mem_iInter.mp hp i) j
      exact Set.mem_singleton_iff.mp ((principalAdelesIsolatingSet_inter_principalAdeles F)
        ▸ (show (p.1.1 i j, p.1.2 i j) ∈
          principalAdelesIsolatingSet F ∩ (principalAdeles F : Set (Adeles F)) from
          ⟨hpU, p.2 i j⟩))
    exact Set.mem_singleton_iff.mpr (Subtype.ext (Prod.ext
      (funext fun i => funext fun j => congrArg Prod.fst (hp₀ i j))
      (funext fun i => funext fun j => congrArg Prod.snd (hp₀ i j))))
  · intro hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun j =>
      zero_mem_principalAdelesIsolatingSet F

/-- The finite matrix slice comes from a compact set of actual finite adelic group points. -/
private theorem exists_isCompact_finiteMatrixSlice
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (rho : GroupScheme.MatrixRepresentation G (Fin n))
    (K : Set (FiniteAdelicGroupPoints F G)) (hK : IsCompact K) :
    ∃ D : Set (FiniteAdelicGL F n), IsCompact D ∧
      ∀ x : AdelicGroupPoints F G, AdelicGroupPoints.finite F G x ∈ K →
        AdelicGL.finite F n (RepresentationGrowth.adelicMatrix F G rho x) ∈ D := by
  let f : FiniteAdelicGroupPoints F G → FiniteAdelicGL F n := fun k =>
    AdelicGL.finite F n (RepresentationGrowth.adelicMatrix F G rho
      (AdelicGroupPoints.ofFinite F G k))
  have hf : Continuous f := (AdelicGL.finite F n).continuous.comp
    ((RepresentationGrowth.adelicMatrix F G rho).continuous.comp
      (AdelicGroupPoints.ofFinite F G).continuous)
  refine ⟨f '' K, hK.image hf, fun x hx => ⟨AdelicGroupPoints.finite F G x, hx, ?_⟩⟩
  have h (y : AdelicGroupPoints F G) :
      AdelicGL.finite F n (RepresentationGrowth.adelicMatrix F G rho y) =
        GeneralLinearGroupPoints.finiteHomeomorph F n
          (G.affinePointsTarget rho (CommAlgCat.of F (FiniteAdeles F))
            (AdelicGroupPoints.finite F G y)) := by
    change AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
      (G.affinePointsTarget rho (CommAlgCat.of F (Adeles F)) y)) = _
    rw [← GeneralLinearGroupPoints.finiteHomeomorph_finite]
    congr 1
  rw [show f (AdelicGroupPoints.finite F G x) = _ from h _, h,
    AdelicGroupPoints.finite_ofFinite]

end RationalMatrices

/-- Fix a positive-rank faithful matrix representation of an affine group over a number
field. For compact `K` in the finite adelic group and compact `C` in the full group, the
number of rational points in `x C x⁻¹`, for `x` with finite component in `K`, is bounded
by a fixed power of the adelic height of `x`. The power is uniform in `K` and `C`. -/
def AdelicRationalConjugateCountingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (n : ℕ) (rho : GroupScheme.MatrixRepresentation G (Fin n)),
    0 < n → GroupScheme.IsClosedSubgroup rho →
    ∃ d : ℕ, ∀ (K : Set (FiniteAdelicGroupPoints F G)), IsCompact K →
      ∀ (C : Set (AdelicGroupPoints F G)), IsCompact C →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : AdelicGroupPoints F G,
          AdelicGroupPoints.finite F G x ∈ K →
          let P := (AdelicGroupPoints.rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
            ((fun y => x * y * x⁻¹) '' C)
          P.Finite ∧ (P.ncard : ℝ) ≤ B * RepresentationGrowth.adelicHeight F G rho x ^ d

open RepresentationGrowth in
/-- Specialization of discrete product packing to the actual rational subgroup. -/
theorem adelicRationalConjugateCounting : AdelicRationalConjugateCountingStatement.{u} := by
  classical
  intro F _ _ G _ n rho hn hrho
  choose normedSpace finiteDimensional using
    fun w : InfinitePlace F => exists_normedSpace_real_infiniteCompletion w
  let (w : InfinitePlace F) : NormedSpace ℝ w.Completion := normedSpace w
  let (w : InfinitePlace F) : FiniteDimensional ℝ w.Completion := finiteDimensional w
  let : T2Space (FiniteAdeles F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let Γ := principalEntries F n
  let : DiscreteTopology Γ := principalEntries_discrete F n
  let d := Module.finrank ℝ (InfiniteEntries F n)
  refine ⟨2 * d, fun K hK C hC => ?_⟩
  obtain ⟨D, hD, hKD⟩ := exists_isCompact_finiteMatrixSlice F n G rho K hK
  obtain ⟨b, hb⟩ := hC.bddAbove_image (continuous_adelicHeight F G rho hn).continuousOn
  let M := max 1 b
  have hM : 1 ≤ M := le_max_left _ _
  let f : FiniteAdelicGL F n × AdelicGroupPoints F G → FiniteEntries F n := fun p i j =>
    (p.1 * AdelicGL.finite F n (adelicMatrix F G rho p.2) * p.1⁻¹) i j
  have hf : Continuous f := continuous_pi fun i => continuous_pi fun j =>
    (Units.continuous_val.matrix_elem i j).comp
      ((continuous_fst.mul ((AdelicGL.finite F n).continuous.comp
        ((adelicMatrix F G rho).continuous.comp continuous_snd))).mul continuous_fst.inv)
  let Q := f '' (D ×ˢ C)
  obtain ⟨A, hA, hcount⟩ := Langlands.Analysis.discreteProductSubgroupCounting
    (E := InfiniteEntries F n) Γ Q
    ((hD.prod hC).image hf)
  refine ⟨A * (2 * M) ^ d, by positivity, fun x hx => ?_⟩
  let P := (AdelicGroupPoints.rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
    ((fun y => x * y * x⁻¹) '' C)
  let H := adelicHeight F G rho x
  have hH : 1 ≤ H := one_le_adelicHeight F G rho hn x
  let R := M * H ^ 2
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hH)
  obtain ⟨hfin, hcard⟩ := hcount R (zero_le_one.trans hR)
  let e := splitEntries F n ∘ adelicMatrix F G rho
  have he : Function.Injective e := (splitEntries_injective F n).comp
    (isClosedEmbedding_adelicMatrix F G rho hrho).injective
  have hem (p : AdelicGroupPoints F G) (hp : p ∈ P) :
      e p ∈ (Γ : Set (InfiniteEntries F n × FiniteEntries F n)) ∩
        (Metric.closedBall (0 : InfiniteEntries F n) R ×ˢ Q) := by
    obtain ⟨y, hy, rfl⟩ := hp.2
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨r, hr⟩ := hp.1
      rw [← hr]
      intro i j
      have eq := DFunLike.congr_fun (AdelicGroupPoints.rational_naturality F G rho) r
      change AdelicGroupPoints.rational F _
        (G.affinePointsTarget rho (CommAlgCat.of F F) r) =
          G.affinePointsTarget rho (CommAlgCat.of F (Adeles F))
            (AdelicGroupPoints.rational F G r) at eq
      have heq : adelicMatrix F G rho (AdelicGroupPoints.rational F G r) =
          AdelicGL.rational F n (GeneralLinearGroupPoints.rationalEquiv F n
            (G.affinePointsTarget rho (CommAlgCat.of F F) r)) := by
        change GeneralLinearGroupPoints.adelicHomeomorph F n
          (G.affinePointsTarget rho (CommAlgCat.of F (Adeles F))
            (AdelicGroupPoints.rational F G r)) = _
        rw [← eq]
        exact GeneralLinearGroupPoints.adelicHomeomorph_rational F n _
      change adelicMatrix F G rho (AdelicGroupPoints.rational F G r) i j ∈ principalAdeles F
      rw [heq, AdelicGL.rational_apply]
      exact ⟨_, rfl⟩
    · have hheight : adelicHeight F G rho (x * y * x⁻¹) ≤ R := calc
        _ ≤ adelicHeight F G rho (x * y) * H := by
          simpa only [adelicHeight_inv, H] using
            adelicHeight_mul_le F G rho hn (x * y) x⁻¹
        _ ≤ (H * adelicHeight F G rho y) * H :=
          mul_le_mul_of_nonneg_right (adelicHeight_mul_le F G rho hn x y)
            (zero_le_one.trans hH)
        _ ≤ (H * M) * H := by
          have hy' := (hb ⟨y, hy, rfl⟩).trans (le_max_right 1 b)
          gcongr
        _ = R := by dsimp [R]; ring
      have hb' := AdelicMatrixHeight.sublevel_subset F hn R
        (show AdelicMatrixHeight.height F n (adelicMatrix F G rho (x * y * x⁻¹)) ≤ R
          from hheight)
      apply mem_closedBall_zero_iff.mpr
      have hR₀ := zero_le_one.trans hR
      refine (pi_norm_le_iff_of_nonneg hR₀).mpr fun i =>
        (pi_norm_le_iff_of_nonneg hR₀).mpr fun j =>
          (pi_norm_le_iff_of_nonneg hR₀).mpr fun w => (hb'.1 i j).1 w
    · refine ⟨(AdelicGL.finite F n (adelicMatrix F G rho x), y), ⟨hKD x hx, hy⟩, ?_⟩
      ext i j
      simp only [f, ← map_inv, ← map_mul, AdelicGL.finite_apply, e,
        Function.comp_apply, splitEntries]
  refine ⟨hfin.of_injOn hem he.injOn, ?_⟩
  calc
    (P.ncard : ℝ) ≤ _ := by exact_mod_cast Set.ncard_le_ncard_of_injOn e hem he.injOn hfin
    _ ≤ A * (1 + R) ^ d := hcard
    _ ≤ A * (2 * R) ^ d := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) _) hA
    _ = (A * (2 * M) ^ d) * H ^ (2 * d) := by
      rw [pow_mul]
      simp only [R, mul_assoc, mul_pow]

end Langlands.Global
