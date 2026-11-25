import Langlands.Geometry.Manifold.LinearLieGroup.ClosedSubgroup
import Langlands.Geometry.Manifold.LinearLieGroup.Units
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Closed linear realizations of Lie groups

`IsClosedLinearRealization I ρ`, for a Lie group `G` modelled on `I` and a homomorphism
`ρ : G →* 𝔸ˣ` into the units of a finite-dimensional normed real algebra: `ρ` is a closed embedding,
`g ↦ ρ g` is smooth into `𝔸`, and a map `ℝᵐ → G` is smooth when its composition with `ρ` is smooth
into `𝔸`. The last condition is stated on the spaces `Fin m → ℝ` only; this suffices because the
charts of the image are the globally defined maps `Y ↦ k exp Y`.

Then the image `ρ.range` is a closed subgroup of `𝔸ˣ`, hence carries the exponential structure
`IsClosedLinearRealization.isExpLieAlgebra` (`ClosedSubgroup`), and `ρ` is a diffeomorphism onto
it (`IsClosedLinearRealization.contMDiff_rangeRestrict_and_symm`): smooth functions on `G` are the
transports of smooth functions on the image (`contMDiff_iff_comp_symm`). This is how statements
proved with the exponential structure (the Dixmier–Malliavin theorem of
`Langlands.Analysis.DixmierMalliavin.LinearGroup`) reach Lie groups given in the Library's notions,
without making the exponential charted space an instance.

`isClosedLinearRealization_id`: the identity of `𝔸ˣ` with Mathlib's structure is a closed linear
realization.
-/

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Langlands.LinearLieGroup

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

/-- A closed linear realization of a Lie group `G` (modelled on `I`): a homomorphism `ρ` into the units
of a finite-dimensional normed real algebra `𝔸` that is a closed topological embedding, is smooth
into `𝔸`, and through which smoothness of maps `ℝᵐ → G` is tested. -/
structure IsClosedLinearRealization
    {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [Group G] [TopologicalSpace G] [ChartedSpace H G]
    (ρ : G →* 𝔸ˣ) : Prop where
  /-- `ρ` is a closed embedding. -/
  isClosedEmbedding : Topology.IsClosedEmbedding ρ
  /-- `g ↦ ρ g` is smooth into `𝔸`. -/
  contMDiff_val : ContMDiff I 𝓘(ℝ, 𝔸) ∞ fun g => ((ρ g : 𝔸ˣ) : 𝔸)
  /-- A map `p : ℝᵐ → G` is smooth when `x ↦ ρ (p x)` is smooth into `𝔸`. -/
  contMDiff_of_val : ∀ {m : ℕ} (p : (Fin m → ℝ) → G),
    ContDiff ℝ ∞ (fun x => ((ρ (p x) : 𝔸ˣ) : 𝔸)) → ContMDiff 𝓘(ℝ, Fin m → ℝ) I ∞ p

namespace IsExpLieAlgebra

variable {K : Subgroup 𝔸ˣ} {𝔨 : Submodule ℝ 𝔸} (hK : IsExpLieAlgebra K 𝔨)

/-- Smoothness at `k` of a map from a linear Lie group (with its exponential charts) into a manifold
is smoothness at `0` of `Y ↦ f (k exp Y)`. -/
theorem contMDiffAt_iff_expG_manifold {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} {f : K → M} {k : K} :
    (letI := hK.chartedSpace; ContMDiffAt 𝓘(ℝ, 𝔨) I n f k) ↔
      ContMDiffAt 𝓘(ℝ, 𝔨) I n (fun Y : 𝔨 => f (k * hK.expG Y)) 0 := by
  let := hK.chartedSpace
  have := hK.isManifold n
  rw [contMDiffAt_iff_source]
  have e1 : (extChartAt 𝓘(ℝ, 𝔨) k) k = 0 := by
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
      Function.id_comp]
    exact hK.chart_self k
  have e2 : f ∘ (extChartAt 𝓘(ℝ, 𝔨) k).symm = fun Y : 𝔨 => f (k * hK.expG Y) := by
    funext Y
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id]
    rfl
  rw [e1, e2, modelWithCornersSelf_coe, range_id, contMDiffWithinAt_univ]

end IsExpLieAlgebra

namespace IsClosedLinearRealization

variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {ρ : G →* 𝔸ˣ} (hρ : IsClosedLinearRealization I ρ)
include hρ

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- The image of a closed linear realization is a closed subgroup of `𝔸ˣ`. -/
theorem isClosed_range : IsClosed (ρ.range : Set 𝔸ˣ) := by
  rw [MonoidHom.coe_range]
  exact hρ.isClosedEmbedding.isClosed_range

/-- The image of a closed linear realization carries the exponential structure of its Lie algebra
(`isExpLieAlgebra_of_isClosed`). -/
theorem isExpLieAlgebra : IsExpLieAlgebra ρ.range (lieSubmodule ρ.range hρ.isClosed_range) :=
  isExpLieAlgebra_of_isClosed ρ.range hρ.isClosed_range

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- `ρ` is a bijection onto its image. -/
theorem bijective_rangeRestrict : Function.Bijective ρ.rangeRestrict :=
  ⟨fun _ _ h => hρ.isClosedEmbedding.injective (congrArg Subtype.val h), ρ.rangeRestrict_surjective⟩

/-- `ρ` as an isomorphism of topological groups from `G` onto its image. -/
def rangeEquiv : G ≃ₜ* ρ.range where
  toMulEquiv := MulEquiv.ofBijective ρ.rangeRestrict hρ.bijective_rangeRestrict
  continuous_toFun := hρ.isClosedEmbedding.continuous.subtype_mk _
  continuous_invFun := by
    rw [hρ.isClosedEmbedding.isEmbedding.continuous_iff]
    have : ⇑ρ ∘ (MulEquiv.ofBijective ρ.rangeRestrict hρ.bijective_rangeRestrict).invFun =
        Subtype.val := by
      funext k
      exact congrArg Subtype.val
        ((MulEquiv.ofBijective ρ.rangeRestrict hρ.bijective_rangeRestrict).apply_symm_apply k)
    rw [this]
    exact continuous_subtype_val

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- `rangeEquiv` is `ρ`. -/
@[simp] theorem coe_rangeEquiv (g : G) : ((hρ.rangeEquiv g : ρ.range) : 𝔸ˣ) = ρ g := rfl

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- `ρ` inverts `rangeEquiv.symm`. -/
@[simp] theorem map_rangeEquiv_symm (k : ρ.range) : ρ (hρ.rangeEquiv.symm k) = k :=
  congrArg Subtype.val (hρ.rangeEquiv.apply_symm_apply k)

/-- **The realization is a diffeomorphism onto its image** with the exponential structure: `rangeEquiv`
and its inverse are smooth. The first part is `IsExpLieAlgebra.contMDiffAt_of_val` applied to
`contMDiff_val`; for the second, in the chart at `k` the inverse is `Y ↦ ρ⁻¹ (k exp Y)`, which is
smooth by `contMDiff_of_val` after a choice of linear coordinates on the Lie algebra. -/
theorem contMDiff_rangeRestrict_and_symm :
    letI := hρ.isExpLieAlgebra.chartedSpace
    ContMDiff I 𝓘(ℝ, lieSubmodule ρ.range hρ.isClosed_range) ∞ hρ.rangeEquiv ∧
      ContMDiff 𝓘(ℝ, lieSubmodule ρ.range hρ.isClosed_range) I ∞ hρ.rangeEquiv.symm := by
  set hK := hρ.isExpLieAlgebra
  let := hK.chartedSpace
  refine ⟨fun x => hK.contMDiffAt_of_val (hρ.contMDiff_val x), fun k => ?_⟩
  rw [hK.contMDiffAt_iff_expG_manifold]
  let 𝔨 := lieSubmodule ρ.range hρ.isClosed_range
  let b := Module.finBasis ℝ 𝔨
  let L : 𝔨 ≃L[ℝ] (Fin (Module.finrank ℝ 𝔨) → ℝ) := b.equivFun.toContinuousLinearEquiv
  let q : (Fin (Module.finrank ℝ 𝔨) → ℝ) → G := fun x => hρ.rangeEquiv.symm (k * hK.expG (L.symm x))
  have hq : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ 𝔨) → ℝ) I ∞ q := by
    refine hρ.contMDiff_of_val q ?_
    have e : (fun x => ((ρ (q x) : 𝔸ˣ) : 𝔸)) =
        fun x => ((k : 𝔸ˣ) : 𝔸) * NormedSpace.exp ((L.symm x : 𝔨) : 𝔸) := by
      funext x
      simp only [q, map_rangeEquiv_symm, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    rw [e]
    exact contDiff_const.mul ((contDiff_exp 𝔸).comp (𝔨.subtypeL.contDiff.comp L.symm.contDiff))
  have e : (fun Y : 𝔨 => hρ.rangeEquiv.symm (k * hK.expG Y)) = q ∘ L := by
    funext Y
    simp only [q, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [e]
  exact (hq.comp L.contDiff.contMDiff).contMDiffAt

/-- A function on `G` is smooth if and only if its transport to the image of `ρ` is smooth for the
exponential charts. -/
theorem contMDiff_iff_comp_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : G → F) :
    ContMDiff I 𝓘(ℝ, F) ∞ f ↔
      (letI := hρ.isExpLieAlgebra.chartedSpace;
        ContMDiff 𝓘(ℝ, lieSubmodule ρ.range hρ.isClosed_range) 𝓘(ℝ, F) ∞
          (f ∘ hρ.rangeEquiv.symm)) := by
  let := hρ.isExpLieAlgebra.chartedSpace
  obtain ⟨h1, h2⟩ := hρ.contMDiff_rangeRestrict_and_symm
  refine ⟨fun hf => hf.comp h2, fun hf => ?_⟩
  have e : f = (f ∘ hρ.rangeEquiv.symm) ∘ hρ.rangeEquiv := by
    funext g; simp
  rw [e]
  exact hf.comp h1

end IsClosedLinearRealization

omit [FiniteDimensional ℝ 𝔸] in
/-- The identity of `𝔸ˣ`, with Mathlib's manifold structure on `𝔸ˣ`, is a closed linear realization. -/
theorem isClosedLinearRealization_id :
    IsClosedLinearRealization 𝓘(ℝ, 𝔸) (MonoidHom.id 𝔸ˣ) where
  isClosedEmbedding := Topology.IsClosedEmbedding.id
  contMDiff_val := Units.contMDiff_val
  contMDiff_of_val := fun p hp => contMDiff_units_of_contDiff_val p hp

end Langlands.LinearLieGroup
