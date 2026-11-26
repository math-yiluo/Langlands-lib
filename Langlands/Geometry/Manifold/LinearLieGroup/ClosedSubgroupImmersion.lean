import Langlands.Geometry.Manifold.LinearLieGroup.Realization
import Mathlib.Geometry.Manifold.Immersion

/-! # Closed subgroups of linearly realized Lie groups are embedded Lie subgroups

Let `G` be a group with a manifold structure modelled on a normed space `E`, and let
`ρ : G →* 𝔸ˣ` be a closed linear realization. Every closed subgroup `S` of `G` carries a Lie group
structure modelled on `Fin e → ℝ`, in its subspace topology, for which the inclusion `S → G` is an
immersion. The charts of `S` are the exponential charts of its image `ρ(S)`, a closed subgroup of
`𝔸ˣ`, read in a basis of its Lie algebra. -/

noncomputable section

open Set Filter Topology Function
open scoped Manifold ContDiff

namespace Langlands.LinearLieGroup

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

local notation "𝔢" => expPartialHomeomorph 𝔸

section RangeHomeomorph

variable {M : Type*} [Group M] [TopologicalSpace M] {f : M →* 𝔸ˣ}

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- A closed embedding into `𝔸ˣ` is a bijection onto its image. -/
theorem bijective_rangeRestrict_of_isClosedEmbedding (hf : IsClosedEmbedding f) :
    Bijective f.rangeRestrict :=
  ⟨fun _ _ h => hf.injective (congrArg Subtype.val h), f.rangeRestrict_surjective⟩

/-- A homomorphism that is a closed embedding into `𝔸ˣ`, as an isomorphism of topological groups
onto its image. -/
def rangeHomeomorph (hf : IsClosedEmbedding f) : M ≃ₜ* f.range where
  toMulEquiv := MulEquiv.ofBijective f.rangeRestrict (bijective_rangeRestrict_of_isClosedEmbedding hf)
  continuous_toFun := hf.continuous.subtype_mk _
  continuous_invFun := by
    rw [hf.isEmbedding.continuous_iff]
    have : ⇑f ∘ (MulEquiv.ofBijective f.rangeRestrict
        (bijective_rangeRestrict_of_isClosedEmbedding hf)).invFun = Subtype.val := by
      funext k
      exact congrArg Subtype.val
        ((MulEquiv.ofBijective f.rangeRestrict
          (bijective_rangeRestrict_of_isClosedEmbedding hf)).apply_symm_apply k)
    rw [this]
    exact continuous_subtype_val

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
@[simp] theorem coe_rangeHomeomorph (hf : IsClosedEmbedding f) (m : M) :
    ((rangeHomeomorph hf m : f.range) : 𝔸ˣ) = f m := rfl

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
@[simp] theorem map_rangeHomeomorph_symm (hf : IsClosedEmbedding f) (k : f.range) :
    f ((rangeHomeomorph hf).symm k) = k :=
  congrArg Subtype.val ((rangeHomeomorph hf).apply_symm_apply k)

end RangeHomeomorph

section ModelEquiv

/-- Two manifolds that are smoothly inverse to each other have linearly isomorphic model spaces:
the derivatives at corresponding points are inverse to each other. -/
theorem nonempty_equiv_of_contMDiff_inverse {E F M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N] {φ : M → N} {ψ : N → M}
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ φ) (hψ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ψ)
    (hl : LeftInverse ψ φ) (hr : RightInverse ψ φ) (x : M) : Nonempty (E ≃L[ℝ] F) := by
  have hφd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) φ x := (hφ x).mdifferentiableAt (by simp)
  have hψd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) ψ (φ x) := (hψ (φ x)).mdifferentiableAt (by simp)
  let A : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) φ x
  let B : F →L[ℝ] E := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ (φ x)
  have hA : ∀ x₀ : M, x₀ = x → HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) φ x₀ A := by
    rintro _ rfl
    exact hφd.hasMFDerivAt
  have hB : HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, E) ψ (φ x) B := hψd.hasMFDerivAt
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E := by
    have hc := (HasMFDerivAt.comp x hB (hA x rfl)).mfderiv
    have hid : ψ ∘ φ = id := funext hl
    rw [hid, mfderiv_id] at hc
    exact hc.symm
  have hAB : A.comp B = ContinuousLinearMap.id ℝ F := by
    have hc := (HasMFDerivAt.comp (φ x) (hA (ψ (φ x)) (hl x)) hB).mfderiv
    have hid : φ ∘ ψ = id := funext hr
    rw [hid, mfderiv_id] at hc
    exact hc.symm
  exact ⟨ContinuousLinearEquiv.equivOfInverse A B
    (fun v => congrArg (fun T : E →L[ℝ] E => T v) hBA)
    (fun w => congrArg (fun T : F →L[ℝ] F => T w) hAB)⟩

end ModelEquiv

namespace IsClosedLinearRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  {ρ : G →* 𝔸ˣ} (hρ : IsClosedLinearRealization 𝓘(ℝ, E) ρ)
  {S : Subgroup G} (hS : IsClosed (S : Set G))

include hρ hS

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- The restriction of `ρ` to a closed subgroup is a closed embedding. -/
theorem isClosedEmbedding_comp_subtype : IsClosedEmbedding (ρ.comp S.subtype) :=
  hρ.isClosedEmbedding.comp hS.isClosedEmbedding_subtypeVal

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- The image `ρ(S)` of a closed subgroup is closed in `𝔸ˣ`. -/
theorem isClosed_subgroupRange : IsClosed ((ρ.comp S.subtype).range : Set 𝔸ˣ) := by
  rw [MonoidHom.coe_range]
  exact (hρ.isClosedEmbedding_comp_subtype hS).isClosed_range

/-- The Lie algebra of `ρ(S)`. -/
def subgroupLie : Submodule ℝ 𝔸 :=
  lieSubmodule (ρ.comp S.subtype).range (hρ.isClosed_subgroupRange hS)

/-- `ρ(S)` carries the exponential structure of its Lie algebra. -/
theorem isExpLieAlgebra_subgroup :
    IsExpLieAlgebra (ρ.comp S.subtype).range (hρ.subgroupLie hS) :=
  isExpLieAlgebra_of_isClosed _ (hρ.isClosed_subgroupRange hS)

/-- The dimension of `S`. -/
def subgroupDim : ℕ := Module.finrank ℝ (hρ.subgroupLie hS)

/-- Linear coordinates on the Lie algebra of `ρ(S)`. -/
def subgroupCoord : hρ.subgroupLie hS ≃L[ℝ] (Fin (hρ.subgroupDim hS) → ℝ) :=
  (Module.finBasis ℝ (hρ.subgroupLie hS)).equivFun.toContinuousLinearEquiv

/-- `S` is isomorphic as a topological group to its image `ρ(S)`. -/
def subgroupHomeomorph : S ≃ₜ* (ρ.comp S.subtype).range :=
  rangeHomeomorph (hρ.isClosedEmbedding_comp_subtype hS)

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
@[simp] theorem coe_subgroupHomeomorph (s : S) :
    ((hρ.subgroupHomeomorph hS s : (ρ.comp S.subtype).range) : 𝔸ˣ) = ρ s := rfl

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
@[simp] theorem map_subgroupHomeomorph_symm (k : (ρ.comp S.subtype).range) :
    ρ ((hρ.subgroupHomeomorph hS).symm k) = k :=
  map_rangeHomeomorph_symm (hρ.isClosedEmbedding_comp_subtype hS) k

/-- The chart of `S` at `s`: the exponential chart of `ρ(S)` at `ρ s`, read in the linear
coordinates `subgroupCoord`. -/
def subgroupChart (s : S) : OpenPartialHomeomorph S (Fin (hρ.subgroupDim hS) → ℝ) :=
  ((hρ.subgroupHomeomorph hS).toHomeomorph.transOpenPartialHomeomorph
    ((hρ.isExpLieAlgebra_subgroup hS).chart (hρ.subgroupHomeomorph hS s))).trans
    (hρ.subgroupCoord hS).toHomeomorph.toOpenPartialHomeomorph

theorem subgroupChart_apply (s y : S) :
    hρ.subgroupChart hS s y = hρ.subgroupCoord hS
      ((hρ.isExpLieAlgebra_subgroup hS).chart (hρ.subgroupHomeomorph hS s)
        (hρ.subgroupHomeomorph hS y)) := rfl

theorem subgroupChart_symm_apply (s : S) (X : Fin (hρ.subgroupDim hS) → ℝ) :
    (hρ.subgroupChart hS s).symm X = (hρ.subgroupHomeomorph hS).symm
      (hρ.subgroupHomeomorph hS s *
        (hρ.isExpLieAlgebra_subgroup hS).expG ((hρ.subgroupCoord hS).symm X)) := rfl

theorem mem_subgroupChart_source (s y : S) :
    y ∈ (hρ.subgroupChart hS s).source ↔
      ((((ρ s)⁻¹ * ρ y : 𝔸ˣ)) : 𝔸) ∈ (hρ.isExpLieAlgebra_subgroup hS).nhdOne := by
  simp [subgroupChart, IsExpLieAlgebra.chart]
  rfl

theorem mem_subgroupChart_target (s : S) (X : Fin (hρ.subgroupDim hS) → ℝ) :
    X ∈ (hρ.subgroupChart hS s).target ↔
      (((hρ.subgroupCoord hS).symm X : hρ.subgroupLie hS) : 𝔸) ∈
        (hρ.isExpLieAlgebra_subgroup hS).nhd := by
  simp [subgroupChart, IsExpLieAlgebra.chart]

/-- The charted space on `S` with the charts `subgroupChart`. It is a definition, installed with
`letI`. -/
@[instance_reducible]
def subgroupChartedSpace : ChartedSpace (Fin (hρ.subgroupDim hS) → ℝ) S where
  atlas := range (hρ.subgroupChart hS)
  chartAt := hρ.subgroupChart hS
  mem_chart_source s := by
    rw [mem_subgroupChart_source]
    simpa using (hρ.isExpLieAlgebra_subgroup hS).one_mem_nhdOne
  chart_mem_atlas s := mem_range_self s

/-- With the charts `subgroupChart`, `S` is a smooth manifold. The transition maps are
`X ↦ L (proj (log (c · exp (L⁻¹ X))))`. -/
theorem subgroupIsManifold (n : WithTop ℕ∞) :
    letI := hρ.subgroupChartedSpace hS
    IsManifold 𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ) n S := by
  let := hρ.subgroupChartedSpace hS
  set h₁ := hρ.isExpLieAlgebra_subgroup hS
  set L := hρ.subgroupCoord hS
  set ψ := hρ.subgroupHomeomorph hS
  apply isManifold_of_contDiffOn
  rintro e e' ⟨s, rfl⟩ ⟨s', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id_eq, range_id, inter_univ]
  set c : 𝔸 := ((((ρ s')⁻¹ * ρ s : 𝔸ˣ)) : 𝔸) with hc
  have key : ∀ X : Fin (hρ.subgroupDim hS) → ℝ,
      ((((ρ s')⁻¹ * ρ ((hρ.subgroupChart hS s).symm X) : 𝔸ˣ)) : 𝔸) =
        c * NormedSpace.exp ((L.symm X : hρ.subgroupLie hS) : 𝔸) := by
    intro X
    rw [subgroupChart_symm_apply, map_subgroupHomeomorph_symm]
    simp [hc, L, mul_assoc]
  have hmaps : MapsTo L.symm ((hρ.subgroupChart hS s).symm ≫ₕ hρ.subgroupChart hS s').source
      {Y : hρ.subgroupLie hS | c * NormedSpace.exp (Y : 𝔸) ∈ (𝔢).target} := by
    intro X hX
    rw [OpenPartialHomeomorph.trans_source] at hX
    have hX' : (hρ.subgroupChart hS s).symm X ∈ (hρ.subgroupChart hS s').source := hX.2
    rw [mem_subgroupChart_source, key] at hX'
    exact h₁.nhdOne_subset_target hX'
  refine (L.contDiff.comp_contDiffOn ((IsExpLieAlgebra.contDiffOn_proj_symm_mul_exp c _
    fun Y hY => hY).comp L.symm.contDiff.contDiffOn hmaps)).congr ?_
  intro X _
  change hρ.subgroupChart hS s' ((hρ.subgroupChart hS s).symm X) = _
  rw [subgroupChart_apply]
  simp only [Function.comp_apply]
  congr 2
  change subspaceProj _ ((𝔢).symm _) = _
  rw [← key]
  rfl

/-- The inclusion `S → 𝔸`, `s ↦ ρ s`, is smooth. -/
theorem contMDiff_subgroup_val (n : WithTop ℕ∞) :
    letI := hρ.subgroupChartedSpace hS
    ContMDiff 𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ) 𝓘(ℝ, 𝔸) n (fun s : S => ((ρ s : 𝔸ˣ) : 𝔸)) := by
  let := hρ.subgroupChartedSpace hS
  set L := hρ.subgroupCoord hS
  intro s
  rw [contMDiffAt_iff_source]
  have : (fun y : S => ((ρ y : 𝔸ˣ) : 𝔸)) ∘ (extChartAt 𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ) s).symm =
      fun X => ((ρ s : 𝔸ˣ) : 𝔸) * NormedSpace.exp ((L.symm X : hρ.subgroupLie hS) : 𝔸) := by
    funext X
    change ((ρ ((hρ.subgroupChart hS s).symm X) : 𝔸ˣ) : 𝔸) = _
    rw [subgroupChart_symm_apply, map_subgroupHomeomorph_symm]
    simp [L]
  rw [this]
  exact (contDiff_const.mul ((Langlands.LinearLieGroup.contDiff_exp 𝔸).comp
    ((hρ.subgroupLie hS).subtypeL.contDiff.comp L.symm.contDiff))).contMDiff.contMDiffAt
    |>.contMDiffWithinAt

omit [FiniteDimensional ℝ 𝔸] in
/-- `s ↦ ρ s` is a topological embedding of `S` into `𝔸`. -/
theorem isEmbedding_subgroup_val : IsEmbedding (fun s : S => ((ρ s : 𝔸ˣ) : 𝔸)) :=
  Units.isOpenEmbedding_val.isEmbedding.comp (hρ.isClosedEmbedding_comp_subtype hS).isEmbedding

/-- A map into `S` is smooth at a point when its composition with `s ↦ ρ s` is smooth there. -/
theorem contMDiffAt_subgroup_of_val {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] {n : WithTop ℕ∞} {f : M → S} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, 𝔸) n (fun y => ((ρ (f y) : 𝔸ˣ) : 𝔸)) x) :
    letI := hρ.subgroupChartedSpace hS
    ContMDiffAt I 𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ) n f x := by
  let := hρ.subgroupChartedSpace hS
  set L := hρ.subgroupCoord hS
  rw [contMDiffAt_iff_target]
  refine ⟨(hρ.isEmbedding_subgroup_val hS).continuousAt_iff.2 hf.continuousAt, ?_⟩
  set c : 𝔸 := (((ρ (f x))⁻¹ : 𝔸ˣ) : 𝔸) with hc
  have h1 : c * ((ρ (f x) : 𝔸ˣ) : 𝔸) = 1 := by simp [c]
  have hF : ContDiffAt ℝ n (fun a : 𝔸 => L (subspaceProj (hρ.subgroupLie hS) ((𝔢).symm (c * a))))
      (((ρ (f x) : 𝔸ˣ) : 𝔸)) := by
    have h3 : ContDiffAt ℝ n (fun a : 𝔸 => (𝔢).symm (c * a)) (((ρ (f x) : 𝔸ˣ) : 𝔸)) := by
      refine ContDiffAt.comp (g := (𝔢).symm) (f := fun a => c * a) _ ?_
        (contDiff_const.mul contDiff_id).contDiffAt
      simp only [h1]
      exact (contDiffOn_expPartialHomeomorph_symm 𝔸).contDiffAt
        ((𝔢).open_target.mem_nhds (one_mem_expPartialHomeomorph_target 𝔸))
    have h4 : ContDiff ℝ n (fun Y : 𝔸 => L (subspaceProj (hρ.subgroupLie hS) Y)) :=
      L.contDiff.comp (subspaceProj (hρ.subgroupLie hS)).contDiff
    exact h4.contDiffAt.comp (((ρ (f x) : 𝔸ˣ) : 𝔸)) h3
  have e : (extChartAt 𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ) (f x)) ∘ f =
      (fun a : 𝔸 => L (subspaceProj (hρ.subgroupLie hS) ((𝔢).symm (c * a)))) ∘
        (fun y => ((ρ (f y) : 𝔸ˣ) : 𝔸)) := by
    funext y
    change hρ.subgroupChart hS (f x) (f y) = _
    rw [subgroupChart_apply]
    simp [c, IsExpLieAlgebra.chart]
    rfl
  rw [e]
  exact ContDiffAt.comp_contMDiffAt hF hf

/-- With the charts `subgroupChart`, `S` is a Lie group. -/
theorem subgroupLieGroup (n : WithTop ℕ∞) :
    letI := hρ.subgroupChartedSpace hS
    LieGroup 𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ) n S := by
  let := hρ.subgroupChartedSpace hS
  exact {
    toIsManifold := hρ.subgroupIsManifold hS n
    contMDiff_mul := fun p => by
      refine hρ.contMDiffAt_subgroup_of_val hS ?_
      have : ContMDiff ((𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ)).prod
          𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ)) 𝓘(ℝ, 𝔸 × 𝔸) n
          (fun p : S × S => (((ρ p.1 : 𝔸ˣ) : 𝔸), ((ρ p.2 : 𝔸ˣ) : 𝔸))) :=
        ((hρ.contMDiff_subgroup_val hS n).comp contMDiff_fst).prodMk_space
            ((hρ.contMDiff_subgroup_val hS n).comp contMDiff_snd)
      have h := (contDiff_mul.comp_contMDiff this) p
      convert h using 1
      funext q
      simp
    contMDiff_inv := fun x => by
      refine hρ.contMDiffAt_subgroup_of_val hS ?_
      have hx : ContDiffAt ℝ n Ring.inverse (((ρ x : 𝔸ˣ) : 𝔸)) :=
        contDiffAt_ringInverse ℝ (ρ x)
      have := ContDiffAt.comp_contMDiffAt (f := fun x : S => ((ρ x : 𝔸ˣ) : 𝔸)) hx
                ((hρ.contMDiff_subgroup_val hS n) x)
      convert this using 1
      funext y
      simp }

omit [FiniteDimensional ℝ 𝔸] in
/-- The Lie algebra of `ρ(S)` lies in that of `ρ(G)`. -/
theorem subgroupLie_le :
    hρ.subgroupLie hS ≤ lieSubmodule ρ.range hρ.isClosed_range := fun _ hX t => by
  obtain ⟨y, hy⟩ := hX t
  exact ⟨y, hy⟩

omit hS in
/-- The Lie algebra of `ρ(G)` is linearly isomorphic to the model space `E` of `G`: the derivatives
at `1` of `ρ : G → ρ(G)` and of its inverse are inverse to each other. -/
theorem exists_lieSubmodule_equiv_model :
    Nonempty (lieSubmodule ρ.range hρ.isClosed_range ≃L[ℝ] E) := by
  obtain ⟨h1, h2⟩ := hρ.contMDiff_rangeRestrict_and_symm
  let := hρ.isExpLieAlgebra.chartedSpace
  exact (nonempty_equiv_of_contMDiff_inverse h1 h2 hρ.rangeEquiv.symm_apply_apply
    hρ.rangeEquiv.apply_symm_apply 1).map ContinuousLinearEquiv.symm

/-- **The inclusion of a closed subgroup is an immersion.** At `s ∈ S`, the chart of `S` is the
exponential chart of `ρ(S)` at `ρ s`, and the chart of `G` is the pullback by `ρ` of the
exponential chart of `ρ(G)` at `ρ s`, followed by a linear isomorphism of the Lie algebra of
`ρ(G)` with `E`. In these charts the inclusion is the linear inclusion of the Lie algebra of
`ρ(S)` into that of `ρ(G)`, `X ↦ (X, 0)` after the choice of a complement. -/
theorem isImmersion_subtype [IsManifold 𝓘(ℝ, E) ∞ G] :
    letI := hρ.subgroupChartedSpace hS
    Manifold.IsImmersion 𝓘(ℝ, Fin (hρ.subgroupDim hS) → ℝ) 𝓘(ℝ, E) ∞ ((↑) : S → G) := by
  let := hρ.subgroupChartedSpace hS
  have := hρ.subgroupIsManifold hS ∞
  obtain ⟨Lam⟩ := hρ.exists_lieSubmodule_equiv_model
  obtain ⟨h1, h2⟩ := hρ.contMDiff_rangeRestrict_and_symm
  let := hρ.isExpLieAlgebra.chartedSpace
  have := hρ.isExpLieAlgebra.isManifold ∞
  have hle := hρ.subgroupLie_le hS
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl
    ((hρ.subgroupLie hS).comap (lieSubmodule ρ.range hρ.isClosed_range).subtype)
  let P := (Submodule.prodEquivOfIsCompl _ W hW).toContinuousLinearEquiv
  let J := (Submodule.comapSubtypeEquivOfLe hle).symm.toContinuousLinearEquiv
  let equiv : ((Fin (hρ.subgroupDim hS) → ℝ) × W) ≃L[ℝ] E :=
    (((hρ.subgroupCoord hS).symm.trans J).prodCongr (ContinuousLinearEquiv.refl ℝ W)).trans
      (P.trans Lam)
  refine Manifold.IsImmersionOfComplement.isImmersion (F := W) fun s => ?_
  let g : ρ.range := hρ.rangeEquiv (s : G)
  let codChart : OpenPartialHomeomorph G E :=
    (hρ.rangeEquiv.toHomeomorph.transOpenPartialHomeomorph (hρ.isExpLieAlgebra.chart g)).trans
      Lam.toHomeomorph.toOpenPartialHomeomorph
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt equiv (chartAt _ s) codChart (mem_chart_source _ s) ?_
    (IsManifold.chart_mem_maximalAtlas s) ?_ ?_
  · simp [codChart, IsExpLieAlgebra.chart, g]
    change (((ρ s)⁻¹ : 𝔸ˣ) : 𝔸) * ((ρ s : 𝔸ˣ) : 𝔸) ∈ hρ.isExpLieAlgebra.nhdOne
    simpa using hρ.isExpLieAlgebra.one_mem_nhdOne
  · rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · have hc : ContMDiffOn 𝓘(ℝ, lieSubmodule ρ.range hρ.isClosed_range)
          𝓘(ℝ, lieSubmodule ρ.range hρ.isClosed_range) ∞ (hρ.isExpLieAlgebra.chart g)
          (hρ.isExpLieAlgebra.chart g).source := contMDiffOn_chart (x := g)
      have hmaps : MapsTo hρ.rangeEquiv codChart.source (hρ.isExpLieAlgebra.chart g).source := by
        intro y hy
        simp only [codChart, OpenPartialHomeomorph.trans_source,
          Homeomorph.transOpenPartialHomeomorph_source] at hy
        exact hy.1
      exact Lam.contDiff.contMDiff.comp_contMDiffOn
        (hc.comp (h1.contMDiffOn (s := codChart.source)) hmaps)
    · have hc : ContMDiffOn 𝓘(ℝ, lieSubmodule ρ.range hρ.isClosed_range)
          𝓘(ℝ, lieSubmodule ρ.range hρ.isClosed_range) ∞ (hρ.isExpLieAlgebra.chart g).symm
          (hρ.isExpLieAlgebra.chart g).target := contMDiffOn_chart_symm (x := g)
      have hmaps : MapsTo Lam.symm codChart.target (hρ.isExpLieAlgebra.chart g).target := by
        intro y hy
        simp only [codChart, OpenPartialHomeomorph.trans_target,
          Homeomorph.transOpenPartialHomeomorph_target] at hy
        exact hy.2
      exact h2.comp_contMDiffOn
        (hc.comp (Lam.symm.contDiff.contMDiff.contMDiffOn (s := codChart.target)) hmaps)
  · intro X hX
    simp only [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe_symm,
      modelWithCornersSelf_coe, preimage_id_eq, range_id, inter_univ, id] at hX
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, id]
    have hY : (((hρ.subgroupCoord hS).symm X : hρ.subgroupLie hS) : 𝔸) ∈
        (hρ.isExpLieAlgebra_subgroup hS).nhd := (hρ.mem_subgroupChart_target hS s X).1 hX
    have key : (((g⁻¹ * hρ.rangeEquiv ((hρ.subgroupChart hS s).symm X : G) : ρ.range) :
        𝔸ˣ) : 𝔸) =
          NormedSpace.exp (((hρ.subgroupCoord hS).symm X : hρ.subgroupLie hS) : 𝔸) := by
      rw [subgroupChart_symm_apply]
      simp [g]
    change Lam (subspaceProj (lieSubmodule ρ.range hρ.isClosed_range) ((𝔢).symm
      (((g⁻¹ * hρ.rangeEquiv ((hρ.subgroupChart hS s).symm X : G) : ρ.range) : 𝔸ˣ) : 𝔸))) =
        equiv (X, 0)
    rw [key, (hρ.isExpLieAlgebra_subgroup hS).symm_exp hY]
    simp only [equiv, P, J, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply]
    congr 1
    apply Subtype.ext
    rw [subspaceProj_of_mem (hle ((hρ.subgroupCoord hS).symm X).2)]
    simp

end IsClosedLinearRealization

end Langlands.LinearLieGroup
