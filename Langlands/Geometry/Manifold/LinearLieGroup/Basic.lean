import Langlands.Geometry.Manifold.LinearLieGroup.Exponential
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Algebra.Group.Units

/-!
# Linear Lie groups

Let `𝔸` be a finite-dimensional normed real algebra. For a subgroup `G` of `𝔸ˣ` and a subspace
`𝔤` of `𝔸`, `IsExpLieAlgebra G 𝔤` says that `exp` maps `𝔤` into `G` and that near `0` every `X`
with `exp X ∈ G` lies in `𝔤`. Then:

* `IsExpLieAlgebra.chartedSpace` is the charted space on `G` modelled on `𝔤` whose chart at `g`
  is `x ↦ log (g⁻¹ x)` (with the local logarithm of `Exponential`, projected to `𝔤`), with inverse
  `X ↦ g exp X`. It is a definition, not an instance, and is installed with
  `letI := h.chartedSpace`;
* for it, `G` is a smooth manifold and a Lie group (`isManifold`, `lieGroup`), the inclusion into
  `𝔸` is smooth (`contMDiff_val`), and a map into `G` is smooth when it is smooth into `𝔸`
  (`contMDiffAt_of_val`);
* a function `f` on `G` is smooth if and only if `Y ↦ f (g exp Y)` is smooth on `𝔤` for every `g`
  (`contMDiff_iff_expG`);
* `G` is closed in `𝔸ˣ` (`IsExpLieAlgebra.isClosed`), locally compact and second countable.

The structure is the vehicle of the Dixmier–Malliavin theorem on linear groups
(`Langlands.Analysis.DixmierMalliavin.LinearGroup`): its proof uses the exponential map, the
one-parameter subgroups `t ↦ exp (t X)` (`expG_add_smul`) and the coordinates of the second kind
`t ↦ ∏ exp (tᵢ Xᵢ)` (`prodExp`). By `Langlands.LinearLieGroup.isExpLieAlgebra_of_isClosed`
(`ClosedSubgroup`) every closed subgroup of `𝔸ˣ` carries the structure, and `𝔤` is then determined
by `G`.
-/

namespace Langlands.LinearLieGroup

open scoped Manifold ContDiff Topology
open NormedSpace Set

section LinearLie

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

/-- A continuous linear projection of `𝔸` onto the subspace `𝔤`, along a chosen complement. -/
noncomputable def subspaceProj (𝔤 : Submodule ℝ 𝔸) : 𝔸 →L[ℝ] 𝔤 :=
  LinearMap.toContinuousLinearMap
    (Submodule.projectionOnto 𝔤 _ (Submodule.exists_isCompl 𝔤).choose_spec)

omit [CompleteSpace 𝔸] in
/-- The projection onto `𝔤` is the identity on `𝔤`. -/
@[simp] theorem subspaceProj_coe (𝔤 : Submodule ℝ 𝔸) (X : 𝔤) : subspaceProj 𝔤 (X : 𝔸) = X :=
  Submodule.projectionOnto_apply_left _ X

omit [CompleteSpace 𝔸] in
/-- The projection onto `𝔤` fixes the elements of `𝔤`. -/
theorem subspaceProj_of_mem {𝔤 : Submodule ℝ 𝔸} {X : 𝔸} (hX : X ∈ 𝔤) :
    (subspaceProj 𝔤 X : 𝔸) = X := by
  simpa using congrArg Subtype.val (subspaceProj_coe 𝔤 ⟨X, hX⟩)

/-- `𝔤` is the Lie algebra of the subgroup `G` of `𝔸ˣ`, and `exp` identifies a neighbourhood of `0`
in `𝔤` with a neighbourhood of `1` in `G`: `exp` maps `𝔤` into `G`, and there is an open
neighbourhood `U` of `0`, inside the source of `expPartialHomeomorph 𝔸`, such that `X ∈ U` and
`exp X ∈ G` imply `X ∈ 𝔤`. -/
structure IsExpLieAlgebra (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) : Prop where
  /-- `exp` maps `𝔤` into `G`. -/
  expUnit_mem : ∀ X ∈ 𝔤, expUnit 𝔸 X ∈ G
  /-- Near `0`, the elements of `𝔸` whose exponential lies in `G` are in `𝔤`. -/
  exists_nhds : ∃ U : Set 𝔸, IsOpen U ∧ (0 : 𝔸) ∈ U ∧
    U ⊆ (expPartialHomeomorph 𝔸).source ∧ ∀ X ∈ U, expUnit 𝔸 X ∈ G → X ∈ 𝔤

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- The inclusion of a subgroup of `𝔸ˣ` into `𝔸` is continuous. -/
theorem continuous_val_val (G : Subgroup 𝔸ˣ) : Continuous (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
  Units.continuous_val.comp continuous_subtype_val

omit [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- The inclusion of a subgroup of `𝔸ˣ` into `𝔸` is a topological embedding. -/
theorem isEmbedding_coe_coe {G : Subgroup 𝔸ˣ} :
    Topology.IsEmbedding (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
  Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal

omit [CompleteSpace 𝔸] in
/-- A subgroup of the units of a finite-dimensional normed real algebra is second countable. -/
theorem secondCountableTopology_subgroup (G : Subgroup 𝔸ˣ) : SecondCountableTopology G :=
  isEmbedding_coe_coe.secondCountableTopology

namespace IsExpLieAlgebra

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

local notation "𝔢" => expPartialHomeomorph 𝔸

/-- The neighbourhood of `0` in `𝔸` given by `IsExpLieAlgebra.exists_nhds` (a choice). -/
def nhd : Set 𝔸 := h.exists_nhds.choose

omit [FiniteDimensional ℝ 𝔸] in
/-- The chosen neighbourhood of `0` is open. -/
theorem isOpen_nhd : IsOpen h.nhd := h.exists_nhds.choose_spec.1
omit [FiniteDimensional ℝ 𝔸] in
/-- The chosen neighbourhood contains `0`. -/
theorem zero_mem_nhd : (0 : 𝔸) ∈ h.nhd := h.exists_nhds.choose_spec.2.1
omit [FiniteDimensional ℝ 𝔸] in
/-- The chosen neighbourhood of `0` lies in the source of `expPartialHomeomorph 𝔸`. -/
theorem nhd_subset : h.nhd ⊆ (𝔢).source := h.exists_nhds.choose_spec.2.2.1
omit [FiniteDimensional ℝ 𝔸] in
/-- In the chosen neighbourhood of `0`, `exp X ∈ G` implies `X ∈ 𝔤`. -/
theorem mem_of_mem_nhd {X : 𝔸} (hX : X ∈ h.nhd) (hG : expUnit 𝔸 X ∈ G) : X ∈ 𝔤 :=
  h.exists_nhds.choose_spec.2.2.2 X hX hG

/-- The image under `exp` of the chosen neighbourhood of `0`: an open neighbourhood of `1` in `𝔸`. -/
def nhdOne : Set 𝔸 := 𝔢 '' h.nhd

omit [FiniteDimensional ℝ 𝔸] in
/-- The neighbourhood `nhdOne` of `1` is open. -/
theorem isOpen_nhdOne : IsOpen h.nhdOne :=
    (𝔢).isOpen_image_of_subset_source h.isOpen_nhd h.nhd_subset

omit [FiniteDimensional ℝ 𝔸] in
/-- `nhdOne` lies in the domain of the local logarithm. -/
theorem nhdOne_subset_target : h.nhdOne ⊆ (𝔢).target := by
  rintro _ ⟨X, hX, rfl⟩; exact (𝔢).map_source (h.nhd_subset hX)

omit [FiniteDimensional ℝ 𝔸] in
/-- The local logarithm maps `nhdOne` into the chosen neighbourhood of `0`. -/
theorem symm_mem_nhd {a : 𝔸} (ha : a ∈ h.nhdOne) : (𝔢).symm a ∈ h.nhd := by
  obtain ⟨X, hX, rfl⟩ := ha; rwa [(𝔢).left_inv (h.nhd_subset hX)]

omit [FiniteDimensional ℝ 𝔸] in
/-- `exp` inverts the local logarithm on `nhdOne`. -/
theorem exp_symm {a : 𝔸} (ha : a ∈ h.nhdOne) : exp ((𝔢).symm a) = a :=
  (𝔢).right_inv (h.nhdOne_subset_target ha)

omit [FiniteDimensional ℝ 𝔸] in
/-- `exp` maps the chosen neighbourhood of `0` into `nhdOne`. -/
theorem exp_mem_nhdOne {X : 𝔸} (hX : X ∈ h.nhd) : exp X ∈ h.nhdOne := ⟨X, hX, rfl⟩

omit [FiniteDimensional ℝ 𝔸] in
/-- The local logarithm inverts `exp` on the chosen neighbourhood of `0`. -/
theorem symm_exp {X : 𝔸} (hX : X ∈ h.nhd) : (𝔢).symm (exp X) = X := (𝔢).left_inv (h.nhd_subset hX)

omit [FiniteDimensional ℝ 𝔸] in
/-- `1 ∈ nhdOne`. -/
theorem one_mem_nhdOne : (1 : 𝔸) ∈ h.nhdOne := by
  simpa [exp_zero] using h.exp_mem_nhdOne h.zero_mem_nhd

/-- The exponential map `𝔤 → G`. -/
noncomputable def expG (X : 𝔤) : G := ⟨expUnit 𝔸 X, h.expUnit_mem X X.2⟩

omit [FiniteDimensional ℝ 𝔸] in
/-- The value of `expG` in `𝔸` is `exp`. -/
@[simp] theorem coe_expG (X : 𝔤) : ((h.expG X : 𝔸ˣ) : 𝔸) = exp (X : 𝔸) := rfl

omit [FiniteDimensional ℝ 𝔸] in
/-- The exponential map `𝔤 → G` is continuous. -/
theorem continuous_expG : Continuous h.expG :=
  ((continuous_expUnit 𝔸).comp continuous_subtype_val).subtype_mk _

omit [FiniteDimensional ℝ 𝔸] in
/-- The local logarithm of an element of `G` close to `1` lies in `𝔤`. -/
theorem symm_mem_lie {x : G} (hx : ((x : 𝔸ˣ) : 𝔸) ∈ h.nhdOne) : (𝔢).symm ((x : 𝔸ˣ) : 𝔸) ∈ 𝔤 := by
  apply h.mem_of_mem_nhd (h.symm_mem_nhd hx)
  have : expUnit 𝔸 ((𝔢).symm ((x : 𝔸ˣ) : 𝔸)) = (x : 𝔸ˣ) := Units.ext (h.exp_symm hx)
  rw [this]; exact x.2

/-- The exponential chart of `G` at `g`: `x ↦ log (g⁻¹ x)`, projected to `𝔤`, defined for `g⁻¹ x` in
`nhdOne`, with inverse `X ↦ g · exp X`. -/
noncomputable def chart (g : G) : OpenPartialHomeomorph G 𝔤 where
  toFun x := subspaceProj 𝔤 ((𝔢).symm (((g⁻¹ * x : G) : 𝔸ˣ) : 𝔸))
  invFun X := g * h.expG X
  source := {x | (((g⁻¹ * x : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne}
  target := {X | (X : 𝔸) ∈ h.nhd}
  map_source' x hx := by
    simp only [mem_ofPred_eq] at hx ⊢
    rw [subspaceProj_of_mem (h.symm_mem_lie hx)]
    exact h.symm_mem_nhd hx
  map_target' X hX := by
    simp only [mem_ofPred_eq, inv_mul_cancel_left] at hX ⊢
    exact h.exp_mem_nhdOne hX
  left_inv' x hx := by
    have e1 := subspaceProj_of_mem (h.symm_mem_lie hx)
    have e2 := h.exp_symm hx
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_expG, Subgroup.coe_inv] at e1 e2 ⊢
    rw [e1, e2, ← mul_assoc, Units.mul_inv, one_mul]
  right_inv' X hX := by
    simp only [mem_ofPred_eq] at hX
    simp only [inv_mul_cancel_left, coe_expG]
    rw [h.symm_exp hX, subspaceProj_coe]
  open_source := h.isOpen_nhdOne.preimage
    ((continuous_val_val G).comp (continuous_const.mul continuous_id))
  open_target := h.isOpen_nhd.preimage continuous_subtype_val
  continuousOn_toFun := by
    refine (subspaceProj 𝔤).continuous.comp_continuousOn ?_
    refine (𝔢).continuousOn_symm.comp
      ((continuous_val_val G).comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx; exact h.nhdOne_subset_target hx
  continuousOn_invFun := (continuous_const.mul h.continuous_expG).continuousOn

end IsExpLieAlgebra

namespace IsExpLieAlgebra

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

local notation "𝔢" => expPartialHomeomorph 𝔸

/-- The charted space on `G` modelled on `𝔤`, with the exponential charts `chart g`. It is a
definition, not an instance: it is installed locally with `letI := h.chartedSpace`, so that it
does not compete with other charted spaces (for instance Mathlib's on `𝔸ˣ`). -/
@[instance_reducible]
noncomputable def chartedSpace : ChartedSpace 𝔤 G where
  atlas := range h.chart
  chartAt := h.chart
  mem_chart_source g := by
    show (((g⁻¹ * g : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne
    simpa using h.one_mem_nhdOne
  chart_mem_atlas g := mem_range_self g

/-- `X ↦ proj (log (c · exp X))` is smooth where it is defined: the transition maps of the exponential
charts have this form. -/
theorem contDiffOn_proj_symm_mul_exp {n : WithTop ℕ∞} (c : 𝔸) (s : Set 𝔤)
    (hs : ∀ X ∈ s, c * exp (X : 𝔸) ∈ (𝔢).target) :
    ContDiffOn ℝ n (fun X : 𝔤 => subspaceProj 𝔤 ((𝔢).symm (c * exp (X : 𝔸)))) s :=
  (subspaceProj 𝔤).contDiff.comp_contDiffOn ((contDiffOn_expPartialHomeomorph_symm 𝔸).comp
    (contDiff_const.mul ((contDiff_exp 𝔸).comp 𝔤.subtypeL.contDiff)).contDiffOn hs)

/-- With the exponential charts, `G` is a smooth manifold modelled on `𝔤`. -/
theorem isManifold (n : WithTop ℕ∞) : letI := h.chartedSpace; IsManifold 𝓘(ℝ, 𝔤) n G := by
  let := h.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨g, rfl⟩ ⟨g', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id_eq, range_id, inter_univ]
  have key : ∀ X : 𝔤, ((((g' : G)⁻¹ * (h.chart g).symm X : G) : 𝔸ˣ) : 𝔸) =
      ((((g'⁻¹ * g : G) : 𝔸ˣ) : 𝔸)) * exp (X : 𝔸) := by
    intro X; show _ = _; simp [chart, expG, mul_assoc]
  refine (contDiffOn_proj_symm_mul_exp ((((g'⁻¹ * g : G) : 𝔸ˣ) : 𝔸)) _ ?_).congr ?_
  · intro X hX
    rw [← key]
    exact h.nhdOne_subset_target hX.2
  · intro X _
    exact congrArg (fun a => subspaceProj 𝔤 ((𝔢).symm a)) (key X)

/-- The inclusion `G → 𝔸` is smooth for the exponential charts. -/
theorem contMDiff_val (n : WithTop ℕ∞) : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔸) n (fun x : G => ((x : 𝔸ˣ) : 𝔸)) := by
  let := h.chartedSpace
  intro x
  rw [contMDiffAt_iff_source]
  have : (fun x : G => ((x : 𝔸ˣ) : 𝔸)) ∘ (extChartAt 𝓘(ℝ, 𝔤) x).symm =
      fun X : 𝔤 => ((x : 𝔸ˣ) : 𝔸) * exp (X : 𝔸) := rfl
  rw [this]
  exact (contDiff_const.mul ((contDiff_exp 𝔸).comp 𝔤.subtypeL.contDiff)).contMDiff.contMDiffAt
    |>.contMDiffWithinAt

/-- A map into `G` is smooth at a point when its composition with the inclusion `G → 𝔸` is: the chart at
`f x` is a smooth function of the ambient coordinate near `f x`. -/
theorem contMDiffAt_of_val {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {n : WithTop ℕ∞} {f : M → G} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, 𝔸) n (fun y => ((f y : 𝔸ˣ) : 𝔸)) x) :
    letI := h.chartedSpace; ContMDiffAt I 𝓘(ℝ, 𝔤) n f x := by
  let := h.chartedSpace
  rw [contMDiffAt_iff_target]
  refine ⟨?_, ?_⟩
  · have hemb : Topology.IsEmbedding (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
      Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    exact hemb.continuousAt_iff.2 hf.continuousAt
  · set c : 𝔸 := ((((f x)⁻¹ : G) : 𝔸ˣ) : 𝔸) with hc
    have h1 : c * ((f x : 𝔸ˣ) : 𝔸) = 1 := by simp [c]
    have hF : ContDiffAt ℝ n (fun a : 𝔸 => subspaceProj 𝔤 ((𝔢).symm (c * a)))
        (((f x : 𝔸ˣ) : 𝔸)) := by
      refine (subspaceProj 𝔤).contDiff.contDiffAt.comp _ ?_
      refine ContDiffAt.comp (g := (𝔢).symm) (f := fun a => c * a) _ ?_
        (contDiff_const.mul contDiff_id).contDiffAt
      simp only [h1]
      exact (contDiffOn_expPartialHomeomorph_symm 𝔸).contDiffAt
        ((𝔢).open_target.mem_nhds (one_mem_expPartialHomeomorph_target 𝔸))
    exact ContDiffAt.comp_contMDiffAt (f := fun y => ((f y : 𝔸ˣ) : 𝔸)) hF hf

/-- With the exponential charts, `G` is a Lie group modelled on `𝔤`. -/
theorem lieGroup (n : WithTop ℕ∞) : letI := h.chartedSpace; LieGroup 𝓘(ℝ, 𝔤) n G := by
  let := h.chartedSpace
  exact {
    toIsManifold := h.isManifold n
    contMDiff_mul := fun p => by
      refine h.contMDiffAt_of_val ?_
      have : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, 𝔤)) 𝓘(ℝ, 𝔸 × 𝔸) n
          (fun p : G × G => (((p.1 : 𝔸ˣ) : 𝔸), ((p.2 : 𝔸ˣ) : 𝔸))) :=
        ((h.contMDiff_val n).comp contMDiff_fst).prodMk_space
            ((h.contMDiff_val n).comp contMDiff_snd)
      exact (contDiff_mul.comp_contMDiff this) p
    contMDiff_inv := fun x => by
      refine h.contMDiffAt_of_val ?_
      have hx : ContDiffAt ℝ n Ring.inverse (((x : 𝔸ˣ) : 𝔸)) := contDiffAt_ringInverse ℝ (x : 𝔸ˣ)
      have := ContDiffAt.comp_contMDiffAt (f := fun x : G => ((x : 𝔸ˣ) : 𝔸)) hx
                ((h.contMDiff_val n) x)
      convert this using 1
      funext y
      simp }

end IsExpLieAlgebra

end LinearLie

section Basic

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

omit [FiniteDimensional ℝ 𝔸] in
/-- `expG ((s + t) • X) = expG (s • X) * expG (t • X)`: one-parameter subgroups. -/
theorem expG_add_smul (X : 𝔤) (s t : ℝ) :
    h.expG ((s + t) • X) = h.expG (s • X) * h.expG (t • X) := by
  apply Subtype.ext; apply Units.ext
  simp only [coe_expG, Submodule.coe_smul, Subgroup.coe_mul, Units.val_mul, add_smul]
  exact exp_add_of_commute' ((Commute.refl (X : 𝔸)).smul_left s |>.smul_right t)

/-- The coordinates of the second kind: `t ↦ ∏ᵢ exp (tᵢ Xᵢ)` (ordered product). -/
noncomputable def prodExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) : G :=
  (List.ofFn fun i => h.expG (t i • X i)).prod

/-- The chart at `g` sends `g` to `0`. -/
theorem chart_self (g : G) : h.chart g g = 0 := by
  show subspaceProj 𝔤 ((expPartialHomeomorph 𝔸).symm (((g⁻¹ * g : G) : 𝔸ˣ) : 𝔸)) = 0
  simp [expPartialHomeomorph_symm_one]

/-- Smoothness at `g` of a function on `G` is smoothness at `0` of `Y ↦ f (g · exp Y)` on `𝔤`. -/
theorem contMDiffAt_iff_expG {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {n : WithTop ℕ∞} {f : G → E'} {g : G} :
    (letI := h.chartedSpace; ContMDiffAt 𝓘(ℝ, 𝔤) 𝓘(ℝ, E') n f g) ↔
      ContDiffAt ℝ n (fun Y : 𝔤 => f (g * h.expG Y)) 0 := by
  let := h.chartedSpace
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  have e1 : (extChartAt 𝓘(ℝ, 𝔤) g) g = 0 := by
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
      Function.id_comp]
    exact h.chart_self g
  have e2 : f ∘ (extChartAt 𝓘(ℝ, 𝔤) g).symm = fun Y : 𝔤 => f (g * h.expG Y) := by
    funext Y
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id]
    rfl
  rw [e1, e2, modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]

include h in

/-- `G` is locally compact (it is a finite-dimensional manifold). -/
theorem locallyCompactSpace : LocallyCompactSpace G := by
  let := h.chartedSpace
  exact ChartedSpace.locallyCompactSpace 𝔤 G


omit [FiniteDimensional ℝ 𝔸] in
/-- `expG 0 = 1`. -/
@[simp] theorem expG_zero : h.expG 0 = 1 := by
  apply Subtype.ext; apply Units.ext; simp

omit [FiniteDimensional ℝ 𝔸] in
/-- `expG (-X) = (expG X)⁻¹`. -/
theorem expG_neg (X : 𝔤) : h.expG (-X) = (h.expG X)⁻¹ := by
  apply Subtype.ext; apply Units.ext
  show exp (-(X : 𝔸)) = ↑((expUnit 𝔸 (X : 𝔸))⁻¹)
  rw [coe_expUnit_inv]

/-- The exponential map `𝔤 → G` is smooth. -/
theorem contMDiff_expG : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔤) ∞ h.expG := by
  let := h.chartedSpace
  intro X
  exact h.contMDiffAt_of_val (f := h.expG)
    (((contDiff_exp 𝔸).comp 𝔤.subtypeL.contDiff).contMDiff X)

/-- `p ↦ expG (φ p)` is smooth for smooth `φ`. -/
theorem contMDiff_expG_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : V → 𝔤}
    (hφ : ContDiff ℝ ∞ φ) : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔤) ∞ (fun p => h.expG (φ p)) := by
  let := h.chartedSpace
  exact h.contMDiff_expG.comp hφ.contMDiff

/-- A function on `G` is smooth for the exponential charts if and only if `Y ↦ f (g · exp Y)` is smooth
on `𝔤` for every `g`. -/
theorem contMDiff_iff_expG {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : G → F) :
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, F) ∞ f) ↔
      ∀ g : G, ContDiff ℝ ∞ (fun Y : 𝔤 => f (g * h.expG Y)) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  constructor
  · intro hf g
    have : ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔤) ∞ (fun Y : 𝔤 => g * h.expG Y) :=
      contMDiff_const.mul h.contMDiff_expG
    exact (hf.comp this).contDiff
  · intro hf x
    rw [contMDiffAt_iff_source]
    have : f ∘ (extChartAt 𝓘(ℝ, 𝔤) x).symm = fun Y : 𝔤 => f (x * h.expG Y) := rfl
    rw [this]
    exact (hf x).contMDiff.contMDiffAt.contMDiffWithinAt

end IsExpLieAlgebra

/-- A subgroup of `𝔸ˣ` with an exponential Lie algebra is closed: near `1` it is the image under `exp`
of the closed subspace `𝔤`, and a group that is closed near `1` is closed. -/
theorem IsExpLieAlgebra.isClosed (h : IsExpLieAlgebra G 𝔤) : IsClosed (G : Set 𝔸ˣ) := by
  set W : Set 𝔸ˣ := (fun u : 𝔸ˣ => (u : 𝔸)) ⁻¹' h.nhdOne with hW
  have hWo : IsOpen W := h.isOpen_nhdOne.preimage Units.continuous_val
  refine isClosed_of_closure_subset fun x hx => ?_
  have hN : {z : 𝔸ˣ | z⁻¹ * x ∈ W} ∈ 𝓝 x := by
    refine (hWo.preimage (continuous_inv.mul continuous_const)).mem_nhds ?_
    show (((x⁻¹ * x : 𝔸ˣ)) : 𝔸) ∈ h.nhdOne
    simpa using h.one_mem_nhdOne
  obtain ⟨g₀, hg₀N, hg₀G⟩ := mem_closure_iff_nhds.1 hx _ hN
  set y := g₀⁻¹ * x with hy
  have hyW : y ∈ W := hg₀N
  have hyc : y ∈ closure (G : Set 𝔸ˣ) :=
    map_mem_closure (continuous_const.mul continuous_id) hx fun z hz =>
      G.mul_mem (G.inv_mem hg₀G) hz
  have hyc' : y ∈ closure (W ∩ (G : Set 𝔸ˣ)) := hWo.inter_closure ⟨hyW, hyc⟩
  set L : 𝔸ˣ → 𝔸 := fun u => (expPartialHomeomorph 𝔸).symm (u : 𝔸) with hLdef
  have hL : ContinuousAt L y :=
    ((expPartialHomeomorph 𝔸).continuousAt_symm (h.nhdOne_subset_target hyW)).comp
      Units.continuous_val.continuousAt
  have himg : L '' (W ∩ (G : Set 𝔸ˣ)) ⊆ (𝔤 : Set 𝔸) := by
    rintro _ ⟨u, ⟨huW, huG⟩, rfl⟩
    apply h.mem_of_mem_nhd (h.symm_mem_nhd huW)
    have : expUnit 𝔸 (L u) = u := Units.ext (h.exp_symm huW)
    rw [this]
    exact huG
  have hLy : L y ∈ 𝔤 :=
    (Submodule.closed_of_finiteDimensional 𝔤).closure_subset_iff.2 himg (mem_closure_image hL hyc')
  have hyG : y ∈ G := by
    have : expUnit 𝔸 (L y) = y := Units.ext (h.exp_symm hyW)
    rw [← this]
    exact h.expUnit_mem _ hLy
  have : x = g₀ * y := by rw [hy, mul_inv_cancel_left]
  rw [this]
  exact G.mul_mem hg₀G hyG

end Basic

end Langlands.LinearLieGroup
