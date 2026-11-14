import Langlands.Representation.LanglandsClassification.ParabolicChamberStatements
import Langlands.Geometry.Building.FiniteRealTorusSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Submodule

noncomputable section

open scoped Pointwise

namespace Langlands.GroupScheme.ParabolicChamberAux

open Module

/-- Restrict a basis to a coordinate subspace. -/
theorem restrict_basis {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : Basis ι ℝ E) (P : Submodule ℝ E) (s : Set ι)
    (hmem : ∀ a ∈ s, b a ∈ P)
    (hzero : ∀ x : P, ∀ a ∉ s, b.repr x a = 0) :
    ∃ c : Basis s ℝ P, ∀ a, (c a : E) = b a := by
  classical
  let v : s → P := fun a => ⟨b a, hmem a a.2⟩
  have hv : LinearIndependent ℝ v :=
    (b.linearIndependent.comp Subtype.val Subtype.val_injective).of_comp P.subtype
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    intro x _
    have hx : (x : E) ∈ Submodule.span ℝ (b '' s) := by
      rw [b.mem_span_image]
      intro a ha
      by_contra has
      exact (Finsupp.mem_support_iff.mp ha) (hzero x a has)
    have heq : Submodule.map P.subtype (Submodule.span ℝ (Set.range v)) =
        Submodule.span ℝ (b '' s) := by
      rw [Submodule.map_span]
      congr 1
      ext y
      simp [v]
      intro a ha hay
      exact hay ▸ hmem a ha
    rw [← heq] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := Subtype.ext hzx
    simpa [this] using hz
  exact ⟨Basis.mk hv hspan, fun a => by simp [v]⟩

/-- Restrict a basis in one ambient submodule to a smaller submodule. -/
theorem restrict_submodule_basis {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    {X P : Submodule ℝ E} (hPX : P ≤ X) (b : Basis ι ℝ X) (s : Set ι)
    (hmem : ∀ a ∈ s, (b a : E) ∈ P)
    (hzero : ∀ x : P, ∀ a ∉ s, b.repr ⟨x, hPX x.2⟩ a = 0) :
    ∃ c : Basis s ℝ P, ∀ a, (c a : E) = b a := by
  obtain ⟨c, hc⟩ := restrict_basis b (P.comap X.subtype) s hmem (by
    intro x a ha
    exact hzero ⟨x, x.2⟩ a ha)
  refine ⟨c.map (Submodule.comapSubtypeEquivOfLe hPX), ?_⟩
  intro a
  change ((c a : X) : E) = b a
  exact congrArg (fun x : X => (x : E)) (hc a)

/-- Complementary subspaces give unique representatives modulo the second one. -/
theorem projection_unique {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P Q : Submodule ℝ E} (h : IsCompl P Q) (x : E) :
    ∃! y : E, y ∈ P ∧ x - y ∈ Q := by
  obtain ⟨u, v, huv, huniq⟩ := Submodule.existsUnique_add_of_isCompl h x
  have hdiff : x - (u : E) = v := by rw [← huv]; abel
  refine ⟨u, ⟨u.2, hdiff ▸ v.2⟩, ?_⟩
  intro y hy
  have heq : (⟨y, hy.1⟩ : P) = u := (huniq ⟨y, hy.1⟩ ⟨x - y, hy.2⟩ (by simp)).1
  exact congrArg Subtype.val heq

/-- A biorthogonal family of functionals reads the coordinates of a basis. -/
theorem repr_eq {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (b : Basis ι ℝ E) (q : ι → E →ₗ[ℝ] ℝ)
    (hq : ∀ a d, q a (b d) = if d = a then 1 else 0) (x : E) (a : ι) :
    b.repr x a = q a x := by
  classical
  have heq : b.coord a = q a := by
    apply b.ext
    intro d
    simp [Basis.coord_apply, hq, Finsupp.single_apply, eq_comm]
  exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) heq

/-- The ambient sum is the image of the coordinate inverse. -/
theorem sum_eq {ι E : Type*} [Finite ι] [AddCommGroup E] [Module ℝ E]
    {P : Submodule ℝ E} (b : Basis ι ℝ P) (c : ι → ℝ) :
    (b.equivFun.symm c : E) = ∑ᶠ a, c a • (b a : E) := by
  classical
  let := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  have h := congrArg (fun x : P => (x : E)) (b.equivFun_symm_apply c)
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using h

/-- Inequalities on coordinates are inequalities on the coefficients of the basis sum. -/
theorem coordinate_set {ι E : Type*} [Finite ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] {P : Submodule ℝ E}
    (b : Basis ι ℝ P) (q : ι → E →ₗ[ℝ] ℝ)
    (hq : ∀ a d, q a (b d) = if d = a then 1 else 0) (p : ℝ → Prop) :
    {y : E | y ∈ P ∧ ∀ a, p (q a y)} =
      {y : E | ∃ c : ι → ℝ, (∀ a, p (c a)) ∧ y = ∑ᶠ a, c a • (b a : E)} := by
  have hcoord (x : P) (a : ι) : b.equivFun x a = q a x :=
    repr_eq b (fun a => (q a).comp P.subtype) hq x a
  ext y
  constructor
  · rintro ⟨hy, hp⟩
    refine ⟨b.equivFun ⟨y, hy⟩, fun a => ?_, ?_⟩
    · rw [hcoord]; exact hp a
    · rw [← sum_eq]
      exact congrArg (fun x : P => (x : E)) (b.equivFun.symm_apply_apply ⟨y, hy⟩).symm
  · rintro ⟨c, hc, rfl⟩
    rw [← sum_eq]
    refine ⟨(b.equivFun.symm c).2, fun a => ?_⟩
    rw [← hcoord, b.equivFun.apply_symm_apply]
    exact hc a

/-- Adding another set to a coefficient cone appends one summand to its formula. -/
theorem coefficient_set_add {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) (p : ℝ → Prop) (C : Set E) :
    {y : E | ∃ c : ι → ℝ, (∀ a, p (c a)) ∧ y = ∑ᶠ a, c a • v a} + C =
      {y : E | ∃ c : ι → ℝ, (∀ a, p (c a)) ∧
        ∃ μ ∈ C, y = (∑ᶠ a, c a • v a) + μ} := by
  ext y
  constructor
  · rintro ⟨x, ⟨c, hc, rfl⟩, μ, hμ, rfl⟩
    exact ⟨c, hc, μ, hμ, rfl⟩
  · rintro ⟨c, hc, μ, hμ, rfl⟩
    exact Set.mem_add.mpr ⟨_, ⟨c, hc, rfl⟩, μ, hμ, rfl⟩

/-- A finite coordinate positive orthant is relatively open, with the nonnegative
orthant as its ambient closure. -/
theorem orthant_topology {ι E : Type*} [Finite ι] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (P : Submodule ℝ E) (b : Basis ι ℝ P) :
    IsOpen ((↑) ⁻¹' {y : E | ∃ c : ι → ℝ, (∀ a, 0 < c a) ∧
        y = ∑ᶠ a, c a • (b a : E)} : Set P) ∧
    closure {y : E | ∃ c : ι → ℝ, (∀ a, 0 < c a) ∧
        y = ∑ᶠ a, c a • (b a : E)} =
      {y : E | ∃ c : ι → ℝ, (∀ a, 0 ≤ c a) ∧
        y = ∑ᶠ a, c a • (b a : E)} := by
  classical
  let e := b.equivFun.toContinuousLinearEquiv.toHomeomorph
  let f : (ι → ℝ) → E := fun c => (e.symm c : P)
  have hf : Topology.IsClosedEmbedding f :=
    (P.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal).comp e.symm.isClosedEmbedding
  have himage (p : ℝ → Prop) :
      {y : E | ∃ c : ι → ℝ, (∀ a, p (c a)) ∧ y = ∑ᶠ a, c a • (b a : E)} =
        f '' Set.pi Set.univ (fun _ : ι => {r : ℝ | p r}) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor <;> rintro ⟨c, hc, hy⟩ <;> refine ⟨c, hc, ?_⟩
    · simpa [f, e, sum_eq] using hy.symm
    · simpa [f, e, sum_eq] using hy.symm
  constructor
  · have heq : ((↑) ⁻¹' {y : E | ∃ c : ι → ℝ, (∀ a, 0 < c a) ∧
        y = ∑ᶠ a, c a • (b a : E)} : Set P) =
        e ⁻¹' Set.pi Set.univ (fun _ : ι => Set.Ioi (0 : ℝ)) := by
      rw [himage]
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨c, hc, hcx⟩
        have : e.symm c = x := Subtype.ext hcx
        simpa [← this] using hc
      · intro hx
        exact ⟨e x, hx, by simp [f]⟩
    rw [heq]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi).preimage e.continuous
  · rw [himage (fun r => 0 < r), himage (fun r => 0 ≤ r), hf.closure_image_eq,
      closure_pi_set]
    change f '' Set.pi Set.univ (fun _ : ι => closure (Set.Ioi (0 : ℝ))) =
      f '' Set.pi Set.univ (fun _ : ι => Set.Ici (0 : ℝ))
    simp only [closure_Ioi]

/-- Finite-dimensional real module topology is Hausdorff, as seen through basis
coordinates. -/
theorem moduleTopology_t2 {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] :
    letI : TopologicalSpace E := moduleTopology ℝ E
    T2Space E := by
  classical
  letI : TopologicalSpace E := moduleTopology ℝ E
  let b := Basis.ofVectorSpace ℝ E
  letI := FiniteDimensional.fintypeBasisIndex b
  exact T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)

end Langlands.GroupScheme.ParabolicChamberAux
