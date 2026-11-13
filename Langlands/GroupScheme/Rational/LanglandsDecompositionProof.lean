import Langlands.GroupScheme.Rational.LanglandsDecompositionStatement
import Langlands.GroupScheme.Rational.ParabolicWeylDisplacement
import Langlands.GroupScheme.Rational.RelativeWeylFaithfulness
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsProof
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.ReflectionNegation
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.Representation.LanglandsClassification.SimpleCorootFaceExistence
import Langlands.Analysis.RenardConeProjectionProof
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Proof of Langlands' combinatorial lemma for actual standard parabolics (Renard V.3.18)

The coroot formula `⟨y, α̌⟩ B(α, α) = 2 B(y, α)`, from the Weyl invariance of `B`, turns the
coroot conditions of `IsLanglandsDecomposition` into `B`-conditions. Every decomposition then
satisfies the variational inequalities of the projections on the two closed cones. These give
the projection characterizations, the orthogonality and the uniqueness. Existence relative to
`P_∅` comes from the V.5.5 Corollary applied to the real root span with the simple roots as
basis. Obtuseness of distinct simple roots shows that this decomposition is also the one
relative to `P`. Conjunct 1 is a dimension count based on the standard Levi central directions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

namespace LanglandsDecomposition

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] (D : RelativeRootReflectionData i)
  {B : LinearMap.BilinForm ℝ (Vstar T)}

/-! ### The coroot formula and central directions -/

/-- Weyl invariance under the reflection of `α` gives the coroot formula
`⟨y, α̌⟩ B(α, α) = 2 B(y, α)`. -/
theorem pair_coroot_mul_form_root (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (y : Vstar T) :
    pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) *
        B ((1 : ℝ) ⊗ₜ[ℤ] α.val) ((1 : ℝ) ⊗ₜ[ℤ] α.val) =
      2 * B y ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  have h := hB.2.2 (QuotientGroup.mk (D.representative α)) y ((1 : ℝ) ⊗ₜ[ℤ] α.val)
  rw [D.fullRealAction_representative, D.fullRealAction_representative, pair_tmul_tmul,
    D.pair_self] at h
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    one_mul] at h
  push_cast at h
  linear_combination h

include D in
/-- The real vector of an actual relative root is nonzero. -/
theorem tmul_root_ne_zero (α : relativeRoots i) :
    ((1 : ℝ) ⊗ₜ[ℤ] α.val : Vstar T) ≠ 0 := by
  intro h
  have h2 := congrArg (fun z => pair T z ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) h
  simp only [pair_tmul_tmul, D.pair_self, map_zero, LinearMap.zero_apply] at h2
  norm_num at h2

include D in
/-- A root has positive `B`-length. -/
theorem form_root_pos (hB : IsWeylInvariantInnerProduct i B) (α : relativeRoots i) :
    0 < B ((1 : ℝ) ⊗ₜ[ℤ] α.val) ((1 : ℝ) ⊗ₜ[ℤ] α.val) :=
  hB.2.1 _ (tmul_root_ne_zero D α)

omit [IsAffineHom G.X.hom] in
/-- `B` is positive semidefinite. -/
theorem form_self_nonneg (hB : IsWeylInvariantInnerProduct i B) (x : Vstar T) :
    0 ≤ B x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (hB.2.1 x hx).le

omit [IsAffineHom G.X.hom] in
/-- A vector of nonpositive `B`-length is zero. -/
theorem eq_zero_of_form_self_nonpos (hB : IsWeylInvariantInnerProduct i B) {x : Vstar T}
    (hx : B x x ≤ 0) : x = 0 := by
  by_contra hne
  exact absurd hx (not_le.mpr (hB.2.1 x hne))

/-- The coroot pairing vanishes exactly when the `B`-product with the root does. -/
theorem pair_eq_zero_iff (hB : IsWeylInvariantInnerProduct i B) (α : relativeRoots i)
    (y : Vstar T) :
    pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 ↔ B y ((1 : ℝ) ⊗ₜ[ℤ] α.val) = 0 := by
  have h := pair_coroot_mul_form_root D hB α y
  have hpos := form_root_pos D hB α
  constructor
  · intro h0
    rw [h0, zero_mul] at h
    linarith
  · intro h0
    rw [h0, mul_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hpos.ne'

/-- The coroot pairing is positive exactly when the `B`-product with the root is. -/
theorem pair_pos_iff (hB : IsWeylInvariantInnerProduct i B) (α : relativeRoots i)
    (y : Vstar T) :
    0 < pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) ↔ 0 < B y ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  have h := pair_coroot_mul_form_root D hB α y
  have hpos := form_root_pos D hB α
  constructor
  · intro h0
    have := mul_pos h0 hpos
    linarith
  · intro h0
    by_contra hle
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hle) hpos.le
    linarith

/-- The coroot pairing is nonnegative exactly when the `B`-product with the root is. -/
theorem pair_nonneg_iff (hB : IsWeylInvariantInnerProduct i B) (α : relativeRoots i)
    (y : Vstar T) :
    0 ≤ pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) ↔ 0 ≤ B y ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, pair_pos_iff D hB, eq_comm, pair_eq_zero_iff D hB,
    eq_comm (a := (0 : ℝ))]

omit [IsAffineHom G.X.hom] in
/-- The full real Weyl action fixes the restrictions of real rational
characters of `G`. -/
theorem relativeWeylFullRealAction_restrictReal (w : relativeWeylGroup i)
    (x : ℝ ⊗[ℤ] rationalCharacters G) :
    relativeWeylFullRealAction i w (rationalCharacterRestrictReal i x) =
      rationalCharacterRestrictReal i x := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    change r ⊗ₜ[ℤ] relativeWeylLatticeAction i w (torusCharacterRestrict i χ) =
      r ⊗ₜ[ℤ] torusCharacterRestrict i χ
    rw [relativeWeylLatticeAction_torusCharacterRestrict]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restrictions of real rational characters of `G` annihilate every coroot. -/
theorem pair_coroot_eq_zero_of_mem_range {z : Vstar T}
    (hz : z ∈ LinearMap.range (rationalCharacterRestrictReal i)) (α : relativeRoots i) :
    pair T z ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 := by
  obtain ⟨x, rfl⟩ := hz
  have h := relativeWeylFullRealAction_restrictReal (QuotientGroup.mk (D.representative α)) x
  rw [D.fullRealAction_representative, sub_eq_self, smul_eq_zero] at h
  exact h.resolve_right (tmul_root_ne_zero D α)

/-- A vector annihilating the coroots of a set of roots is `B`-orthogonal to
their real span. -/
theorem form_eq_zero_of_pair_eq_zero (hB : IsWeylInvariantInnerProduct i B)
    {K : Set (characterLattice T)} (hK : K ⊆ relativeRoots i) {m z : Vstar T}
    (hm : ∀ α : relativeRoots i, α.1 ∈ K → pair T m ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hz : z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K)) :
    B m z = 0 := by
  have hle : Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) ≤
      LinearMap.ker (B m) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    exact (pair_eq_zero_iff D hB ⟨α, hK hα⟩ m).mp (hm ⟨α, hK hα⟩ hα)
  exact hle hz

include D in
/-- Central directions are `B`-orthogonal to the real root span. -/
theorem form_eq_zero_of_mem_range_of_mem_rootSpan (hB : IsWeylInvariantInnerProduct i B)
    {z c : Vstar T} (hz : z ∈ LinearMap.range (rationalCharacterRestrictReal i))
    (hc : c ∈ relativeRootSpanReal i) : B z c = 0 :=
  form_eq_zero_of_pair_eq_zero D hB subset_rfl
    (fun α _ => pair_coroot_eq_zero_of_mem_range D hz α) hc

/-! ### Cones of roots -/

/-- Nonnegative combinations of roots on which `w` has nonnegative coroot
pairings have nonnegative `B`-product with `w`. -/
theorem form_nonneg_of_mem_hull (hB : IsWeylInvariantInnerProduct i B)
    {S : Set (characterLattice T)} (hS : S ⊆ relativeRoots i) {z w : Vstar T}
    (hw : ∀ α : relativeRoots i, α.1 ∈ S → 0 ≤ pair T w ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (hz : z ∈ PointedCone.hull ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S)) :
    0 ≤ B z w := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    rw [hB.1]
    exact (pair_nonneg_iff D hB ⟨α, hS hα⟩ w).mp (hw ⟨α, hS hα⟩ hα)
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, LinearMap.add_apply]
    linarith
  | smul t x _ hx =>
    change 0 ≤ B ((t : ℝ) • x) w
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg t.2 hx

/-- A nonnegative combination of roots of `K` differs from a nonnegative
combination of roots of `K ∖ J` by an element of the real span of `J`. -/
theorem exists_split_of_mem_hull {K J : Set (characterLattice T)} {x : Vstar T}
    (hx : x ∈ PointedCone.hull ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K)) :
    ∃ z ∈ PointedCone.hull ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' (K \ J)),
      x - z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    by_cases hαJ : α ∈ J
    · refine ⟨0, zero_mem _, ?_⟩
      rw [sub_zero]
      exact Submodule.subset_span ⟨α, hαJ, rfl⟩
    · refine ⟨_, Submodule.subset_span ⟨α, ⟨hα, hαJ⟩, rfl⟩, ?_⟩
      rw [sub_self]
      exact zero_mem _
  | zero => exact ⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨z₁, hz₁, h₁⟩ := hx
    obtain ⟨z₂, hz₂, h₂⟩ := hy
    refine ⟨z₁ + z₂, add_mem hz₁ hz₂, ?_⟩
    have h := add_mem h₁ h₂
    convert h using 1
    abel
  | smul t x _ hx =>
    obtain ⟨z, hz, h⟩ := hx
    refine ⟨t • z, Submodule.smul_mem _ t hz, ?_⟩
    have h' := Submodule.smul_mem _ (t : ℝ) h
    rw [smul_sub] at h'
    exact h'

/-- Nonnegative combinations of roots of `S` lie in the real span of `S`. -/
theorem mem_span_of_mem_hull {S : Set (characterLattice T)} {x : Vstar T}
    (hx : x ∈ PointedCone.hull ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S)) :
    x ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S) :=
  PointedCone.hull_le_span ℝ _ hx

omit [Mono i.hom.hom.left] in
/-- The real span of a set of roots lies in the real root span. -/
theorem span_le_rootSpan {S : Set (characterLattice T)} (hS : S ⊆ relativeRoots i) :
    Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S) ≤
      relativeRootSpanReal i :=
  Submodule.span_mono (Set.image_mono hS)

/-! ### Properties of an arbitrary decomposition -/

section Decomposition

variable (ν : cocharacterLattice T)

omit [Mono i.hom.hom.left] in
theorem simple_subset_roots : simpleRelativeRoots i ν ⊆ relativeRoots i := fun _ hα =>
  positiveRelativeRoots_subset_relativeRoots i ν (simpleRelativeRoots_subset_positive i ν hα)

variable {ν} {J K : Set (characterLattice T)} {μ μG μp μm : Vstar T}

/-- In a decomposition, `-μ⁻` lies in the real span of the roots of `K`. -/
theorem neg_m_mem_span (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) :
    -μm ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) := by
  obtain ⟨hJK, -, -, -, -, -, z, hz, hzs⟩ := h
  have h1 : z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) :=
    Submodule.span_mono (Set.image_mono Set.sdiff_subset) (mem_span_of_mem_hull hz)
  have h2 : -μm - z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) :=
    Submodule.span_mono (Set.image_mono hJK) hzs
  have h3 := add_mem h2 h1
  rwa [sub_add_cancel] at h3

/-- In a decomposition, `μ⁻` lies in the real root span. -/
theorem m_mem_rootSpan (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) :
    μm ∈ relativeRootSpanReal i := by
  have h' := span_le_rootSpan (fun _ hα => simple_subset_roots ν (h.2.1 hα))
    (neg_m_mem_span D h)
  simpa using neg_mem h'

/-- In a decomposition, `μ⁺` and `μ⁻` are `B`-orthogonal. -/
theorem form_p_m (hB : IsWeylInvariantInnerProduct i B)
    (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) : B μp μm = 0 := by
  have hz := form_eq_zero_of_pair_eq_zero D hB
    (fun _ hα => simple_subset_roots ν (h.2.1 hα)) h.2.2.2.2.1.2.1 (neg_m_mem_span D h)
  rw [map_neg, neg_eq_zero] at hz
  exact hz

/-- In a decomposition, `μ_G` and `μ⁺` are `B`-orthogonal. -/
theorem form_G_p (hB : IsWeylInvariantInnerProduct i B)
    (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) : B μG μp = 0 :=
  form_eq_zero_of_mem_range_of_mem_rootSpan D hB h.2.2.2.1 h.2.2.2.2.1.1

/-- In a decomposition, `μ_G` and `μ⁻` are `B`-orthogonal. -/
theorem form_G_m (hB : IsWeylInvariantInnerProduct i B)
    (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) : B μG μm = 0 :=
  form_eq_zero_of_mem_range_of_mem_rootSpan D hB h.2.2.2.1 (m_mem_rootSpan D h)

/-- In a decomposition, `μ - μ_G` is `B`-orthogonal to the central directions. -/
theorem form_sub_G_central (hB : IsWeylInvariantInnerProduct i B)
    (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) {z : Vstar T}
    (hz : z ∈ LinearMap.range (rationalCharacterRestrictReal i)) : B (μ - μG) z = 0 := by
  have hroot : μ - μG ∈ relativeRootSpanReal i := by
    rw [h.2.2.1, show μG + μp + μm - μG = μp + μm by abel]
    exact add_mem h.2.2.2.2.1.1 (m_mem_rootSpan D h)
  rw [hB.1]
  exact form_eq_zero_of_mem_range_of_mem_rootSpan D hB hz hroot

/-- In a decomposition, `μ⁺` lies in the closed coroot face of `J`. -/
theorem p_mem_closedFace (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) :
    μp ∈ closedCorootFace i ν D J := by
  obtain ⟨hJK, -, -, -, ⟨hroot, hzero, hpos⟩, -⟩ := h
  refine ⟨hroot, fun α hα => hzero α (hJK hα), fun α hα _ => ?_⟩
  by_cases hαK : α.1 ∈ K
  · exact (hzero α hαK).ge
  · exact (hpos α hα hαK).le

/-- In a decomposition, `-μ⁻` lies in the projected cone of the roots of
`Δ ∖ J`. -/
theorem neg_m_mem_cone (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) :
    -μm ∈ projectedRootNonnegCone i D J (simpleRelativeRoots i ν \ J) := by
  obtain ⟨-, hKΔ, -, -, -, hann, z, hz, hzs⟩ := h
  refine ⟨hann, z, ?_, hzs⟩
  exact Submodule.span_mono (Set.image_mono (Set.sdiff_subset_sdiff_left hKΔ)) hz

/-- Variational inequality for `μ⁺` on the closed coroot face of `J`. -/
theorem p_variational (hB : IsWeylInvariantInnerProduct i B)
    (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) {w : Vstar T}
    (hw : w ∈ closedCorootFace i ν D J) : B (μ - μp) (w - μp) ≤ 0 := by
  have hpm := form_p_m D hB h
  have hproot := h.2.2.2.2.1.1
  obtain ⟨hJK, hKΔ, hμ, hμG, -, -, z, hz, hzs⟩ := h
  have hJr : J ⊆ relativeRoots i := fun _ hα => simple_subset_roots ν (hKΔ (hJK hα))
  have hKJr : K \ J ⊆ relativeRoots i := fun _ hα => simple_subset_roots ν (hKΔ hα.1)
  have h1 : B μG (w - μp) = 0 :=
    form_eq_zero_of_mem_range_of_mem_rootSpan D hB hμG (sub_mem hw.1 hproot)
  have h2 : B w (-μm - z) = 0 := form_eq_zero_of_pair_eq_zero D hB hJr hw.2.1 hzs
  have h3 : 0 ≤ B z w := form_nonneg_of_mem_hull D hB hKJr
    (fun α hα => hw.2.2 α (hKΔ hα.1) hα.2) hz
  have hsplit : μ - μp = μG + μm := by rw [hμ]; abel
  rw [hsplit]
  have s1 := hB.1 μm μp
  have s2 := hB.1 w μm
  have s3 := hB.1 w z
  simp only [map_add, map_sub, map_neg, LinearMap.add_apply] at h1 h2 ⊢
  linarith

/-- Variational inequality for `μ⁻` on `-projectedRootNonnegCone J (Δ ∖ J)`. -/
theorem m_variational (hB : IsWeylInvariantInnerProduct i B)
    (h : IsLanglandsDecomposition i ν D J μ K μG μp μm) {w : Vstar T}
    (hw : -w ∈ projectedRootNonnegCone i D J (simpleRelativeRoots i ν \ J)) :
    B (μ - μm) (w - μm) ≤ 0 := by
  have hpm := form_p_m D hB h
  have hmroot := m_mem_rootSpan D h
  obtain ⟨hJK, hKΔ, hμ, hμG, ⟨-, hpzero, hppos⟩, -⟩ := h
  obtain ⟨-, z, hz, hzs⟩ := hw
  have hJr : J ⊆ relativeRoots i := fun _ hα => simple_subset_roots ν (hKΔ (hJK hα))
  have hΔJr : simpleRelativeRoots i ν \ J ⊆ relativeRoots i :=
    fun _ hα => simple_subset_roots ν hα.1
  have hwroot : w ∈ relativeRootSpanReal i := by
    have hz' : z ∈ relativeRootSpanReal i := span_le_rootSpan hΔJr (mem_span_of_mem_hull hz)
    have hs' : -w - z ∈ relativeRootSpanReal i := span_le_rootSpan hJr hzs
    have h' := add_mem hs' hz'
    rw [sub_add_cancel] at h'
    simpa using neg_mem h'
  have h1 : B μG (w - μm) = 0 :=
    form_eq_zero_of_mem_range_of_mem_rootSpan D hB hμG (sub_mem hwroot hmroot)
  have h2 : B μp (-w - z) = 0 :=
    form_eq_zero_of_pair_eq_zero D hB hJr (fun α hα => hpzero α (hJK hα)) hzs
  have h3 : 0 ≤ B z μp := form_nonneg_of_mem_hull D hB hΔJr (fun α hα => by
    by_cases hαK : α.1 ∈ K
    · exact (hpzero α hαK).ge
    · exact (hppos α hα.1 hαK).le) hz
  have hsplit : μ - μm = μG + μp := by rw [hμ]; abel
  rw [hsplit]
  have s1 := hB.1 μp μm
  have s3 := hB.1 μp z
  simp only [map_add, map_sub, map_neg, LinearMap.add_apply] at h1 h2 ⊢
  linarith

omit [IsAffineHom G.X.hom] in
/-- The variational inequality implies the nearest-point inequality. -/
theorem nearest_of_variational (hB : IsWeylInvariantInnerProduct i B) {a x w : Vstar T}
    (h : B (a - x) (w - x) ≤ 0) : B (a - x) (a - x) ≤ B (a - w) (a - w) := by
  have hd := form_self_nonneg hB (w - x)
  have heq : a - w = (a - x) - (w - x) := by abel
  rw [heq]
  have s := hB.1 (a - x) (w - x)
  simp only [map_sub, LinearMap.sub_apply] at s ⊢
  simp only [map_sub, LinearMap.sub_apply] at h hd
  linarith

omit [IsAffineHom G.X.hom] in
/-- Two points satisfying the variational inequalities against each other agree. -/
theorem eq_of_variational (hB : IsWeylInvariantInnerProduct i B) {a x y : Vstar T}
    (hx : B (a - x) (y - x) ≤ 0) (hy : B (a - y) (x - y) ≤ 0) : x = y := by
  have h : B (y - x) (y - x) ≤ 0 := by
    simp only [map_sub, LinearMap.sub_apply] at hx hy ⊢
    linarith
  exact (sub_eq_zero.mp (eq_zero_of_form_self_nonpos hB h)).symm

/-- Two decompositions of the same vector relative to the same `J` agree. -/
theorem eq_of_isLanglandsDecomposition (hB : IsWeylInvariantInnerProduct i B)
    {K' : Set (characterLattice T)} {μG' μp' μm' : Vstar T}
    (h : IsLanglandsDecomposition i ν D J μ K μG μp μm)
    (h' : IsLanglandsDecomposition i ν D J μ K' μG' μp' μm') :
    K = K' ∧ μG = μG' ∧ μp = μp' ∧ μm = μm' := by
  have hp : μp = μp' := eq_of_variational hB (p_variational D hB h (p_mem_closedFace D h'))
    (p_variational D hB h' (p_mem_closedFace D h))
  have hm : μm = μm' := eq_of_variational hB (m_variational D hB h (neg_m_mem_cone D h'))
    (m_variational D hB h' (neg_m_mem_cone D h))
  have hG : μG = μG' := by
    have e1 := h.2.2.1
    have e2 := h'.2.2.1
    rw [hp, hm] at e1
    have := e1.symm.trans e2
    simpa using this
  refine ⟨?_, hG, hp, hm⟩
  obtain ⟨-, hKΔ, -, -, ⟨-, hz, hpos⟩, -⟩ := h
  obtain ⟨-, hKΔ', -, -, ⟨-, hz', hpos'⟩, -⟩ := h'
  ext χ
  constructor
  · intro hχ
    by_contra hχ'
    have hα := hpos' ⟨χ, simple_subset_roots ν (hKΔ hχ)⟩ (hKΔ hχ) hχ'
    rw [← hp, hz ⟨χ, simple_subset_roots ν (hKΔ hχ)⟩ hχ] at hα
    exact lt_irrefl _ hα
  · intro hχ
    by_contra hχ'
    have hα := hpos ⟨χ, simple_subset_roots ν (hKΔ' hχ)⟩ (hKΔ' hχ) hχ'
    rw [hp, hz' ⟨χ, simple_subset_roots ν (hKΔ' hχ)⟩ hχ] at hα
    exact lt_irrefl _ hα

end Decomposition

/-! ### The V.5.5 Corollary for a positive definite form -/

/-- Renard V.5.5 Corollary for a vector space with a symmetric positive
definite bilinear form, a finite basis `b` and a dual family `ω`: every vector is
`∑_{i ∉ F} tᵢ ωᵢ - ∑_{j ∈ F} sⱼ bⱼ` with `tᵢ > 0` and `sⱼ ≥ 0`. -/
theorem exists_cone_decomposition_of_form {E : Type*} [AddCommGroup E] [Module ℝ E]
    (β : LinearMap.BilinForm ℝ E) (hsymm : ∀ x y, β x y = β y x)
    (hpos : ∀ x, x ≠ 0 → 0 < β x x)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (ω : ι → E)
    (hω : ∀ i j, β (b i) (ω j) = if i = j then 1 else 0) (x : E) :
    ∃ (F : Finset ι) (t s : ι → ℝ), (∀ i ∈ Finset.univ \ F, 0 < t i) ∧
      (∀ j ∈ F, 0 ≤ s j) ∧ x = (∑ i ∈ Finset.univ \ F, t i • ω i) - ∑ j ∈ F, s j • b j := by
  let core : InnerProductSpace.Core ℝ E :=
    { inner := fun x y => β x y
      conj_inner_symm := fun x y => by
        change (starRingEnd ℝ) (β y x) = β x y
        rw [conj_trivial]
        exact hsymm _ _
      re_inner_nonneg := fun x => by
        rw [RCLike.re_to_real]
        by_cases hx : x = 0
        · simp [hx]
        · exact (hpos x hx).le
      add_left := fun x y z => by
        change β (x + y) z = β x z + β y z
        rw [map_add, LinearMap.add_apply]
      smul_left := fun x y r => by
        change β (r • x) y = (starRingEnd ℝ) r * β x y
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, conj_trivial]
      definite := fun x hx => by
        by_contra hne
        have h : β x x = 0 := hx
        exact absurd h (hpos x hne).ne' }
  let : NormedAddCommGroup E := @InnerProductSpace.Core.toNormedAddCommGroup ℝ E _ _ _ core
  let : InnerProductSpace ℝ E := InnerProductSpace.ofCore core.toCore
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  exact ((Langlands.Renard.coneProjectionBasisStatement ι E b ω hω) x).1.exists

/-! ### Obtuseness of simple roots and existence -/

section Existence

variable (ν : cocharacterLattice T)

/-- Distinct simple roots pair nonpositively with each other's coroots. -/
theorem latticePairing_coroot_nonpos (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (hν : IsGenericCocharacter i ν) {α β : relativeRoots i}
    (hα : α.1 ∈ simpleRelativeRoots i ν) (hβ : β.1 ∈ simpleRelativeRoots i ν)
    (hne : α ≠ β) : latticePairing T α.1 (D.coroot β) ≤ 0 := by
  classical
  have : Finite (relativeRoots i) := hfinite.to_subtype
  let P := D.rootPairing hT hfinite
  have : P.IsCrystallographic := D.rootPairing_isCrystallographic hT hfinite
  let f : relativeRootSpan i →ₗ[ℚ] ℚ := RelativeRootSystem.corootFunctional i ν
  have hfr (γ : relativeRoots i) :
      f (P.root γ) = (latticePairing T γ.val ν : ℚ) :=
    RelativeRootSystem.corootFunctional_rootVector i ν γ
  have hf (γ : relativeRoots i) : f.toAddMonoidHom (P.root γ) ≠ 0 := by
    change f (P.root γ) ≠ 0
    rw [hfr]
    exact_mod_cast hν γ.val γ.property
  have hbase : {γ : relativeRoots i | γ.val ∈ simpleRelativeRoots i ν} ⊆
      IsAddIndecomposable.baseOf P.root f.toAddMonoidHom := by
    intro γ hγ
    refine ⟨?_, fun β' hβ' γ' hγ' heq => ?_⟩
    · change 0 < f (P.root γ)
      rw [hfr]
      exact_mod_cast hγ.1.2
    · exfalso
      apply hγ.2
      have hβpos : 0 < latticePairing T β'.val ν := by
        change 0 < f (P.root β') at hβ'
        rw [hfr] at hβ'
        exact_mod_cast hβ'
      have hγpos : 0 < latticePairing T γ'.val ν := by
        change 0 < f (P.root γ') at hγ'
        rw [hfr] at hγ'
        exact_mod_cast hγ'
      refine ⟨β'.val, ⟨β'.property, hβpos⟩, γ'.val, ⟨γ'.property, hγpos⟩, ?_⟩
      apply hT.character_toRat_injective
      rw [map_add]
      exact congrArg Subtype.val heq
  have h := P.baseOf_pairwise_pairing_le_zero f.toAddMonoidHom hf (hbase hα) (hbase hβ) hne
  have hpair : P.pairing α β = (latticePairing T α.1 (D.coroot β) : ℚ) :=
    RelativeRootSystem.corootFunctional_rootVector i (D.coroot β) α
  have hcast := P.algebraMap_pairingIn ℤ α β
  rw [hpair] at hcast
  have heq : P.pairingIn ℤ α β = latticePairing T α.1 (D.coroot β) := by
    rw [algebraMap_int_eq, eq_intCast] at hcast
    exact_mod_cast hcast
  rw [← heq]
  exact h

/-- Nonnegative combinations of simple roots of `S` pair nonpositively with the
coroot of a simple root outside `S`. -/
theorem pair_nonpos_of_mem_hull (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (hν : IsGenericCocharacter i ν)
    {S : Set (characterLattice T)} (hS : S ⊆ simpleRelativeRoots i ν)
    {β : relativeRoots i} (hβ : β.1 ∈ simpleRelativeRoots i ν) (hβS : β.1 ∉ S) {x : Vstar T}
    (hx : x ∈ PointedCone.hull ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S)) :
    pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot β) ≤ 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    rw [pair_tmul_tmul, one_mul, one_mul]
    have hne : (⟨α, simple_subset_roots ν (hS hα)⟩ : relativeRoots i) ≠ β := fun h =>
      hβS (by rw [← h]; exact hα)
    exact_mod_cast latticePairing_coroot_nonpos D ν hT hfinite hν (hS hα) hβ hne
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    linarith
  | smul t x _ hx =>
    change pair T ((t : ℝ) • x) _ ≤ 0
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos t.2 hx

/-- A decomposition relative to `P_∅` of a vector of `𝔞*_M` is a decomposition
relative to `P`. -/
theorem isLanglandsDecomposition_of_empty (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} {μ μG μp μm : Vstar T}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hμ : μ ∈ corootAnnihilator i D J)
    (h : IsLanglandsDecomposition i ν D ∅ μ K μG μp μm) :
    IsLanglandsDecomposition i ν D J μ K μG μp μm := by
  obtain ⟨-, hKΔ, hμeq, hμG, hp, hm⟩ := h
  have hmK : -μm ∈ PointedCone.hull ℝ
      ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) := by
    obtain ⟨-, z, hz, hzspan⟩ := hm
    rw [Set.image_empty, Submodule.span_empty, Submodule.mem_bot, sub_eq_zero] at hzspan
    rw [Set.sdiff_empty] at hz
    rwa [hzspan]
  have hpair (α : relativeRoots i) : pair T μ ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) =
      pair T μp ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) + pair T μm ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) := by
    rw [hμeq, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      pair_coroot_eq_zero_of_mem_range D hμG α, zero_add]
  have hJK : J ⊆ K := by
    intro β hβJ
    by_contra hβK
    have hβr : β ∈ relativeRoots i := simple_subset_roots ν (hJ hβJ)
    have h0 := (mem_corootAnnihilator i D J μ).mp hμ ⟨β, hβr⟩ hβJ
    have h1 := hp.2.2 ⟨β, hβr⟩ (hJ hβJ) hβK
    have h2 := pair_nonpos_of_mem_hull D ν hT hfinite hν (S := K) hKΔ (β := ⟨β, hβr⟩) (hJ hβJ) hβK hmK
    rw [map_neg, LinearMap.neg_apply] at h2
    rw [hpair] at h0
    linarith
  refine ⟨hJK, hKΔ, hμeq, hμG, hp, ?_, exists_split_of_mem_hull hmK⟩
  rw [mem_corootAnnihilator]
  intro α hα
  have h0 := (mem_corootAnnihilator i D J μ).mp hμ α hα
  rw [hpair, hp.2.1 α (hJK hα), zero_add] at h0
  rw [map_neg, LinearMap.neg_apply, h0, neg_zero]

omit [Mono i.hom.hom.left] in
/-- Every real character is a central direction plus an element of the real root span. -/
theorem exists_central_add_root (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (y : Vstar T) : ∃ c ∈ LinearMap.range (rationalCharacterRestrictReal i),
      ∃ r ∈ relativeRootSpanReal i, y = c + r := by
  have h := (relativeCharacterRootComplement k G hG T i hi).2
  have hy : y ∈ relativeRootSpanReal i ⊔ LinearMap.range (rationalCharacterRestrictReal i) := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨r, hr, c, hc, hrc⟩ := Submodule.mem_sup.mp hy
  exact ⟨c, hc, r, hr, by rw [← hrc, add_comm]⟩

include D in
open Classical in
/-- For each simple root `β` there is a vector of the real root span whose
`B`-products with the simple roots are `δ_{αβ}`. -/
theorem exists_dual_vector (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hB : IsWeylInvariantInnerProduct i B)
    (β : relativeRoots i) (hβ : β.1 ∈ simpleRelativeRoots i ν) :
    ∃ w ∈ relativeRootSpanReal i, ∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν →
      B ((1 : ℝ) ⊗ₜ[ℤ] α.1) w = if α = β then 1 else 0 := by
  classical
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  obtain ⟨y, hy0, hypos⟩ := D.exists_mem_openSimpleCorootFace i ν hT
    (hT.finite_relativeRoots i) hν (simpleRelativeRoots i ν \ {β.1}) Set.sdiff_subset
  obtain ⟨c, hc, r, hr, rfl⟩ := exists_central_add_root hG hi y
  have hpr (α : relativeRoots i) : pair T (c + r) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) =
      pair T r ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) := by
    rw [map_add, LinearMap.add_apply, pair_coroot_eq_zero_of_mem_range D hc α, zero_add]
  have hβpos : 0 < B r ((1 : ℝ) ⊗ₜ[ℤ] β.1) := by
    have h := hypos β hβ (fun h => h.2 rfl)
    rw [hpr] at h
    exact (pair_pos_iff D hB β r).mp h
  refine ⟨(B r ((1 : ℝ) ⊗ₜ[ℤ] β.1))⁻¹ • r, Submodule.smul_mem _ _ hr, fun α hα => ?_⟩
  rw [map_smul, smul_eq_mul, hB.1 _ r]
  split_ifs with hαβ
  · subst hαβ
    field_simp
  · have h0 := hy0 α ⟨hα, fun h => hαβ (Subtype.ext h)⟩
    rw [hpr] at h0
    rw [(pair_eq_zero_iff D hB α r).mp h0, mul_zero]

include D in
/-- The simple roots span the real root span. -/
theorem span_simple_eq_rootSpan (hν : IsGenericCocharacter i ν) :
    Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) ''
      simpleRelativeRoots i ν) = relativeRootSpanReal i := by
  apply le_antisymm
  · exact span_le_rootSpan (simple_subset_roots ν)
  · let φ : characterLattice T →+ Vstar T :=
      (TensorProduct.mk ℤ ℝ (characterLattice T) 1).toAddMonoidHom
    have hcl : AddSubgroup.closure (simpleRelativeRoots i ν) ≤
        (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) ''
          simpleRelativeRoots i ν)).toAddSubgroup.comap φ := by
      rw [AddSubgroup.closure_le]
      intro α hα
      exact Submodule.subset_span ⟨α, hα, rfl⟩
    rw [relativeRootSpanReal, Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    exact hcl (relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots i ν hν
      (fun _ h => D.neg_mem_relativeRoots i h) hα)

/-- Every real character has a decomposition relative to `P_∅`, from the
V.5.5 Corollary applied to the real root span with the simple roots as basis. -/
theorem exists_empty_decomposition (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hB : IsWeylInvariantInnerProduct i B) (μ : Vstar T) :
    ∃ (K : Set (characterLattice T)) (μG μp μm : Vstar T),
      IsLanglandsDecomposition i ν D ∅ μ K μG μp μm := by
  classical
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  have hΔfin : (simpleRelativeRoots i ν).Finite :=
    (hT.finite_relativeRoots i).subset (simple_subset_roots ν)
  let ι := ↥(simpleRelativeRoots i ν)
  let : Fintype ι := hΔfin.fintype
  let E := ↥(relativeRootSpanReal i)
  have hroot (α : ι) :
      ((1 : ℝ) ⊗ₜ[ℤ] (α : characterLattice T) : Vstar T) ∈ relativeRootSpanReal i :=
    Submodule.subset_span ⟨α.1, simple_subset_roots ν α.2, rfl⟩
  let v : ι → E := fun α => ⟨(1 : ℝ) ⊗ₜ[ℤ] (α : characterLattice T), hroot α⟩
  let ρ : ι → relativeRoots i := fun α => ⟨α.1, simple_subset_roots ν α.2⟩
  choose ω hωmem hω using fun α : ι => exists_dual_vector D ν hG hi hν hB (ρ α) α.2
  let ωE : ι → E := fun α => ⟨ω α, hωmem α⟩
  have hdual (α β : ι) :
      B (v α : Vstar T) (ωE β : Vstar T) = if α = β then 1 else 0 := by
    change B ((1 : ℝ) ⊗ₜ[ℤ] (ρ α).1) (ω β) = _
    rw [hω β (ρ α) α.2]
    by_cases h : α = β
    · subst h
      simp
    · have h' : ρ α ≠ ρ β := fun h' => by
        apply h
        apply Subtype.ext
        have h'' := Subtype.ext_iff.mp h'
        exact h''
      simp [h, h']
  let ℓ : ι → E →ₗ[ℝ] ℝ := fun β => (B.flip (ω β)).comp (relativeRootSpanReal i).subtype
  have hℓ (α β : ι) : ℓ β (v α) = if α = β then 1 else 0 := hdual α β
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg β
    have h := congrArg (ℓ β) hg
    rw [map_sum, map_zero] at h
    simp only [map_smul, smul_eq_mul, hℓ, mul_ite, mul_one, mul_zero] at h
    rw [Finset.sum_eq_single β (fun x _ hx => by simp [hx])
      (fun h => absurd (Finset.mem_univ β) h)] at h
    simpa using h
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    refine le_of_eq ((Submodule.span_range_subtype_eq_top_iff (relativeRootSpanReal i)
      hroot).mpr ?_).symm
    rw [← span_simple_eq_rootSpan D ν hν]
    congr 1
    ext x
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨α.1, α.2, rfl⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨⟨α, hα⟩, rfl⟩
  let b : Module.Basis ι ℝ E := Module.Basis.mk hli hsp
  obtain ⟨c, hc, r, hr, hμ⟩ := exists_central_add_root hG hi μ
  obtain ⟨F, t, s, ht, hs, hrep⟩ := exists_cone_decomposition_of_form
    (B.compl₁₂ (relativeRootSpanReal i).subtype (relativeRootSpanReal i).subtype)
    (fun x y => hB.1 _ _) (fun x hx => hB.2.1 _ (fun h => hx (Submodule.coe_eq_zero.mp h)))
    b ωE (fun α β => by rw [Module.Basis.mk_apply]; exact hdual α β) ⟨r, hr⟩
  let ℓ' : ι → E →ₗ[ℝ] ℝ := fun γ => (B (v γ : Vstar T)).comp (relativeRootSpanReal i).subtype
  have hAval (γ : ι) : B (v γ : Vstar T) ((∑ i ∈ Finset.univ \ F, t i • ωE i : E) : Vstar T) =
      if γ ∈ Finset.univ \ F then t γ else 0 := by
    change ℓ' γ (∑ i ∈ Finset.univ \ F, t i • ωE i) = _
    rw [map_sum]
    have hℓ' (i' : ι) : ℓ' γ (ωE i') = if γ = i' then 1 else 0 := hdual γ i'
    simp only [map_smul, smul_eq_mul, hℓ']
    split_ifs with hγ
    · rw [Finset.sum_eq_single γ (fun x _ hx => by simp [Ne.symm hx]) (fun h => absurd hγ h)]
      simp
    · exact Finset.sum_eq_zero (fun x hx => by
        have hne : γ ≠ x := fun h => hγ (h ▸ hx)
        simp [hne])
  have hcoe : r = ((∑ i ∈ Finset.univ \ F, t i • ωE i : E) : Vstar T) -
      ((∑ j ∈ F, s j • b j : E) : Vstar T) := by
    have h := congrArg Subtype.val hrep
    rw [Submodule.coe_sub] at h
    exact h
  have hSval : ((∑ j ∈ F, s j • b j : E) : Vstar T) =
      ∑ j ∈ F, s j • ((1 : ℝ) ⊗ₜ[ℤ] (j : characterLattice T)) := by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Module.Basis.mk_apply]
  refine ⟨Subtype.val '' (F : Set ι), c, ((∑ i ∈ Finset.univ \ F, t i • ωE i : E) : Vstar T),
    -((∑ j ∈ F, s j • b j : E) : Vstar T), Set.empty_subset _, ?_, ?_, hc, ?_, ?_⟩
  · rintro _ ⟨j, -, rfl⟩
    exact j.2
  · rw [hμ, hcoe]
    abel
  · refine ⟨Submodule.coe_mem _, fun α hα => ?_, fun α hα hαK => ?_⟩
    · obtain ⟨j, hjF, hj⟩ := hα
      apply (pair_eq_zero_iff D hB α _).mpr
      rw [hB.1]
      have hαj : ((1 : ℝ) ⊗ₜ[ℤ] α.1 : Vstar T) = (v j : Vstar T) := by
        change _ = (1 : ℝ) ⊗ₜ[ℤ] j.1
        rw [hj]
      have hjF' : j ∈ F := hjF
      rw [hαj, hAval j]
      simp [hjF']
    · have hjF : (⟨α.1, hα⟩ : ι) ∉ F := fun h => hαK ⟨⟨α.1, hα⟩, h, rfl⟩
      apply (pair_pos_iff D hB α _).mpr
      rw [hB.1]
      have h2 : B ((1 : ℝ) ⊗ₜ[ℤ] α.1)
          ((∑ i ∈ Finset.univ \ F, t i • ωE i : E) : Vstar T) =
          if (⟨α.1, hα⟩ : ι) ∈ Finset.univ \ F then t ⟨α.1, hα⟩ else 0 :=
        hAval ⟨α.1, hα⟩
      have hmem : (⟨α.1, hα⟩ : ι) ∈ Finset.univ \ F := by simpa using hjF
      rw [h2]
      simp only [hmem, ↓reduceIte]
      exact ht _ hmem
  · refine ⟨(mem_corootAnnihilator i D ∅ _).mpr fun α h => absurd h (Set.notMem_empty _),
      -(-((∑ j ∈ F, s j • b j : E) : Vstar T)), ?_, by rw [sub_self]; exact zero_mem _⟩
    rw [neg_neg, hSval, Set.sdiff_empty]
    refine Submodule.sum_mem _ fun j hj => ?_
    exact PointedCone.smul_mem _ (hs j hj) (Submodule.subset_span ⟨j.1, ⟨j, hj, rfl⟩, rfl⟩)

end Existence

/-! ### The realization of `𝔞*_M` (conjunct 1) -/

section Realization

variable (ν : cocharacterLattice T)

/-- Conjunct 1 of V.3.18: restriction along the split-centre map is a bijection
from the coroot annihilator of `J` onto the real characters of `A_M`. -/
theorem existsUnique_restrict (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hB : IsWeylInvariantInnerProduct i B)
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {P M : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {J : Set (characterLattice T)} {f : A ⟶ T}
    (hc : (⟨T, i, ν, J, f⟩ : ParabolicRootPresentationData A G).IsCompatible p l a)
    (x : Vstar A) :
    ∃! y : Vstar T, y ∈ corootAnnihilator i D J ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y = x := by
  classical
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have hJΔ : J ⊆ simpleRelativeRoots i ν := hc.subset_simpleRoots
  have hJr : J ⊆ relativeRoots i := fun _ h => simple_subset_roots ν (hJΔ h)
  obtain ⟨hJfin, hVfin, -, hVrank, hrank⟩ :=
    standardLeviCentralDirections.1 k G hG T i hi ν hν J hJΔ
  have : IsAffineHom M.X.hom := hc.levi.isConnectedReductive.isAffineHom
  have hjc : IsClosedSubgroup (l ≫ p) :=
    hc.levi.isClosedSubgroup.comp hc.parabolic.isClosedSubgroup
  have := hjc.mono
  have hj : (standardLevi i ν J).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, hc.levi_eq⟩
  obtain ⟨-, hsplit⟩ := standardLeviCentralDirections.2 k G hG T i hi ν hν J hJΔ M (l ≫ p) hjc hj
  obtain ⟨hVAfin, f', hf'comp, -, hf'inj, hf'range, -, -, -⟩ := hsplit A a hc.splitComponent
  have hff' : f' = f := by
    have hm : Mono i.hom.hom := Over.mono_of_mono_left _
    have hg : CommGroupScheme.groupHom f' = CommGroupScheme.groupHom f := by
      apply (Grp.forget (Over (Spec (CommRingCat.of k)))).map_injective
      apply hm.right_cancellation
      have h' := congrArg (Grp.forget (Over (Spec (CommRingCat.of k)))).map
        (hf'comp.trans hc.factor_comp.symm)
      rw [Functor.map_comp, Functor.map_comp] at h'
      exact h'
    exact congrArg Additive.ofMul hg
  rw [hff'] at hf'inj hf'range
  have hA : IsSplitTorus A.toGrp := hc.splitComponent.1.1.1
  let ρ := rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
  have hker : LinearMap.ker ρ =
      Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J) := by
    rw [ker_restrictReal_eq_characterAnnihilator_range hA f, hf'range,
      rootAnnihilator_eq_cocharacterAnnihilator, characterAnnihilator_cocharacterAnnihilator hT]
  have hinj : ∀ y₁ ∈ corootAnnihilator i D J, ∀ y₂ ∈ corootAnnihilator i D J,
      ρ y₁ = ρ y₂ → y₁ = y₂ := by
    intro y₁ h₁ y₂ h₂ h
    have hd : y₁ - y₂ ∈ LinearMap.ker ρ := by
      rw [LinearMap.mem_ker, map_sub, h, sub_self]
    rw [hker] at hd
    have hann := sub_mem h₁ h₂
    have h0 := form_eq_zero_of_pair_eq_zero D hB hJr
      ((mem_corootAnnihilator i D J _).mp hann) hd
    exact sub_eq_zero.mp (eq_zero_of_form_self_nonpos hB h0.le)
  -- dimension count
  have : FiniteDimensional ℝ (Vstar T) :=
    LinearEquiv.finiteDimensional (characterDualEquiv hT).symm
  have : FiniteDimensional ℝ (Vstar A) :=
    LinearEquiv.finiteDimensional (characterDualEquiv hA).symm
  have hdimT : Module.finrank ℝ (Vstar T) = Module.finrank ℝ (V T) :=
    (characterDualEquiv hT).finrank_eq.trans Subspace.dual_finrank_eq
  have hdimA : Module.finrank ℝ (Vstar A) = Module.finrank ℝ (V A) :=
    (characterDualEquiv hA).finrank_eq.trans Subspace.dual_finrank_eq
  have hdimVA : Module.finrank ℝ (V A) = Module.finrank ℝ (rootAnnihilator T J) := by
    rw [(LinearEquiv.ofInjective _ hf'inj).finrank_eq, hf'range]
  have : Fintype J := Fintype.ofFinite J
  let Φ : Vstar T →ₗ[ℝ] (J → ℝ) :=
    LinearMap.pi fun β : J => (pair T).flip ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨β.1, hJr β.2⟩)
  have hkerΦ : LinearMap.ker Φ ≤ corootAnnihilator i D J := by
    intro y hy
    rw [mem_corootAnnihilator]
    intro α hα
    have h := congrFun (LinearMap.mem_ker.mp hy) ⟨α.1, hα⟩
    exact h
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : Module.finrank ℝ (LinearMap.range Φ) ≤ Nat.card J := by
    rw [Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card ℝ]
    exact Submodule.finrank_le _
  have hkerle := Submodule.finrank_mono hkerΦ
  let ρ' := ρ.domRestrict (corootAnnihilator i D J)
  have hρ'inj : Function.Injective ρ' := fun y₁ y₂ h =>
    Subtype.ext (hinj y₁ y₁.2 y₂ y₂.2 h)
  have hle : Module.finrank ℝ (corootAnnihilator i D J) ≤ Module.finrank ℝ (Vstar A) :=
    LinearMap.finrank_le_finrank_of_injective hρ'inj
  have hrn' : Module.finrank ℝ (LinearMap.range Φ) + Module.finrank ℝ (LinearMap.ker Φ) =
      Module.finrank ℝ (Vstar T) := hrn
  have hkerle' : Module.finrank ℝ (LinearMap.ker Φ) ≤
      Module.finrank ℝ (corootAnnihilator i D J) := hkerle
  have h1 : Module.finrank ℝ (Vstar A) + Nat.card J = Module.finrank ℝ (Vstar T) := by
    rw [hdimA, hdimVA, hrank, hdimT, hVrank]
  have heq : Module.finrank ℝ (corootAnnihilator i D J) = Module.finrank ℝ (Vstar A) := by
    omega
  have hsurj : Function.Surjective ρ' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hρ'inj
  obtain ⟨⟨y, hy⟩, hyx⟩ := hsurj x
  exact ⟨y, ⟨hy, hyx⟩, fun y' hy' => hinj y' hy'.1 y hy (hy'.2.trans hyx.symm)⟩

end Realization

end LanglandsDecomposition

open LanglandsDecomposition in
/-- **Renard V.3.18, Langlands' combinatorial lemma** for actual standard
parabolics, with the `μ⁻` cone of the V.5.5 proof. -/
theorem langlandsCombinatorialDecomposition :
    LanglandsCombinatorialDecompositionStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν D B hB A P M p l a J f hc
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  have hfinite := hT.finite_relativeRoots i
  have hJΔ : J ⊆ simpleRelativeRoots i ν := hc.subset_simpleRoots
  refine ⟨existsUnique_restrict D ν hG hi hν hB hc, fun μ hμ => ?_⟩
  obtain ⟨K₀, G₀, p₀, m₀, h₀⟩ := exists_empty_decomposition D ν hG hi hν hB μ
  have hJ₀ := isLanglandsDecomposition_of_empty D ν hT hfinite hν hJΔ hμ h₀
  refine ⟨⟨(K₀, G₀, p₀, m₀), hJ₀, ?_⟩, ?_⟩
  · rintro ⟨K', G', p', m'⟩ h'
    obtain ⟨e1, e2, e3, e4⟩ := eq_of_isLanglandsDecomposition D hB h' hJ₀
    exact Prod.ext_iff.mpr ⟨e1, Prod.ext_iff.mpr ⟨e2, Prod.ext_iff.mpr ⟨e3, e4⟩⟩⟩
  · intro K μG μp μm h
    obtain ⟨e1, e2, e3, e4⟩ := eq_of_isLanglandsDecomposition D hB h hJ₀
    refine ⟨fun z hz => form_sub_G_central D hB h hz,
      ⟨p_mem_closedFace D h, fun w hw => nearest_of_variational hB (p_variational D hB h hw)⟩,
      ⟨neg_m_mem_cone D h, fun w hw => nearest_of_variational hB (m_variational D hB h hw)⟩,
      form_G_p D hB h, form_G_m D hB h, form_p_m D hB h, fun K' μG' μp' μm' => ⟨fun h' => ?_, ?_⟩⟩
    · obtain ⟨f1, f2, f3, f4⟩ := eq_of_isLanglandsDecomposition D hB h' h₀
      exact ⟨f1.trans e1.symm, f2.trans e2.symm, f3.trans e3.symm, f4.trans e4.symm⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      rw [e1, e2, e3, e4]
      exact h₀

end Langlands.GroupScheme
