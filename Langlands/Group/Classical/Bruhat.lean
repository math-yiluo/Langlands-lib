import Langlands.Group.Classical.SiegelParabolic

/-!
# The Bruhat decomposition and the generalized Bruhat decomposition

GKT §4.4.2 (the Bruhat decomposition with respect to the Siegel parabolic) and §4.4.3
(Proposition 4.30, Theorem 4.31: the generalized Bruhat decomposition).

Let `h` be a non-degenerate `-ε`-Hermitian form (the book's `W`) with a standard basis `e`,
`X = span {eᵢ}`, `Y = span {eᵢ*}`, `P = P(X)`, and for `A ⊆ ι` let `X_A`, `Y_A`, `W_A = X_A ⊕ Y_A`
be the coordinate subspaces (`blockFst`, `blockSnd`, `block`; GKT (4.7)).

* `exists_isometry_map_pair_iff`: two pairs of Lagrangians are conjugate iff their intersections
  have the same dimension;
* `mem_doubleCoset_weylElement_iff`: `g ∈ P w_S P` iff `dim (X ∩ g X) + |S| = n`, equivalently
  `|S| = n - dim ker c(g)` (`siegelCPart`); hence `G = ⋃_S P w_S P` (`exists_mem_doubleCoset`), and
  `P w_S P = P w_{S'} P` iff `|S| = |S'|`;
* `exists_mem_siegelParabolic_map_eq` (Proposition 4.30 in coordinates) and
  `exists_generalizedBruhat` (Theorem 4.31): `g₁ = p₁ κ₁ p⁻¹`, `g₂ = p κ₂ p₂⁻¹` with
  `κ₁ = w_{S₁ ∪ S₂ ∪ S₄}`, `κ₂ = n(b) w_{S₁ ∪ S₃ ∪ S₄}`, where the form `(y, y') ↦ h(b y, y')` on
  `Y_{S₄}` (`siegelHermForm`) is the Leray invariant `L(X, g₁⁻¹ X, g₂ X)`;
  `nonempty_isometryEquiv_lerayInvariant_of_eq_mul`: `L(X, g₁⁻¹ X, g₂ X) = L(X, κ₁⁻¹ X, κ₂ X)`.
-/
noncomputable section

namespace Langlands

namespace EpsilonHermitianForm

open Module
open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V]

/-! ### Coordinates of a standard basis -/

theorem mem_orthogonal_span_iff {ε' : ℤˣ} {h : EpsilonHermitianForm τ ε' V} {S : Set V} {v : V} :
    v ∈ h.orthogonal (Submodule.span D S) ↔ ∀ s ∈ S, h v s = 0 := by
  refine ⟨fun H s hs => H s (Submodule.subset_span hs), fun H u hu => ?_⟩
  induction hu using Submodule.span_induction with
  | mem x hx => exact H x hx
  | zero => exact h.map_zero_right v
  | add x y _ _ hx hy => rw [h.map_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [h.map_smul_right, hx, zero_mul]

namespace StandardBasis

variable {ε' : ℤˣ} {h : EpsilonHermitianForm τ ε' V} {ι : Type*} [DecidableEq ι]
  (e : h.StandardBasis ι)

/-- The subspace `X_A = span {eᵢ | i ∈ A}` (GKT (4.7)). -/
def blockFst (A : Set ι) : Submodule D V := Submodule.span D (e.fst '' A)

/-- The subspace `Y_A = span {eᵢ* | i ∈ A}` (GKT (4.7)). -/
def blockSnd (A : Set ι) : Submodule D V := Submodule.span D (e.snd '' A)

/-- The subspace `W_A = X_A ⊕ Y_A`. -/
def block (A : Set ι) : Submodule D V := e.blockFst A ⊔ e.blockSnd A

theorem fst_mem_blockFst {A : Set ι} {i : ι} (hi : i ∈ A) : e.fst i ∈ e.blockFst A :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem snd_mem_blockSnd {A : Set ι} {i : ι} (hi : i ∈ A) : e.snd i ∈ e.blockSnd A :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem fst_mem_block {A : Set ι} {i : ι} (hi : i ∈ A) : e.fst i ∈ e.block A :=
  Submodule.mem_sup_left (e.fst_mem_blockFst hi)

theorem snd_mem_block {A : Set ι} {i : ι} (hi : i ∈ A) : e.snd i ∈ e.block A :=
  Submodule.mem_sup_right (e.snd_mem_blockSnd hi)

theorem blockFst_univ : e.blockFst Set.univ = e.lagrangianFst := by
  rw [blockFst, Set.image_univ]; rfl

theorem blockSnd_univ : e.blockSnd Set.univ = e.lagrangianSnd := by
  rw [blockSnd, Set.image_univ]; rfl

theorem blockFst_le_lagrangianFst (A : Set ι) : e.blockFst A ≤ e.lagrangianFst :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem blockSnd_le_lagrangianSnd (A : Set ι) : e.blockSnd A ≤ e.lagrangianSnd :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem finrank_blockFst (A : Finset ι) : finrank D (e.blockFst A) = A.card := by
  rw [blockFst, show (e.fst '' (A : Set ι)) = Set.range (e.basis ∘ (Sum.inl ∘ ((↑) : A → ι))) by
    ext v; simp [fst]]
  rw [finrank_span_eq_card (e.basis.linearIndependent.comp _
    (Sum.inl_injective.comp Subtype.val_injective)), Fintype.card_coe]

theorem finrank_blockSnd (A : Finset ι) : finrank D (e.blockSnd A) = A.card := by
  rw [blockSnd, show (e.snd '' (A : Set ι)) = Set.range (e.basis ∘ (Sum.inr ∘ ((↑) : A → ι))) by
    ext v; simp [snd]]
  rw [finrank_span_eq_card (e.basis.linearIndependent.comp _
    (Sum.inr_injective.comp Subtype.val_injective)), Fintype.card_coe]

/-- Basis vectors with distinct indices are orthogonal. -/
theorem apply_basis_eq_zero_of_ne {k l : ι ⊕ ι} (hkl : Sum.elim id id k ≠ Sum.elim id id l) :
    h (e.basis k) (e.basis l) = 0 := by
  rcases k with i | i <;> rcases l with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, id] at hkl
  · exact e.apply_inl_inl i j
  · rw [e.apply_inl_inr, ite_eq_right_iff]; exact fun H => absurd H hkl
  · rw [e.apply_inr_inl, ite_eq_right_iff]; exact fun H => absurd H (Ne.symm hkl)
  · exact e.apply_inr_inr i j

theorem block_eq_span (A : Set ι) :
    e.block A = Submodule.span D (e.basis '' ((Sum.inl '' A) ∪ (Sum.inr '' A))) := by
  rw [block, blockFst, blockSnd, ← Submodule.span_union, Set.image_union, ← Set.image_comp,
    ← Set.image_comp]; rfl

theorem block_le_orthogonal {A B : Set ι} (hAB : Disjoint A B) :
    e.block A ≤ h.orthogonal (e.block B) := by
  rw [e.block_eq_span A, e.block_eq_span B, Submodule.span_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [SetLike.mem_coe, mem_orthogonal_span_iff]
  rintro _ ⟨l, hl, rfl⟩
  apply e.apply_basis_eq_zero_of_ne
  intro hkl
  rcases hk with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> rcases hl with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;>
    simp only [Sum.elim_inl, Sum.elim_inr, id] at hkl <;> subst hkl <;>
    exact Set.disjoint_left.1 hAB hi hj

theorem block_sup_block_compl (A : Set ι) : e.block A ⊔ e.block Aᶜ = ⊤ := by
  rw [eq_top_iff, ← e.basis.span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rcases k with i | i
  · by_cases hi : i ∈ A
    · exact Submodule.mem_sup_left (e.fst_mem_block hi)
    · exact Submodule.mem_sup_right (e.fst_mem_block (Set.mem_compl hi))
  · by_cases hi : i ∈ A
    · exact Submodule.mem_sup_left (e.snd_mem_block hi)
    · exact Submodule.mem_sup_right (e.snd_mem_block (Set.mem_compl hi))

theorem blockFst_le_block (A : Set ι) : e.blockFst A ≤ e.block A := le_sup_left

theorem blockSnd_le_block (A : Set ι) : e.blockSnd A ≤ e.block A := le_sup_right

variable [Fintype ι]

theorem restrict_block_nondegenerate (A : Set ι) : (h.restrict (e.block A)).Nondegenerate := by
  rw [restrict_nondegenerate_iff, eq_bot_iff]
  rintro v ⟨hvA, hv⟩
  have hv' : v ∈ h.orthogonal (e.block Aᶜ) :=
    e.block_le_orthogonal disjoint_compl_right hvA
  have : v ∈ h.orthogonal (e.block A ⊔ e.block Aᶜ) := by
    rw [orthogonal_sup]; exact ⟨hv, hv'⟩
  rw [e.block_sup_block_compl, orthogonal_top e.nondegenerate] at this
  exact this

theorem disjoint_blockFst_blockSnd (A B : Set ι) : Disjoint (e.blockFst A) (e.blockSnd B) :=
  e.isCompl_lagrangianFst_lagrangianSnd.disjoint.mono (e.blockFst_le_lagrangianFst A)
    (e.blockSnd_le_lagrangianSnd B)

theorem disjoint_blockFst_blockSnd_comap (A : Set ι) :
    Disjoint ((e.blockFst A).comap (e.block A).subtype)
      ((e.blockSnd A).comap (e.block A).subtype) := by
  rw [Submodule.disjoint_def]
  intro v hv hv'
  exact Subtype.ext (Submodule.disjoint_def.1 (e.disjoint_blockFst_blockSnd A A) _ hv hv')

/-- The blocks of a partition of the index set form an orthogonal decomposition. -/
theorem isOrthogonalDecomposition_block {κ : Type*} (σ : ι → κ) :
    h.IsOrthogonalDecomposition (fun j => e.block {i | σ i = j}) := by
  refine ⟨fun j j' hjj' => e.block_le_orthogonal ?_, ?_, fun j => e.restrict_block_nondegenerate _⟩
  · rw [Set.disjoint_left]; rintro i rfl hi; exact hjj' hi
  · rw [eq_top_iff, ← e.basis.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases k with i | i
    · exact Submodule.mem_iSup_of_mem (σ i) (e.fst_mem_block rfl)
    · exact Submodule.mem_iSup_of_mem (σ i) (e.snd_mem_block rfl)

variable [FiniteDimensional D V]

theorem finrank_block (A : Finset ι) : finrank D (e.block A) = 2 * A.card := by
  have := Submodule.finrank_sup_add_finrank_inf_eq (e.blockFst A) (e.blockSnd A)
  rw [disjoint_iff.1 (e.disjoint_blockFst_blockSnd A A), finrank_bot, add_zero,
    e.finrank_blockFst, e.finrank_blockSnd] at this
  rw [block, this]; ring

/-- `X_A` is a Lagrangian of `W_A`. -/
theorem isLagrangian_blockFst (A : Finset ι) :
    (h.restrict (e.block A)).IsLagrangian ((e.blockFst A).comap (e.block A).subtype) := by
  apply isLagrangian_of_two_mul_finrank (e.restrict_block_nondegenerate A)
  · intro x hx y hy
    exact e.isLagrangian_lagrangianFst.apply_eq_zero (e.blockFst_le_lagrangianFst A hx)
      (e.blockFst_le_lagrangianFst A hy)
  · rw [finrank_comap_subtype, inf_eq_left.2 (e.blockFst_le_block A), e.finrank_blockFst,
      e.finrank_block]

/-- `Y_A` is a Lagrangian of `W_A`. -/
theorem isLagrangian_blockSnd (A : Finset ι) :
    (h.restrict (e.block A)).IsLagrangian ((e.blockSnd A).comap (e.block A).subtype) := by
  apply isLagrangian_of_two_mul_finrank (e.restrict_block_nondegenerate A)
  · intro x hx y hy
    exact e.isLagrangian_lagrangianSnd.apply_eq_zero (e.blockSnd_le_lagrangianSnd A hx)
      (e.blockSnd_le_lagrangianSnd A hy)
  · rw [finrank_comap_subtype, inf_eq_left.2 (e.blockSnd_le_block A), e.finrank_blockSnd,
      e.finrank_block]

end StandardBasis

/-! ### Orbits of pairs and the Bruhat decomposition (GKT §4.4.2) -/

/-- Two forms on zero spaces are isometric. -/
def isometryEquivOfSubsingleton {ε'' : ℤˣ} {U U' : Type*} [AddCommGroup U] [Module D U]
    [AddCommGroup U'] [Module D U'] [Subsingleton U] [Subsingleton U']
    (k : EpsilonHermitianForm τ ε'' U) (k' : EpsilonHermitianForm τ ε'' U') :
    IsometryEquiv k k' where
  toLinearEquiv := LinearEquiv.ofSubsingleton U U'
  map_app' x y := by
    have h₁ : ∀ u : U, k u y = 0 := fun u => by rw [Subsingleton.elim u 0, k.map_zero_left]
    have h₂ : ∀ u u' : U', k' u u' = 0 := fun u u' => by
      rw [Subsingleton.elim u 0, k'.map_zero_left]
    rw [h₁, h₂]

theorem lerayM_self (X₁ X₂ : Submodule D V) : lerayM X₁ X₂ X₂ = X₂ := by
  simp only [lerayM, inf_idem]
  exact le_antisymm (sup_le (sup_le inf_le_right le_rfl) inf_le_left)
    (le_sup_of_le_left le_sup_right)

section Pairs

variable {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional D V] [NeZero (2 : D)]

omit [FiniteDimensional D V] [NeZero (2 : D)] in
private theorem subsingleton_reductionSubmodule {X₁ X₂ : Submodule D V} (h₂ : h.IsLagrangian X₂) :
    Subsingleton (h.reductionSubmodule (lerayM X₁ X₂ X₂) X₂) := by
  have key : ∀ v : V, v ∈ h.orthogonal (lerayM X₁ X₂ X₂) → v ∈ lerayM X₁ X₂ X₂ := by
    rw [lerayM_self, h₂]; exact fun v hv => hv
  constructor
  intro a b
  apply Subtype.ext
  have hz : ∀ c : h.ReductionSpace (lerayM X₁ X₂ X₂), c = 0 := by
    intro c
    obtain ⟨x, rfl⟩ := h.reductionMap_surjective _ c
    rw [reductionMap_eq_zero_iff]; exact key x x.2
  rw [hz a, hz b]

/-- GKT §4.4.2: two pairs of Lagrangians are conjugate under the isometry group if and only if their
intersections have the same dimension. -/
theorem exists_isometry_map_pair_iff (hh : h.Nondegenerate) {X₁ X₂ Y₁ Y₂ : Submodule D V}
    (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂) (k₁ : h.IsLagrangian Y₁)
    (k₂ : h.IsLagrangian Y₂) :
    (∃ g : h.isometryGroup, X₁.map (g : V ≃ₗ[D] V).toLinearMap = Y₁ ∧
        X₂.map (g : V ≃ₗ[D] V).toLinearMap = Y₂) ↔
      finrank D (X₁ ⊓ X₂ : Submodule D V) = finrank D (Y₁ ⊓ Y₂ : Submodule D V) := by
  constructor
  · rintro ⟨g, rfl, rfl⟩
    rw [← Submodule.map_inf _ (g : V ≃ₗ[D] V).injective]
    exact (LinearEquiv.finrank_map_eq _ _).symm
  · intro hd
    have := (exists_isometry_map_iff hh h₁ h₂ h₂ k₁ k₂ k₂).2
      ⟨by rw [inf_assoc, inf_idem, inf_assoc, inf_idem]; exact hd, hd,
        by rw [inf_idem, inf_idem]; exact finrank_eq_of_isLagrangian hh h₂ k₂, hd, by
          have := subsingleton_reductionSubmodule (X₁ := X₁) h₂
          have := subsingleton_reductionSubmodule (h := h) (X₁ := Y₁) k₂
          exact ⟨isometryEquivOfSubsingleton _ _⟩⟩
    obtain ⟨g, hg₁, hg₂, -⟩ := this
    exact ⟨g, hg₁, hg₂⟩

end Pairs

section CPart

variable {ε' : ℤˣ} {h : EpsilonHermitianForm τ ε' V} {X Y : Submodule D V}

/-- The `c`-part `c(g) : X → Y` of `g` for a polarization `V = X ⊕ Y` (GKT §4.4.2): the
`Y`-component of `g` on `X`. -/
def siegelCPart (hXY : IsCompl X Y) (g : h.isometryGroup) : X →ₗ[D] Y :=
  Y.projectionOnto X hXY.symm ∘ₗ (g : V ≃ₗ[D] V).toLinearMap ∘ₗ X.subtype

theorem mem_ker_siegelCPart (hXY : IsCompl X Y) (g : h.isometryGroup) {x : X} :
    x ∈ LinearMap.ker (siegelCPart hXY g) ↔ (g : V ≃ₗ[D] V) x ∈ X := by
  rw [LinearMap.mem_ker, siegelCPart, LinearMap.comp_apply, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_eq_zero_iff]
  rfl

/-- `ker c(g) = X ∩ g⁻¹ X`, so `dim ker c(g) = dim (X ∩ g X)`. -/
theorem finrank_ker_siegelCPart [FiniteDimensional D V] (hXY : IsCompl X Y)
    (g : h.isometryGroup) : finrank D (LinearMap.ker (siegelCPart hXY g)) =
      finrank D (X ⊓ X.map (g : V ≃ₗ[D] V).toLinearMap : Submodule D V) := by
  have e₁ : LinearMap.ker (siegelCPart hXY g) =
      (X.comap (g : V ≃ₗ[D] V).toLinearMap).comap X.subtype := by
    ext x; rw [mem_ker_siegelCPart]; rfl
  rw [e₁, finrank_comap_subtype, Submodule.comap_equiv_eq_map_symm,
    ← LinearEquiv.finrank_map_eq (g : V ≃ₗ[D] V), Submodule.map_inf _ (g : V ≃ₗ[D] V).injective,
    (Submodule.map_symm_eq_iff _).1 rfl, inf_comm]

end CPart

namespace StandardBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : EpsilonHermitianForm τ (-ε) V}
  (e : h.StandardBasis ι) [FiniteDimensional D V]

/-- `w_S X = X_{S^c} ⊕ Y_S`. -/
theorem map_weylElement_lagrangianFst (S : Finset ι) :
    e.lagrangianFst.map ((e.weylElement S : h.isometryGroup) : V ≃ₗ[D] V).toLinearMap =
      e.blockFst (↑S)ᶜ ⊔ e.blockSnd S := by
  rw [lagrangianFst, Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    by_cases hi : i ∈ S
    · rw [e.weylElement_fst_of_mem hi]
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (e.snd_mem_blockSnd hi))
    · rw [e.weylElement_fst_of_not_mem hi]
      exact Submodule.mem_sup_left (e.fst_mem_blockFst (show i ∈ (↑S : Set ι)ᶜ from hi))
  · refine sup_le ?_ ?_
    · rw [blockFst, Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i ∉ S := hi
      refine Submodule.subset_span ⟨i, ?_⟩
      simp only [Function.comp_apply, LinearEquiv.coe_coe]
      exact e.weylElement_fst_of_not_mem hi'
    · rw [blockSnd, Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have hmem : ((e.weylElement S : h.isometryGroup) : V ≃ₗ[D] V) (e.fst i) ∈
          Submodule.span D (Set.range (⇑((e.weylElement S : h.isometryGroup) :
            V ≃ₗ[D] V).toLinearMap ∘ e.fst)) := Submodule.subset_span ⟨i, rfl⟩
      rw [e.weylElement_fst_of_mem hi] at hmem
      have := Submodule.smul_mem _ (((-ε : ℤˣ) : ℤ) : D) hmem
      rwa [smul_smul, units_int_cast_mul_self', one_smul] at this

theorem lagrangianFst_inf_map_weylElement (S : Finset ι) :
    e.lagrangianFst ⊓ e.lagrangianFst.map ((e.weylElement S : h.isometryGroup) :
      V ≃ₗ[D] V).toLinearMap = e.blockFst (↑S)ᶜ := by
  rw [map_weylElement_lagrangianFst]
  apply le_antisymm
  · rintro v ⟨hvX, hv⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have hbX : b ∈ e.lagrangianFst := by
      have := e.lagrangianFst.sub_mem hvX (e.blockFst_le_lagrangianFst _ ha)
      rwa [add_sub_cancel_left] at this
    rw [Submodule.disjoint_def.1 e.isCompl_lagrangianFst_lagrangianSnd.disjoint b hbX
      (e.blockSnd_le_lagrangianSnd _ hb), add_zero]
    exact ha
  · exact le_inf (e.blockFst_le_lagrangianFst _) le_sup_left

theorem finrank_lagrangianFst_inf_map_weylElement (S : Finset ι) :
    finrank D (e.lagrangianFst ⊓ e.lagrangianFst.map ((e.weylElement S : h.isometryGroup) :
      V ≃ₗ[D] V).toLinearMap : Submodule D V) + S.card = Fintype.card ι := by
  rw [e.lagrangianFst_inf_map_weylElement, show ((↑S : Set ι)ᶜ) = ↑(Sᶜ) from
    (Finset.coe_compl S).symm, e.finrank_blockFst, Finset.card_compl, Nat.sub_add_cancel
      (Finset.card_le_univ S)]

variable [NeZero (2 : D)]

/-- GKT §4.4.2: `g ∈ P w_S P` if and only if `dim (X ∩ g X) = n - |S|`. -/
theorem mem_doubleCoset_weylElement_iff (S : Finset ι) (g : h.isometryGroup) :
    (∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
        g = p₁ * e.weylElement S * p₂) ↔
      finrank D (e.lagrangianFst ⊓ e.lagrangianFst.map (g : V ≃ₗ[D] V).toLinearMap :
        Submodule D V) + S.card = Fintype.card ι := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    rw [map_isometryGroup_mul, map_isometryGroup_mul, hp₂]
    conv_lhs => rw [show e.lagrangianFst = e.lagrangianFst.map ((p₁ : h.isometryGroup) :
      V ≃ₗ[D] V).toLinearMap from hp₁.symm]
    rw [← Submodule.map_inf _ (p₁ : V ≃ₗ[D] V).injective, LinearEquiv.finrank_map_eq]
    conv_lhs => rw [hp₁]
    exact e.finrank_lagrangianFst_inf_map_weylElement S
  · intro hd
    have hXw := e.isLagrangian_lagrangianFst.map (e.weylElement S)
    have hXg := e.isLagrangian_lagrangianFst.map g
    obtain ⟨k, hk₁, hk₂⟩ := (exists_isometry_map_pair_iff e.nondegenerate
      e.isLagrangian_lagrangianFst hXg e.isLagrangian_lagrangianFst hXw).2
      (by have := e.finrank_lagrangianFst_inf_map_weylElement S; omega)
    refine ⟨k⁻¹, (h.siegelParabolic e.lagrangianFst).inv_mem hk₁, (e.weylElement S)⁻¹ * k * g,
      ?_, ?_⟩
    · rw [mem_siegelParabolic_iff, map_isometryGroup_mul, map_isometryGroup_mul, hk₂,
        ← map_isometryGroup_mul, inv_mul_cancel]
      exact Submodule.map_id _
    · group

/-- GKT §4.4.2: `g ∈ P w_S P` if and only if `|S| = n - dim ker c(g)`. -/
theorem mem_doubleCoset_weylElement_iff_finrank_ker (S : Finset ι) (g : h.isometryGroup) :
    (∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
        g = p₁ * e.weylElement S * p₂) ↔
      finrank D (LinearMap.ker (siegelCPart e.isCompl_lagrangianFst_lagrangianSnd g)) + S.card =
        Fintype.card ι := by
  rw [finrank_ker_siegelCPart]; exact e.mem_doubleCoset_weylElement_iff S g

/-- GKT §4.4.2, the Bruhat decomposition: every element of `G` lies in some `P w_S P`. -/
theorem exists_mem_doubleCoset (g : h.isometryGroup) :
    ∃ S : Finset ι, ∃ p₁ ∈ h.siegelParabolic e.lagrangianFst,
      ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst, g = p₁ * e.weylElement S * p₂ := by
  set d := finrank D (e.lagrangianFst ⊓ e.lagrangianFst.map (g : V ≃ₗ[D] V).toLinearMap :
    Submodule D V)
  have hd : d ≤ Fintype.card ι := by
    have := Submodule.finrank_mono (inf_le_left : e.lagrangianFst ⊓ e.lagrangianFst.map
      (g : V ≃ₗ[D] V).toLinearMap ≤ e.lagrangianFst)
    rwa [e.finrank_lagrangianFst] at this
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (n := Fintype.card ι - d)
    (by rw [Finset.card_univ]; omega)
  exact ⟨S, (e.mem_doubleCoset_weylElement_iff S g).2 (by rw [hS]; omega)⟩

/-- `P w_S P = P w_{S'} P` if and only if `|S| = |S'|` (GKT §4.4.2). -/
theorem mem_doubleCoset_weylElement_iff_card (S S' : Finset ι) :
    (∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
        e.weylElement S' = p₁ * e.weylElement S * p₂) ↔ S.card = S'.card := by
  rw [e.mem_doubleCoset_weylElement_iff]
  have := e.finrank_lagrangianFst_inf_map_weylElement S'
  omega

end StandardBasis

/-! ### The generalized Bruhat decomposition (GKT §4.4.3) -/

/-- An isometry carries a non-degenerate form to a non-degenerate form. -/
theorem IsometryEquiv.nondegenerate {ε'' : ℤˣ} {U U' : Type*} [AddCommGroup U] [Module D U]
    [AddCommGroup U'] [Module D U'] {k : EpsilonHermitianForm τ ε'' U}
    {k' : EpsilonHermitianForm τ ε'' U'} (φ : IsometryEquiv k k') (hk : k.Nondegenerate) :
    k'.Nondegenerate := by
  intro x hx
  have : φ.symm x = 0 := hk _ fun y => by
    rw [← φ.map_app, φ.apply_symm_apply]; exact hx _
  rw [← φ.apply_symm_apply x, this, map_zero]

/-- A Lagrangian contained in a Lagrangian is equal to it. -/
theorem IsLagrangian.eq_of_le {ε'' : ℤˣ} {k : EpsilonHermitianForm τ ε'' V} {A B : Submodule D V}
    (hA : k.IsLagrangian A) (hB : k.IsLagrangian B) (hAB : A ≤ B) : A = B :=
  le_antisymm hAB (by rw [← hA, ← hB]; exact orthogonal_le_orthogonal hAB)

section Generalized

variable {h : EpsilonHermitianForm τ (-ε) V}

/-- The `ε`-Hermitian form `(y, y') ↦ h (b y) y'` of `b ∈ Herm(Y, X)` on a subspace `U ≤ Y`
(GKT §4.4.1, (4.6)). -/
def siegelHermForm {X Y : Submodule D V} {b : Y →ₗ[D] X} (hb : b ∈ h.siegelHerm X Y)
    (U : Submodule D V) (hU : U ≤ Y) : EpsilonHermitianForm τ ε U where
  toFun y y' := h (b (Submodule.inclusion hU y)) y'
  map_add_left' y y' z := by simp only [map_add, Submodule.coe_add, h.map_add_left]
  map_smul_left' a y z := by simp only [map_smul, Submodule.coe_smul, h.map_smul_left]
  conj_swap' y y' := by
    have e := hb (Submodule.inclusion hU y) (Submodule.inclusion hU y')
    simp only [Submodule.coe_inclusion] at e
    change h (b (Submodule.inclusion hU y')) y =
      ((ε : ℤ) : D) * conj τ (h (b (Submodule.inclusion hU y)) y')
    rw [h.conj_swap (y : V) (b (Submodule.inclusion hU y') : V), Units.val_neg, Int.cast_neg,
      eq_neg_of_add_eq_zero_right e, RingInvo.conj_neg]
    noncomm_ring

theorem siegelHermForm_apply {X Y : Submodule D V} {b : Y →ₗ[D] X} (hb : b ∈ h.siegelHerm X Y)
    (U : Submodule D V) (hU : U ≤ Y) (y y' : U) :
    h.siegelHermForm hb U hU y y' = h (b (Submodule.inclusion hU y)) y' := rfl

/-- For Lagrangians `X, Y, Z` with `Z` a complement of `X`, there is `b ∈ Herm(Y, X)` with
`y + b y ∈ Z` for `y ∈ Y` (so that `n(b) Y = Z` when `Y` is a complement of `X` too). -/
theorem exists_siegelHerm_add_mem {X Y Z : Submodule D V} (hX : h.IsLagrangian X)
    (hY : h.IsLagrangian Y) (hZ : h.IsLagrangian Z) (hZX : IsCompl Z X) :
    ∃ b ∈ h.siegelHerm X Y, ∀ y : Y, (y : V) + b y ∈ Z := by
  have hsub : ∀ v : V, Z.projection X hZX v - v ∈ X := fun v => by
    have := Submodule.sub_projection_mem hZX v
    rw [← neg_sub]; exact X.neg_mem this
  let b : Y →ₗ[D] X := (((Z.projection X hZX) - LinearMap.id) ∘ₗ Y.subtype).codRestrict X
    (fun y => hsub y)
  have hq : ∀ y : Y, Z.projection X hZX y = (y : V) + b y := fun y => by
    change _ = (y : V) + (Z.projection X hZX y - y); abel
  refine ⟨b, fun y y' => ?_, fun y => ?_⟩
  · have e := hZ.apply_eq_zero (Submodule.projection_apply_mem hZX (y : V))
      (Submodule.projection_apply_mem hZX (y' : V))
    rw [hq, hq, h.map_add_left, h.map_add_right, h.map_add_right, hY.apply_eq_zero y.2 y'.2,
      hX.apply_eq_zero (b y).2 (b y').2, zero_add, add_zero, add_comm] at e
    exact e
  · rw [← hq]; exact Submodule.projection_apply_mem hZX _

private theorem fin_five_cases (j : Fin 5) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
  fin_cases j <;> simp

private theorem exists_fiber_card {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (n : κ → ℕ) (hn : ∑ j, n j = Fintype.card ι) :
    ∃ σ : ι → κ, ∀ j, (Finset.univ.filter fun i => σ i = j).card = n j := by
  have hc : Fintype.card ι = Fintype.card (Σ j, Fin (n j)) := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]; exact hn.symm
  let f := Fintype.equivOfCardEq hc
  refine ⟨fun i => (f i).1, fun j => ?_⟩
  rw [← Fintype.card_subtype, Fintype.card_congr ((f.subtypeEquiv (p := fun i => (f i).1 = j)
    (q := fun x => x.1 = j) (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype j)), Fintype.card_fin]

/-- Disjointness of the parts of two subspaces in `W` passes to `W`. -/
private theorem disjoint_comap_subtype {A B W : Submodule D V} (hAB : Disjoint (A ⊓ W) (B ⊓ W)) :
    Disjoint (A.comap W.subtype) (B.comap W.subtype) := by
  rw [Submodule.disjoint_def]
  intro w hwA hwB
  exact Subtype.ext (Submodule.disjoint_def.1 hAB _ ⟨hwA, w.2⟩ ⟨hwB, w.2⟩)

/-- An isometry `Φ` of `V` restricting to `φ : U ≅ W` carries `B ≤ U` to `A ∩ W` if `φ` carries
`B` to `A ∩ W` as subspaces of `U` and `W`. -/
private theorem map_eq_inf_of_map_comap {U W B A : Submodule D V} (Φ : V →ₗ[D] V)
    (φ : U →ₗ[D] W) (hΦ : ∀ u : U, Φ u = φ u) (hB : B ≤ U)
    (H : (B.comap U.subtype).map φ = A.comap W.subtype) : B.map Φ = A ⊓ W := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have : φ ⟨v, hB hv⟩ ∈ A.comap W.subtype := H ▸ ⟨⟨v, hB hv⟩, hv, rfl⟩
    rw [show Φ v = Φ (⟨v, hB hv⟩ : U) from rfl, hΦ]
    exact ⟨this, (φ ⟨v, hB hv⟩).2⟩
  · rintro w ⟨hwA, hwW⟩
    have : (⟨w, hwW⟩ : W) ∈ (B.comap U.subtype).map φ := H ▸ hwA
    obtain ⟨u, hu, hu'⟩ := this
    exact ⟨u, hu, by rw [hΦ u, hu']⟩

namespace StandardBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : h.StandardBasis ι)

omit [Fintype ι] in
theorem blockFst_sup_blockFst_compl (A : Set ι) :
    e.blockFst A ⊔ e.blockFst Aᶜ = e.lagrangianFst := by
  rw [blockFst, blockFst, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self,
    Set.image_univ]; rfl

omit [Fintype ι] in
theorem blockSnd_sup_blockSnd_compl (A : Set ι) :
    e.blockSnd A ⊔ e.blockSnd Aᶜ = e.lagrangianSnd := by
  rw [blockSnd, blockSnd, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self,
    Set.image_univ]; rfl

theorem disjoint_block_compl (A : Set ι) : Disjoint (e.block A) (e.block Aᶜ) := by
  rw [disjoint_iff, eq_bot_iff]
  refine le_trans (inf_le_inf_left _ (e.block_le_orthogonal disjoint_compl_left)) ?_
  exact (restrict_nondegenerate_iff.1 (e.restrict_block_nondegenerate A)).le

/-- An isometry carries `X` onto a Lagrangian `L` as soon as it carries every `eᵢ` into `L`. -/
theorem map_lagrangianFst_eq (g : h.isometryGroup) {L : Submodule D V} (hL : h.IsLagrangian L)
    (H : ∀ i, (g : V ≃ₗ[D] V) (e.fst i) ∈ L) :
    e.lagrangianFst.map (g : V ≃ₗ[D] V).toLinearMap = L := by
  refine (e.isLagrangian_lagrangianFst.map g).eq_of_le hL ?_
  rw [lagrangianFst, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact H i

variable [FiniteDimensional D V]

theorem weylElement_inv_fst_of_mem {S : Finset ι} {i : ι} (hi : i ∈ S) :
    (((e.weylElement S)⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) (e.fst i) = e.snd i := by
  rw [← e.weylElement_snd_of_mem hi, isometryGroup_coe_inv_apply']

theorem weylElement_inv_fst_of_not_mem {S : Finset ι} {i : ι} (hi : i ∉ S) :
    (((e.weylElement S)⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) (e.fst i) = e.fst i := by
  conv_lhs => rw [← e.weylElement_fst_of_not_mem hi]
  rw [isometryGroup_coe_inv_apply']

variable [NeZero (2 : D)]

/-- The isometry `h₀ = h₀ ⊕ ⋯ ⊕ h₄ : W_{S₀} ⊕ ⋯ ⊕ W_{S₄} → W₀ ⊕ ⋯ ⊕ W₄` of the proof of GKT
Theorem 4.31, for a five-term decomposition of `(X, X₂, X₃)` and a partition `σ` of the index set
with `|Sⱼ| = dim (X ∩ Wⱼ)`. -/
private theorem exists_isometryEquiv_fiveTerm {X₂ X₃ : Submodule D V}
    (F : h.FiveTermDecomposition e.lagrangianFst X₂ X₃) (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) {σ : ι → Fin 5}
    (hσ : ∀ j, (Finset.univ.filter fun i => σ i = j).card =
      finrank D (e.lagrangianFst ⊓ F.W j : Submodule D V)) :
    ∃ Φ : IsometryEquiv h h,
      (∀ j, (e.block {i | σ i = j}).map Φ.toLinearEquiv.toLinearMap = F.W j) ∧
      (∀ j, (e.blockFst {i | σ i = j}).map Φ.toLinearEquiv.toLinearMap =
        e.lagrangianFst ⊓ F.W j) ∧
      (e.blockSnd {i | σ i = 1}).map Φ.toLinearEquiv.toLinearMap = X₂ ⊓ F.W 1 ∧
      (e.blockSnd {i | σ i = 2}).map Φ.toLinearEquiv.toLinearMap = X₂ ⊓ F.W 2 ∧
      (e.blockSnd {i | σ i = 3}).map Φ.toLinearEquiv.toLinearMap = X₃ ⊓ F.W 3 ∧
      (e.blockSnd {i | σ i = 4}).map Φ.toLinearEquiv.toLinearMap = X₂ ⊓ F.W 4 := by
  have hX := e.isLagrangian_lagrangianFst
  have hD := F.isOrthogonalDecomposition
  have hS : ∀ j, ((Finset.univ.filter fun i => σ i = j : Finset ι) : Set ι) = {i | σ i = j} :=
    fun j => Finset.coe_filter_univ _
  have hd : ∀ j, finrank D (e.block {i | σ i = j}) = finrank D (F.W j) := by
    intro j
    rw [← hS, e.finrank_block, hσ, F.finrank_W_eq (F.isLagrangian_comap₁ hX j)]
  have hLX : ∀ j, (h.restrict (e.block {i | σ i = j})).IsLagrangian
      ((e.blockFst {i | σ i = j}).comap (e.block {i | σ i = j}).subtype) := by
    intro j; have := e.isLagrangian_blockFst (Finset.univ.filter fun i => σ i = j)
    rwa [hS] at this
  have hLY : ∀ j, (h.restrict (e.block {i | σ i = j})).IsLagrangian
      ((e.blockSnd {i | σ i = j}).comap (e.block {i | σ i = j}).subtype) := by
    intro j; have := e.isLagrangian_blockSnd (Finset.univ.filter fun i => σ i = j)
    rwa [hS] at this
  have hpol : ∀ j {A : Submodule D V}, h.IsLagrangian A → CommutesWith F.W A →
      Disjoint (e.lagrangianFst ⊓ F.W j) (A ⊓ F.W j) →
      ∃ φ : IsometryEquiv (h.restrict (e.block {i | σ i = j})) (h.restrict (F.W j)),
        ((e.blockFst {i | σ i = j}).comap (e.block {i | σ i = j}).subtype).map
            φ.toLinearEquiv.toLinearMap = e.lagrangianFst.comap (F.W j).subtype ∧
        ((e.blockSnd {i | σ i = j}).comap (e.block {i | σ i = j}).subtype).map
            φ.toLinearEquiv.toLinearMap = A.comap (F.W j).subtype := by
    intro j A hA hAc hdis
    exact exists_isometryEquiv_map_polarization (e.restrict_block_nondegenerate _)
      (hD.nondegenerate j) (hLX j) (hLY j) (e.disjoint_blockFst_blockSnd_comap _)
      (F.isLagrangian_comap₁ hX j) (hD.isLagrangian_comap hA hAc j) (disjoint_comap_subtype hdis)
      (hd j)
  let A : Fin 5 → Submodule D V := ![e.lagrangianFst, X₂, X₂, X₃, X₂]
  have key : ∀ j, ∃ φ : IsometryEquiv (h.restrict (e.block {i | σ i = j})) (h.restrict (F.W j)),
      ((e.blockFst {i | σ i = j}).comap (e.block {i | σ i = j}).subtype).map
          φ.toLinearEquiv.toLinearMap = e.lagrangianFst.comap (F.W j).subtype ∧
      (j ≠ 0 → ((e.blockSnd {i | σ i = j}).comap (e.block {i | σ i = j}).subtype).map
          φ.toLinearEquiv.toLinearMap = (A j).comap (F.W j).subtype) := by
    intro j
    rcases fin_five_cases j with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨φ, hφ⟩ := exists_isometryEquiv_map_isLagrangian (e.restrict_block_nondegenerate _)
        (hD.nondegenerate 0) (hLX 0) (F.isLagrangian_comap₁ hX 0) (hd 0)
      exact ⟨φ, hφ, fun h0 => absurd rfl h0⟩
    · obtain ⟨φ, h1, h2⟩ := hpol 1 h₂ F.commutes₂ F.disjoint₁
      exact ⟨φ, h1, fun _ => h2⟩
    · obtain ⟨φ, h1, h2⟩ := hpol 2 h₂ F.commutes₂ F.disjoint₂.symm
      exact ⟨φ, h1, fun _ => h2⟩
    · obtain ⟨φ, h1, h2⟩ := hpol 3 h₃ F.commutes₃ F.disjoint₃.symm
      exact ⟨φ, h1, fun _ => h2⟩
    · obtain ⟨φ, h1, h2⟩ := hpol 4 h₂ F.commutes₂ F.disjoint₄₁₂
      exact ⟨φ, h1, fun _ => h2⟩
  choose φ hφ₁ hφ₂ using key
  obtain ⟨Φ, hΦ⟩ := exists_isometryEquiv_of_decomposition (e.isOrthogonalDecomposition_block σ) hD φ
  have hΦ' : ∀ j (u : e.block {i | σ i = j}),
      Φ.toLinearEquiv.toLinearMap u = (φ j).toLinearEquiv.toLinearMap u := fun j u => hΦ j u
  have hsnd : ∀ j, j ≠ 0 → (e.blockSnd {i | σ i = j}).map Φ.toLinearEquiv.toLinearMap =
      A j ⊓ F.W j := fun j hj =>
    map_eq_inf_of_map_comap _ _ (hΦ' j) (e.blockSnd_le_block _) (hφ₂ j hj)
  refine ⟨Φ, fun j => ?_, fun j => map_eq_inf_of_map_comap _ _ (hΦ' j) (e.blockFst_le_block _)
    (hφ₁ j), hsnd 1 (by decide), hsnd 2 (by decide), hsnd 3 (by decide), hsnd 4 (by decide)⟩
  have := map_eq_inf_of_map_comap (B := e.block {i | σ i = j}) (A := ⊤) _ _ (hΦ' j) le_rfl (by
    rw [Submodule.comap_subtype_self, Submodule.map_top, LinearEquiv.range, Submodule.comap_top])
  rwa [top_inf_eq] at this

omit [NeZero (2 : D)] in
/-- The map `b` of GKT Theorem 4.31: given the isometry `Φ` carrying `W_{S₄}` onto `W₄` and `X_{S₄}`
onto `X ∩ W₄`, there is `b ∈ Herm(Y, X)` vanishing on `Y_{S₄ᶜ}`, with values in `X_{S₄}`, and with
`Φ (y + b y) ∈ X₃ ∩ W₄` for `y ∈ Y_{S₄}`; it is obtained from the Lagrangian
`Zh = Y_{S₄ᶜ} ⊕ Φ⁻¹ (X₃ ∩ W₄)`, a complement of `X`. -/
private theorem exists_siegelHerm_fiveTerm {X₂ X₃ : Submodule D V}
    (F : h.FiveTermDecomposition e.lagrangianFst X₂ X₃) (h₃ : h.IsLagrangian X₃) {σ : ι → Fin 5}
    (hσ : ∀ j, (Finset.univ.filter fun i => σ i = j).card =
      finrank D (e.lagrangianFst ⊓ F.W j : Submodule D V))
    (Φ : IsometryEquiv h h)
    (hW : (e.block {i | σ i = 4}).map Φ.toLinearEquiv.toLinearMap = F.W 4)
    (hF : (e.blockFst {i | σ i = 4}).map Φ.toLinearEquiv.toLinearMap = e.lagrangianFst ⊓ F.W 4) :
    ∃ b ∈ h.siegelHerm e.lagrangianFst e.lagrangianSnd,
      (∀ y : e.lagrangianSnd, (y : V) ∈ e.blockSnd {i | σ i ≠ 4} → b y = 0) ∧
      (∀ y : e.lagrangianSnd, (b y : V) ∈ e.blockFst {i | σ i = 4}) ∧
      (∀ y : e.lagrangianSnd, (y : V) ∈ e.blockSnd {i | σ i = 4} →
        Φ ((y : V) + b y) ∈ X₃ ⊓ F.W 4) := by
  have hh := e.nondegenerate
  have hX := e.isLagrangian_lagrangianFst
  have hY := e.isLagrangian_lagrangianSnd
  have hc : ({i | σ i = 4} : Set ι)ᶜ = {i | σ i ≠ 4} := by ext; simp
  have hBB : Disjoint (e.block {i | σ i = 4}) (e.block {i | σ i ≠ 4}) :=
    hc ▸ e.disjoint_block_compl _
  have hBo : e.block {i | σ i ≠ 4} ≤ h.orthogonal (e.block {i | σ i = 4}) :=
    e.block_le_orthogonal (by rw [Set.disjoint_left]; intro i hi hi'; exact hi hi')
  have hBo' : e.block {i | σ i = 4} ≤ h.orthogonal (e.block {i | σ i ≠ 4}) :=
    e.block_le_orthogonal (by rw [Set.disjoint_left]; intro i hi hi'; exact hi' hi)
  -- dimensions on `W₄`
  have hd₁ := F.finrank_W_eq (F.isLagrangian_comap₁ hX 4)
  have hd₃ := F.finrank_W_eq (F.isLagrangian_comap₃ h₃ 4)
  have hW₄ : e.lagrangianFst ⊓ F.W 4 ⊔ X₃ ⊓ F.W 4 = F.W 4 := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_right inf_le_right)
    have := Submodule.finrank_sup_add_finrank_inf_eq (e.lagrangianFst ⊓ F.W 4) (X₃ ⊓ F.W 4)
    rw [disjoint_iff.1 F.disjoint₄₁₃, finrank_bot] at this
    omega
  -- `Z = Φ⁻¹ (X₃ ∩ W₄)`
  set Z := (X₃ ⊓ F.W 4).comap Φ.toLinearEquiv.toLinearMap with hZdef
  have hZB : Z ≤ e.block {i | σ i = 4} := by
    intro z hz
    have : Φ.toLinearEquiv.toLinearMap z ∈ (e.block {i | σ i = 4}).map
        Φ.toLinearEquiv.toLinearMap := hW ▸ hz.2
    obtain ⟨u, hu, hzu⟩ := this
    rwa [Φ.toLinearEquiv.injective hzu] at hu
  have hBZ : e.block {i | σ i = 4} ≤ e.blockFst {i | σ i = 4} ⊔ Z := by
    intro u hu
    have : Φ.toLinearEquiv.toLinearMap u ∈ e.lagrangianFst ⊓ F.W 4 ⊔ X₃ ⊓ F.W 4 := by
      rw [hW₄, ← hW]; exact Submodule.mem_map_of_mem hu
    obtain ⟨a, ha, c, hc', hac⟩ := Submodule.mem_sup.1 this
    rw [← hF] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have huxZ : u - x ∈ Z := by
      change Φ.toLinearEquiv.toLinearMap (u - x) ∈ X₃ ⊓ F.W 4
      rw [map_sub, ← hac, add_sub_cancel_left]; exact hc'
    exact Submodule.mem_sup.2 ⟨x, hx, u - x, huxZ, add_sub_cancel _ _⟩
  have hdZ : finrank D Z = finrank D (X₃ ⊓ F.W 4 : Submodule D V) := by
    rw [hZdef, Submodule.comap_equiv_eq_map_symm]; exact LinearEquiv.finrank_map_eq _ _
  -- `Zh = Y_{S₄ᶜ} ⊕ Z`
  set Zh := e.blockSnd {i | σ i ≠ 4} ⊔ Z with hZhdef
  have hZho : Zh ≤ h.orthogonal Zh := by
    rw [orthogonal_sup]
    refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact fun v hv u hu => hY.apply_eq_zero (e.blockSnd_le_lagrangianSnd _ hv)
        (e.blockSnd_le_lagrangianSnd _ hu)
    · exact fun v hv u hu => hBo (e.blockSnd_le_block _ hv) u (hZB hu)
    · exact fun v hv u hu => hBo' (hZB hv) u (e.blockSnd_le_block _ hu)
    · intro v hv u hu
      rw [← Φ.map_app]; exact h₃.apply_eq_zero hv.1 hu.1
  have hZhd : finrank D Zh = Fintype.card ι := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (e.blockSnd {i | σ i ≠ 4}) Z
    have h3 : finrank D (e.blockSnd {i | σ i ≠ 4}) =
        (Finset.univ.filter fun i => σ i ≠ 4).card := by
      rw [← Finset.coe_filter_univ, e.finrank_blockSnd]
    rw [disjoint_iff.1 (hBB.symm.mono (e.blockSnd_le_block _) hZB), finrank_bot, add_zero,
      h3, hdZ] at h1
    have h2 : (Finset.univ.filter fun i => σ i ≠ 4).card +
        (Finset.univ.filter fun i => σ i = 4).card = Fintype.card ι := by
      rw [add_comm, Finset.card_univ.symm]; exact Finset.card_filter_add_card_filter_not _
    rw [hσ] at h2
    rw [hZhdef]; omega
  have hZhL : h.IsLagrangian Zh :=
    isLagrangian_of_two_mul_finrank hh (isTotallyIsotropic_iff_le_orthogonal.2 hZho)
      (by rw [hZhd, e.finrank_eq])
  have htop : Zh ⊔ e.lagrangianFst = ⊤ := by
    rw [eq_top_iff, ← e.block_sup_block_compl {i | σ i = 4}, hc]
    refine sup_le (hBZ.trans (sup_le (le_sup_of_le_right (e.blockFst_le_lagrangianFst _))
      (le_sup_of_le_left le_sup_right))) ?_
    exact sup_le (le_sup_of_le_right (e.blockFst_le_lagrangianFst _))
      (le_sup_of_le_left le_sup_left)
  have hZhX : IsCompl Zh e.lagrangianFst := by
    refine (hZhL.isCompl_iff_disjoint hh hX).2 ?_
    have : Zh ⊓ e.lagrangianFst = h.orthogonal (Zh ⊔ e.lagrangianFst) := by
      rw [orthogonal_sup, hZhL, hX]
    rw [disjoint_iff, this, htop, orthogonal_top hh]
  obtain ⟨b, hb, hbZ⟩ := exists_siegelHerm_add_mem hX hY hZhL hZhX
  have huniq : ∀ (y : e.lagrangianSnd) (x : V), x ∈ e.lagrangianFst → (y : V) + x ∈ Zh →
      (b y : V) = x := by
    intro y x hx hyx
    have h1 := Zh.sub_mem (hbZ y) hyx
    rw [add_sub_add_left_eq_sub] at h1
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hZhX.disjoint _ h1
      (e.lagrangianFst.sub_mem (b y).2 hx))
  have hb4 : ∀ y : e.lagrangianSnd, (b y : V) ∈ e.blockFst {i | σ i = 4} := by
    intro y
    have hy : (y : V) ∈ e.blockSnd {i | σ i = 4} ⊔ e.blockSnd {i | σ i ≠ 4} := by
      rw [← hc, e.blockSnd_sup_blockSnd_compl]; exact y.2
    obtain ⟨y₁, hy₁, y₂, hy₂, hy12⟩ := Submodule.mem_sup.1 hy
    obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.1 (hBZ (e.blockSnd_le_block _ hy₁))
    have := huniq y (-x) (e.lagrangianFst.neg_mem (e.blockFst_le_lagrangianFst _ hx)) (by
      rw [← hy12, ← hxz, show x + z + y₂ + -x = y₂ + z by abel]
      exact Submodule.add_mem_sup hy₂ hz)
    rw [this]; exact neg_mem hx
  refine ⟨b, hb, fun y hy => Subtype.ext ?_, hb4, fun y hy => ?_⟩
  · exact huniq y 0 (zero_mem _) (by rw [add_zero]; exact Submodule.mem_sup_left hy)
  · have hv : (y : V) + b y ∈ e.block {i | σ i = 4} :=
      add_mem (e.blockSnd_le_block _ hy) (e.blockFst_le_block _ (hb4 y))
    obtain ⟨y₂, hy₂, z, hz, hyz⟩ := Submodule.mem_sup.1 (hbZ y)
    have : y₂ = 0 := by
      have hy₂' : y₂ ∈ e.block {i | σ i = 4} := by
        rw [show y₂ = ((y : V) + b y) - z by rw [← hyz]; abel]
        exact sub_mem hv (hZB hz)
      exact Submodule.disjoint_def.1 hBB _ hy₂' (e.blockSnd_le_block _ hy₂)
    rw [← hyz, this, zero_add]
    exact hz

omit [NeZero (2 : D)] in
/-- The isometry of the form `(y, y') ↦ h (b y) y'` on `U = Y_{S₄}` with the Leray form of the
transverse triple `(X ∩ W₄, X₂ ∩ W₄, X₃ ∩ W₄)` of `W₄`, through `Φ`. -/
private theorem nonempty_isometryEquiv_siegelHermForm {X₂ X₃ : Submodule D V}
    (F : h.FiveTermDecomposition e.lagrangianFst X₂ X₃) (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) (Φ : IsometryEquiv h h) {b : e.lagrangianSnd →ₗ[D] e.lagrangianFst}
    (hb : b ∈ h.siegelHerm e.lagrangianFst e.lagrangianSnd) {U : Submodule D V}
    (hU : U ≤ e.lagrangianSnd) (hUW : U.map Φ.toLinearEquiv.toLinearMap = X₂ ⊓ F.W 4)
    (hΦX : ∀ x ∈ e.lagrangianFst, Φ x ∈ e.lagrangianFst)
    (hb₃ : ∀ y : U, Φ ((y : V) + b (Submodule.inclusion hU y)) ∈ X₃ ⊓ F.W 4) :
    Nonempty (IsometryEquiv (h.siegelHermForm hb U hU)
      ((h.restrict (F.W 4)).lerayForm (F.isTransverseTriple₄ e.isLagrangian_lagrangianFst h₂ h₃)
        (F.isOrthogonalDecomposition.nondegenerate 4))) := by
  have hmem : ∀ y : U, Φ y ∈ X₂ ⊓ F.W 4 := fun y => hUW ▸ Submodule.mem_map_of_mem y.2
  let f : U →ₗ[D] X₂.comap (F.W 4).subtype :=
    LinearMap.codRestrict _ (LinearMap.codRestrict (F.W 4)
      (Φ.toLinearEquiv.toLinearMap ∘ₗ U.subtype) (fun y => (hmem y).2)) (fun y => (hmem y).1)
  have hf : ∀ y : U, ((f y : F.W 4) : V) = Φ y := fun _ => rfl
  have hinj : Function.Injective f := by
    intro y y' hyy'
    apply Subtype.ext
    apply Φ.toLinearEquiv.injective
    have := congrArg (fun z : X₂.comap (F.W 4).subtype => ((z : F.W 4) : V)) hyy'
    simp only [hf] at this
    exact this
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨w, hwW⟩, hwX⟩
    have : w ∈ U.map Φ.toLinearEquiv.toLinearMap := hUW ▸ ⟨hwX, hwW⟩
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  refine ⟨{ toLinearEquiv := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, map_app' := fun y y' => ?_ }⟩
  change (h.restrict (F.W 4)).lerayForm _ _ (f y) (f y') = h.siegelHermForm hb U hU y y'
  rw [lerayForm_apply, restrict_apply, siegelHermForm_apply]
  have hp : lerayProj (F.isTransverseTriple₄ e.isLagrangian_lagrangianFst h₂ h₃)
      (F.isOrthogonalDecomposition.nondegenerate 4) (f y : F.W 4) =
        ⟨Φ ((y : V) + b (Submodule.inclusion hU y)), (hb₃ y).2⟩ := by
    apply lerayProj_eq_of
    · exact (hb₃ y).1
    · change Φ ((y : V) + b (Submodule.inclusion hU y)) - Φ y ∈ e.lagrangianFst
      rw [map_add, add_sub_cancel_left]; exact hΦX _ (b _).2
  rw [hp]
  change h (Φ ((y : V) + b (Submodule.inclusion hU y))) (Φ y') =
    h (b (Submodule.inclusion hU y) : V) y'
  rw [Φ.map_app, h.map_add_left, e.isLagrangian_lagrangianSnd.apply_eq_zero (hU y.2) (hU y'.2),
    zero_add]

/-- GKT Proposition 4.30 in coordinates (the core of Theorem 4.31): for Lagrangians `X₂, X₃` there
are a partition `σ` of the index set into `S₀, …, S₄`, a map `b ∈ Herm(Y, X)` vanishing on
`Y_{S₄ᶜ}` with values in `X_{S₄}`, and `p ∈ P(X)` with `p κ₁⁻¹ X = X₂` and `p κ₂ X = X₃`, where
`κ₁ = w_{S₁ ∪ S₂ ∪ S₄}` and `κ₂ = n(b) w_{S₁ ∪ S₃ ∪ S₄}`; the form `(y, y') ↦ h(b y, y')` on
`Y_{S₄}` is isometric to the Leray invariant `L(X, X₂, X₃)`. -/
theorem exists_mem_siegelParabolic_map_eq {X₂ X₃ : Submodule D V} (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) :
    ∃ σ : ι → Fin 5, ∃ b : e.lagrangianSnd →ₗ[D] e.lagrangianFst,
      ∃ hb : b ∈ h.siegelHerm e.lagrangianFst e.lagrangianSnd,
      (∀ y : e.lagrangianSnd, (y : V) ∈ e.blockSnd {i | σ i ≠ 4} → b y = 0) ∧
      (∀ y : e.lagrangianSnd, (b y : V) ∈ e.blockFst {i | σ i = 4}) ∧
      (∃ p ∈ h.siegelParabolic e.lagrangianFst,
        e.lagrangianFst.map ((p * (e.weylElement (Finset.univ.filter fun i =>
          σ i = 1 ∨ σ i = 2 ∨ σ i = 4))⁻¹ : h.isometryGroup) : V ≃ₗ[D] V).toLinearMap = X₂ ∧
        e.lagrangianFst.map ((p * (h.siegelUnipotentOf e.nondegenerate
          e.isLagrangian_lagrangianFst e.isCompl_lagrangianFst_lagrangianSnd b hb *
          e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 3 ∨ σ i = 4)) :
            h.isometryGroup) : V ≃ₗ[D] V).toLinearMap = X₃) ∧
      Nonempty (IsometryEquiv (h.lerayInvariant e.nondegenerate e.isLagrangian_lagrangianFst h₂ h₃)
        (h.siegelHermForm hb (e.blockSnd {i | σ i = 4}) (e.blockSnd_le_lagrangianSnd _))) := by
  have hh := e.nondegenerate
  have hX := e.isLagrangian_lagrangianFst
  obtain ⟨F⟩ := nonempty_fiveTermDecomposition hh hX h₂ h₃
  have hD := F.isOrthogonalDecomposition
  have hsum : ∑ j, finrank D (e.lagrangianFst ⊓ F.W j : Submodule D V) = Fintype.card ι := by
    have h1 : finrank D V = ∑ j, finrank D (F.W j) := by
      rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective (DirectSum.coeLinearMap F.W)
        hD.isInternal), Module.finrank_directSum]
    rw [e.finrank_eq, Finset.sum_congr rfl
      (fun j _ => F.finrank_W_eq (F.isLagrangian_comap₁ hX j)), ← Finset.mul_sum] at h1
    omega
  obtain ⟨σ, hσ⟩ := exists_fiber_card _ hsum
  obtain ⟨Φ, hW, hF, hY₁, hY₂, hY₃, hY₄⟩ := e.exists_isometryEquiv_fiveTerm F h₂ h₃ hσ
  obtain ⟨b, hb, hb0, hb4, hb₃⟩ := e.exists_siegelHerm_fiveTerm F h₃ hσ Φ (hW 4) (hF 4)
  have hmem : ∀ {v : V} {B A : Submodule D V}, v ∈ B →
      B.map Φ.toLinearEquiv.toLinearMap = A → Φ v ∈ A :=
    fun hv hB => hB ▸ Submodule.mem_map_of_mem hv
  have hfst : ∀ i, Φ (e.fst i) ∈ e.lagrangianFst ⊓ F.W (σ i) := fun i =>
    hmem (e.fst_mem_blockFst (show i ∈ {i' | σ i' = σ i} from rfl)) (hF (σ i))
  have hsndj : ∀ {i j}, σ i = j → e.snd i ∈ e.blockSnd {i' | σ i' = j} := fun hi =>
    e.snd_mem_blockSnd hi
  let g₀ : h.isometryGroup := ⟨Φ.toLinearEquiv, fun x y => Φ.map_app x y⟩
  have hP : e.lagrangianFst.map (g₀ : V ≃ₗ[D] V).toLinearMap = e.lagrangianFst :=
    e.map_lagrangianFst_eq g₀ hX fun i => (hfst i).1
  have hΦX : ∀ x ∈ e.lagrangianFst, Φ x ∈ e.lagrangianFst := fun x hx =>
    hP ▸ Submodule.mem_map_of_mem hx
  have hXY := e.isCompl_lagrangianFst_lagrangianSnd
  have hn : ∀ i, ((h.siegelUnipotentOf hh hX hXY b hb : h.isometryGroup) : V ≃ₗ[D] V)
      (e.snd i) = e.snd i + b ⟨e.snd i, e.snd_mem_lagrangianSnd i⟩ := fun i =>
    siegelUnipotentOf_apply_right hh hX hXY hb ⟨e.snd i, e.snd_mem_lagrangianSnd i⟩
  have hb0' : ∀ i, σ i ≠ 4 → b ⟨e.snd i, e.snd_mem_lagrangianSnd i⟩ = 0 := fun i hi =>
    hb0 _ (e.snd_mem_blockSnd hi)
  refine ⟨σ, b, hb, hb0, hb4, ⟨g₀, hP, ?_, ?_⟩, ?_⟩
  · refine e.map_lagrangianFst_eq _ h₂ fun i => ?_
    rw [isometryGroup_coe_mul_apply]
    rcases fin_five_cases (σ i) with hi | hi | hi | hi | hi
    · rw [e.weylElement_inv_fst_of_not_mem (by simp [hi])]
      have := hfst i; rw [hi, F.eq₀₁₂] at this; exact this.1
    · rw [e.weylElement_inv_fst_of_mem (by simp [hi])]; exact (hmem (hsndj hi) hY₁).1
    · rw [e.weylElement_inv_fst_of_mem (by simp [hi])]; exact (hmem (hsndj hi) hY₂).1
    · rw [e.weylElement_inv_fst_of_not_mem (by simp [hi])]
      have := hfst i; rw [hi, F.eq₃] at this; exact this.1
    · rw [e.weylElement_inv_fst_of_mem (by simp [hi])]; exact (hmem (hsndj hi) hY₄).1
  · refine e.map_lagrangianFst_eq _ h₃ fun i => ?_
    rw [isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply]
    rcases fin_five_cases (σ i) with hi | hi | hi | hi | hi
    · rw [e.weylElement_fst_of_not_mem (by simp [hi]), apply_eq_of_mem_siegelUnipotent hh hX
        (siegelUnipotentOf_mem hh hX hXY hb) (e.fst_mem_lagrangianFst i)]
      have := hfst i; rw [hi, F.eq₀₁₃] at this; exact this.1
    · rw [e.weylElement_fst_of_mem (by simp [hi]), map_smul, hn, hb0' i (by rw [hi]; decide),
        Submodule.coe_zero, add_zero, map_smul]
      have := hmem (hsndj hi) hY₁; rw [F.eq₁] at this; exact X₃.smul_mem _ this.1
    · rw [e.weylElement_fst_of_not_mem (by simp [hi]), apply_eq_of_mem_siegelUnipotent hh hX
        (siegelUnipotentOf_mem hh hX hXY hb) (e.fst_mem_lagrangianFst i)]
      have := hfst i; rw [hi, F.eq₂] at this; exact this.1
    · rw [e.weylElement_fst_of_mem (by simp [hi]), map_smul, hn, hb0' i (by rw [hi]; decide),
        Submodule.coe_zero, add_zero, map_smul]
      exact X₃.smul_mem _ (hmem (hsndj hi) hY₃).1
    · rw [e.weylElement_fst_of_mem (by simp [hi]), map_smul, hn, map_smul]
      exact X₃.smul_mem _ (hb₃ ⟨e.snd i, e.snd_mem_lagrangianSnd i⟩ (hsndj hi)).1
  · obtain ⟨L⟩ := F.nonempty_isometryEquiv_lerayInvariant hh hX h₂ h₃
    obtain ⟨ψ⟩ := e.nonempty_isometryEquiv_siegelHermForm F h₂ h₃ Φ hb
      (e.blockSnd_le_lagrangianSnd _) hY₄ hΦX
      (fun y => hb₃ (Submodule.inclusion (e.blockSnd_le_lagrangianSnd _) y) y.2)
    exact ⟨L.trans ψ.symm⟩

/-- GKT Theorem 4.31, the generalized Bruhat decomposition: for `g₁, g₂ ∈ G` there are a partition
`σ` of the index set into `S₀, …, S₄`, a map `b ∈ Herm(Y, X)` vanishing on `Y_{S₄ᶜ}` with values in
`X_{S₄}`, and `p₁, p, p₂ ∈ P` with `g₁ = p₁ κ₁ p⁻¹` and `g₂ = p κ₂ p₂⁻¹`, where
`κ₁ = w_{S₁ ∪ S₂ ∪ S₄}` and `κ₂ = n(b) w_{S₁ ∪ S₃ ∪ S₄}`; the form `(y, y') ↦ h(b y, y')` on
`Y_{S₄}` is non-degenerate and isometric to `L(X, g₁⁻¹ X, g₂ X)`. -/
theorem exists_generalizedBruhat (g₁ g₂ : h.isometryGroup) :
    ∃ σ : ι → Fin 5, ∃ b : e.lagrangianSnd →ₗ[D] e.lagrangianFst,
      ∃ hb : b ∈ h.siegelHerm e.lagrangianFst e.lagrangianSnd,
      (∀ y : e.lagrangianSnd, (y : V) ∈ e.blockSnd {i | σ i ≠ 4} → b y = 0) ∧
      (∀ y : e.lagrangianSnd, (b y : V) ∈ e.blockFst {i | σ i = 4}) ∧
      (∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p ∈ h.siegelParabolic e.lagrangianFst,
        ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
        g₁ = p₁ * e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 2 ∨ σ i = 4) * p⁻¹ ∧
        g₂ = p * (h.siegelUnipotentOf e.nondegenerate e.isLagrangian_lagrangianFst
          e.isCompl_lagrangianFst_lagrangianSnd b hb *
          e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 3 ∨ σ i = 4)) * p₂⁻¹) ∧
      (h.siegelHermForm hb (e.blockSnd {i | σ i = 4})
        (e.blockSnd_le_lagrangianSnd _)).Nondegenerate ∧
      Nonempty (IsometryEquiv (h.lerayInvariant e.nondegenerate e.isLagrangian_lagrangianFst
          (e.isLagrangian_lagrangianFst.map g₁⁻¹) (e.isLagrangian_lagrangianFst.map g₂))
        (h.siegelHermForm hb (e.blockSnd {i | σ i = 4}) (e.blockSnd_le_lagrangianSnd _))) := by
  obtain ⟨σ, b, hb, hb0, hb4, ⟨p, hp, hp₁, hp₂⟩, ⟨L⟩⟩ :=
    e.exists_mem_siegelParabolic_map_eq (e.isLagrangian_lagrangianFst.map g₁⁻¹)
      (e.isLagrangian_lagrangianFst.map g₂)
  refine ⟨σ, b, hb, hb0, hb4, ⟨g₁ * p * (e.weylElement (Finset.univ.filter fun i =>
    σ i = 1 ∨ σ i = 2 ∨ σ i = 4))⁻¹, ?_, p, hp, g₂⁻¹ * p * (h.siegelUnipotentOf e.nondegenerate
    e.isLagrangian_lagrangianFst e.isCompl_lagrangianFst_lagrangianSnd b hb *
    e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 3 ∨ σ i = 4)), ?_, by group,
    by group⟩, L.nondegenerate (lerayInvariant_nondegenerate _ _ _ _), ⟨L⟩⟩
  · rw [mem_siegelParabolic_iff, mul_assoc, map_isometryGroup_mul, hp₁, ← map_isometryGroup_mul,
      mul_inv_cancel]
    exact Submodule.map_id _
  · rw [mem_siegelParabolic_iff, mul_assoc, map_isometryGroup_mul, hp₂, ← map_isometryGroup_mul,
      inv_mul_cancel]
    exact Submodule.map_id _

end StandardBasis

variable [FiniteDimensional D V]

/-- Leray invariants of equal triples are isometric. -/
theorem nonempty_isometryEquiv_lerayInvariant_of_eq (hh : h.Nondegenerate)
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Submodule D V} (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) (k₁ : h.IsLagrangian Y₁) (k₂ : h.IsLagrangian Y₂)
    (k₃ : h.IsLagrangian Y₃) (e₁ : X₁ = Y₁) (e₂ : X₂ = Y₂) (e₃ : X₃ = Y₃) :
    Nonempty (IsometryEquiv (h.lerayInvariant hh h₁ h₂ h₃) (h.lerayInvariant hh k₁ k₂ k₃)) := by
  subst e₁ e₂ e₃; exact ⟨IsometryEquiv.refl _⟩

/-- GKT Theorem 4.31, last assertion: if `g₁ = p₁ κ₁ p⁻¹` and `g₂ = p κ₂ p₂⁻¹` with
`p₁, p, p₂ ∈ P(X)`, then `L(X, g₁⁻¹ X, g₂ X) = L(X, κ₁⁻¹ X, κ₂ X)`. -/
theorem nonempty_isometryEquiv_lerayInvariant_of_eq_mul (hh : h.Nondegenerate)
    {X : Submodule D V} (hX : h.IsLagrangian X) {g₁ g₂ κ₁ κ₂ p₁ p p₂ : h.isometryGroup}
    (hp₁ : p₁ ∈ h.siegelParabolic X) (hp : p ∈ h.siegelParabolic X)
    (hp₂ : p₂ ∈ h.siegelParabolic X) (hg₁ : g₁ = p₁ * κ₁ * p⁻¹) (hg₂ : g₂ = p * κ₂ * p₂⁻¹) :
    Nonempty (IsometryEquiv (h.lerayInvariant hh hX (hX.map g₁⁻¹) (hX.map g₂))
      (h.lerayInvariant hh hX (hX.map κ₁⁻¹) (hX.map κ₂))) := by
  have hP : ∀ q ∈ h.siegelParabolic X, X.map (q : V ≃ₗ[D] V).toLinearMap = X := fun q hq => hq
  obtain ⟨φ⟩ := nonempty_isometryEquiv_lerayInvariant_map_isometryGroup hh hX (hX.map g₁⁻¹)
    (hX.map g₂) p⁻¹
  obtain ⟨ψ⟩ := nonempty_isometryEquiv_lerayInvariant_of_eq hh (hX.map p⁻¹)
    ((hX.map g₁⁻¹).map p⁻¹) ((hX.map g₂).map p⁻¹) hX (hX.map κ₁⁻¹) (hX.map κ₂)
    (hP _ (inv_mem hp))
    (by rw [← map_isometryGroup_mul, show p⁻¹ * g₁⁻¹ = κ₁⁻¹ * p₁⁻¹ by rw [hg₁]; group,
      map_isometryGroup_mul, hP _ (inv_mem hp₁)])
    (by rw [← map_isometryGroup_mul, show p⁻¹ * g₂ = κ₂ * p₂⁻¹ by rw [hg₂]; group,
      map_isometryGroup_mul, hP _ (inv_mem hp₂)])
  exact ⟨φ.trans ψ⟩

end Generalized

end EpsilonHermitianForm

end Langlands

end
