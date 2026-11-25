import Langlands.LinearAlgebra.EpsilonHermitian.Decomposition

/-!
# Rao's five-term decomposition

GKT §4.3: Lemmas 4.19 and 4.21, Proposition 4.22 (Rao's five-term decomposition) with its
dimension formulas, Corollary 4.23, Lemma 4.24, Corollary 4.25, Proposition 4.26.

For a triple `(X₁, X₂, X₃)` of Lagrangians of a non-degenerate `ε`-Hermitian space `V` there is an
orthogonal decomposition `V = W₀ ⊕ W₁ ⊕ W₂ ⊕ W₃ ⊕ W₄` into non-degenerate subspaces with which
the three Lagrangians commute, such that on `W₀` the three agree, on `Wᵢ` (`i = 1, 2, 3`) `Xᵢ` is
transverse to the two others, which agree, and on `W₄` they are pairwise transverse. The Leray
invariant is computed on `W₄` (Corollary 4.23), and two triples are conjugate under the isometry
group if and only if they have the same intersection dimensions and isometric Leray invariants
(Corollary 4.25).
-/

noncomputable section

namespace Langlands

namespace EpsilonHermitianForm

open Module
open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε' : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V] {h : EpsilonHermitianForm τ ε' V}

/-! ### Preliminaries -/

section Preliminaries

/-- Inside a subspace `B`, the part `A ⊓ B` of `A` has a complement contained in `B`. -/
theorem exists_le_inf_eq_bot_sup_eq (A B : Submodule D V) :
    ∃ C ≤ B, C ⊓ (A ⊓ B) = ⊥ ∧ C ⊔ (A ⊓ B) = B := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl ((A ⊓ B).comap B.subtype)
  refine ⟨q.map B.subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨c, hc, rfl⟩, hcA⟩
    have : c ∈ (A ⊓ B).comap B.subtype ⊓ q := ⟨hcA, hc⟩
    rw [hq.inf_eq_bot] at this
    rw [(Submodule.mem_bot D).1 this]; exact (Submodule.mem_bot D).2 rfl
  · apply le_antisymm (sup_le (Submodule.map_subtype_le _ _) inf_le_right)
    intro b hb
    have : (⟨b, hb⟩ : B) ∈ (A ⊓ B).comap B.subtype ⊔ q := by rw [hq.sup_eq_top]; trivial
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 this
    have : b = (c : V) + (a : V) := by rw [← Submodule.coe_add, add_comm, hac]
    rw [this]
    exact Submodule.add_mem_sup ⟨c, hc, rfl⟩ ha

/-- An orthogonal sum of two non-degenerate subspaces is non-degenerate. -/
theorem restrict_sup_nondegenerate_of_orthogonal {A B : Submodule D V}
    (hAB : A ≤ h.orthogonal B) (hA : (h.restrict A).Nondegenerate)
    (hB : (h.restrict B).Nondegenerate) : (h.restrict (A ⊔ B)).Nondegenerate := by
  rw [restrict_nondegenerate_iff, eq_bot_iff]
  rintro v ⟨hv, hv'⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  have hBA : B ≤ h.orthogonal A := le_orthogonal_iff.1 hAB
  have ha0 : a = 0 := by
    have := hA ⟨a, ha⟩ fun y => by
      have e := hv' y (Submodule.mem_sup_left y.2)
      rwa [h.map_add_left, hBA hb y y.2, add_zero] at e
    exact congrArg Subtype.val this
  have hb0 : b = 0 := by
    have := hB ⟨b, hb⟩ fun y => by
      have e := hv' y (Submodule.mem_sup_right y.2)
      rwa [h.map_add_left, hAB ha y y.2, zero_add] at e
    exact congrArg Subtype.val this
  rw [ha0, hb0, add_zero]; exact (Submodule.mem_bot D).2 rfl

variable [FiniteDimensional D V]

/-- For a non-degenerate subspace `A` with orthogonal `B` and `N ≤ A`:
`N^⊥ = (N^⊥ ∩ A) ⊕ B`. -/
theorem orthogonal_eq_inf_sup (hh : h.Nondegenerate) {A N : Submodule D V}
    (hA : (h.restrict A).Nondegenerate) (hN : N ≤ A) :
    h.orthogonal N = h.orthogonal N ⊓ A ⊔ h.orthogonal A := by
  apply le_antisymm
  · intro v hv
    have hc := isCompl_orthogonal_of_restrict_nondegenerate hh hA
    have : v ∈ A ⊔ h.orthogonal A := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 this
    have haN : a ∈ h.orthogonal N := by
      intro n hn
      have e := hv n hn
      rwa [h.map_add_left, hb n (hN hn), add_zero] at e
    exact Submodule.add_mem_sup ⟨haN, ha⟩ hb
  · exact sup_le inf_le_left (orthogonal_le_orthogonal hN)

omit [FiniteDimensional D V] in
/-- For `V = M^⊥ ⊕ M*`: `M ∩ M*^⊥ = 0`. -/
theorem inf_orthogonal_eq_bot_of_isCompl (hh : h.Nondegenerate) {M M' : Submodule D V}
    (hc : IsCompl (h.orthogonal M) M') :
    M ⊓ h.orthogonal M' = ⊥ := by
  rw [eq_bot_iff]
  rintro m ⟨hm, hm'⟩
  refine (Submodule.mem_bot D).2 (hh m fun v => ?_)
  have : v ∈ h.orthogonal M ⊔ M' := by rw [hc.sup_eq_top]; trivial
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 this
  rw [h.map_add_right, (h.apply_eq_zero_comm).1 (hp m hm), hm' q hq, add_zero]

omit [FiniteDimensional D V] in
/-- For totally isotropic `M`, `M*` with `V = M^⊥ ⊕ M*`, `M` is a Lagrangian of `M ⊕ M*`:
`M^⊥ ∩ (M ⊕ M*) = M`. -/
theorem orthogonal_inf_sup_eq_left {M M' : Submodule D V} (hM : h.IsTotallyIsotropic M)
    (hc : IsCompl (h.orthogonal M) M') : h.orthogonal M ⊓ (M ⊔ M') = M := by
  rw [inf_comm, sup_inf_assoc_of_le M' (isTotallyIsotropic_iff_le_orthogonal.1 hM), inf_comm,
    hc.inf_eq_bot, sup_bot_eq]

omit [FiniteDimensional D V] in
theorem orthogonal_inf_sup_eq_right (hh : h.Nondegenerate) {M M' : Submodule D V}
    (hM' : h.IsTotallyIsotropic M')
    (hc : IsCompl (h.orthogonal M) M') : h.orthogonal M' ⊓ (M ⊔ M') = M' := by
  rw [sup_comm, inf_comm, sup_inf_assoc_of_le M (isTotallyIsotropic_iff_le_orthogonal.1 hM'),
    inf_orthogonal_eq_bot_of_isCompl hh hc, sup_bot_eq]

omit [FiniteDimensional D V] in
/-- GKT Lemma 4.20 for two pieces: if `V = A ⊕ B` orthogonally and the Lagrangian `X` commutes with
the decomposition, `X ∩ B` is a Lagrangian of `B`. -/
theorem isLagrangian_comap_of_le_orthogonal {A B X : Submodule D V} (hX : h.IsLagrangian X)
    (hAB : A ≤ h.orthogonal B) (hcomm : X ⊓ A ⊔ X ⊓ B = X) :
    (h.restrict B).IsLagrangian (X.comap B.subtype) := by
  rw [IsLagrangian, restrict_orthogonal_comap]
  ext w
  simp only [Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · intro hw
    rw [← hX, ← hcomm, orthogonal_sup]
    exact ⟨orthogonal_le_orthogonal inf_le_right (le_orthogonal_iff.1 hAB w.2), hw⟩
  · intro hw
    exact orthogonal_le_orthogonal inf_le_left (hX.symm.le hw)

/-- GKT Lemma 4.19: for totally isotropic `M₁`, `M₂` with `V = M₁^⊥ ⊕ M₂`, the sum `M₁ ⊕ M₂` is
direct, non-degenerate and split (with the Lagrangians `M₁`, `M₂`). -/
theorem isSplit_restrict_sup (hh : h.Nondegenerate) [NeZero (2 : D)] {M₁ M₂ : Submodule D V}
    (h₁ : h.IsTotallyIsotropic M₁) (h₂ : h.IsTotallyIsotropic M₂)
    (hc : IsCompl (h.orthogonal M₁) M₂) :
    Disjoint M₁ M₂ ∧ (h.restrict (M₁ ⊔ M₂)).Nondegenerate ∧ (h.restrict (M₁ ⊔ M₂)).IsSplit := by
  have hd : finrank D M₂ = finrank D M₁ := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    have := finrank_add_finrank_orthogonal hh M₁
    omega
  obtain ⟨e⟩ := exists_standardBasis_restrict_sup hh h₁ h₂ hc hd
  exact ⟨disjoint_of_isCompl_orthogonal h₁ hc, restrict_sup_nondegenerate hh h₁ hc,
    ⟨_, _, e.isLagrangian_lagrangianFst, e.isLagrangian_lagrangianSnd,
      e.isCompl_lagrangianFst_lagrangianSnd⟩⟩

end Preliminaries

/-! ### Lagrangians of a subspace -/

section Relative

/-- A subspace `X ≤ U` is a Lagrangian of `(U, h|_U)` iff `X^⊥ ∩ U = X`. -/
theorem isLagrangian_restrict_iff {U X : Submodule D V} (hXU : X ≤ U) :
    (h.restrict U).IsLagrangian (X.comap U.subtype) ↔ h.orthogonal X ⊓ U = X := by
  rw [IsLagrangian, restrict_orthogonal_comap, inf_eq_left.2 hXU]
  constructor
  · intro H
    have := congrArg (Submodule.map U.subtype) H
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hXU,
      inf_comm] at this
  · intro H
    conv_rhs => rw [← H]
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]

/-- GKT Lemma 4.20 inside a subspace: if `X` is a Lagrangian of `U`, `B ≤ U`, `A ⊥ B` and `X`
commutes with `A`, `B`, then `X ∩ B` is a Lagrangian of `B`. -/
theorem orthogonal_inf_inf_eq {U A B X : Submodule D V} (hXU : h.orthogonal X ⊓ U = X)
    (hBU : B ≤ U) (hAB : A ≤ h.orthogonal B) (hcomm : X ⊓ A ⊔ X ⊓ B = X) :
    h.orthogonal (X ⊓ B) ⊓ B = X ⊓ B := by
  apply le_antisymm
  · rintro w ⟨hw, hwB⟩
    refine ⟨?_, hwB⟩
    rw [← hXU]
    refine ⟨?_, hBU hwB⟩
    rw [← hcomm, orthogonal_sup]
    exact ⟨orthogonal_le_orthogonal inf_le_right (le_orthogonal_iff.1 hAB hwB), hw⟩
  · exact le_inf ((inf_le_left.trans (hXU.symm.le.trans inf_le_left)).trans
      (orthogonal_le_orthogonal inf_le_left)) inf_le_right

end Relative

/-! ### Splittings (GKT Lemma 4.21) -/

variable (h) in
/-- `(A, B)` splits the triple inside `U`: `U = A ⊕ B` orthogonally with `A`, `B` non-degenerate,
the three subspaces commute with the decomposition, `X₁ = X₂` on `A` and `X₁`, `X₂` are transverse
on `B` (GKT Lemma 4.21). -/
structure IsSplitting (U A B X₁ X₂ X₃ : Submodule D V) : Prop where
  sup_eq : A ⊔ B = U
  le_orthogonal : A ≤ h.orthogonal B
  nondegenerate_left : (h.restrict A).Nondegenerate
  nondegenerate_right : (h.restrict B).Nondegenerate
  commutes₁ : X₁ ⊓ A ⊔ X₁ ⊓ B = X₁
  commutes₂ : X₂ ⊓ A ⊔ X₂ ⊓ B = X₂
  commutes₃ : X₃ ⊓ A ⊔ X₃ ⊓ B = X₃
  inf_left : X₁ ⊓ A = X₂ ⊓ A
  disjoint_right : Disjoint (X₁ ⊓ B) (X₂ ⊓ B)

namespace IsSplitting

variable {U A B X₁ X₂ X₃ : Submodule D V}

theorem disjoint (hS : h.IsSplitting U A B X₁ X₂ X₃) : Disjoint A B := by
  rw [Submodule.disjoint_def]
  intro v hvA hvB
  exact congrArg Subtype.val (hS.nondegenerate_right ⟨v, hvB⟩ fun y => hS.le_orthogonal hvA y y.2)

theorem le_left (hS : h.IsSplitting U A B X₁ X₂ X₃) : A ≤ U := hS.sup_eq ▸ le_sup_left

theorem le_right (hS : h.IsSplitting U A B X₁ X₂ X₃) : B ≤ U := hS.sup_eq ▸ le_sup_right

/-- Transport of a splitting along the inclusion of a subspace `U`. -/
theorem map_subtype {A' B' : Submodule D U}
    (hS : (h.restrict U).IsSplitting ⊤ A' B' (X₁.comap U.subtype) (X₂.comap U.subtype)
      (X₃.comap U.subtype)) (h₁ : X₁ ≤ U) (h₂ : X₂ ≤ U) (h₃ : X₃ ≤ U) :
    h.IsSplitting U (A'.map U.subtype) (B'.map U.subtype) X₁ X₂ X₃ := by
  have hinj := Submodule.injective_subtype U
  have hmapX : ∀ {X : Submodule D V}, X ≤ U → (X.comap U.subtype).map U.subtype = X := fun hX => by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hX]
  have hcomm : ∀ {X : Submodule D V}, X ≤ U →
      X.comap U.subtype ⊓ A' ⊔ X.comap U.subtype ⊓ B' = X.comap U.subtype →
      X ⊓ A'.map U.subtype ⊔ X ⊓ B'.map U.subtype = X := fun hX hc => by
    have := congrArg (Submodule.map U.subtype) hc
    rwa [Submodule.map_sup, Submodule.map_inf _ hinj, Submodule.map_inf _ hinj, hmapX hX] at this
  refine ⟨?_, ?_, ?_, ?_, hcomm h₁ hS.commutes₁, hcomm h₂ hS.commutes₂, hcomm h₃ hS.commutes₃,
    ?_, ?_⟩
  · rw [← Submodule.map_sup, hS.sup_eq, Submodule.map_subtype_top]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hS.le_orthogonal ha b hb
  · exact (restrict_restrict_nondegenerate_iff U A').1 hS.nondegenerate_left
  · exact (restrict_restrict_nondegenerate_iff U B').1 hS.nondegenerate_right
  · have := congrArg (Submodule.map U.subtype) hS.inf_left
    rwa [Submodule.map_inf _ hinj, Submodule.map_inf _ hinj, hmapX h₁, hmapX h₂] at this
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨hxX₁, b, hb, rfl⟩ := hx1
    obtain ⟨hxX₂, -⟩ := hx2
    have := Submodule.disjoint_def.1 hS.disjoint_right b ⟨hxX₁, hb⟩ ⟨hxX₂, hb⟩
    rw [this]; rfl

end IsSplitting

section Splitting

variable [FiniteDimensional D V] [NeZero (2 : D)]

omit [NeZero (2 : D)] in
/-- GKT Lemma 4.21 when `X₁ ∩ X₂ ∩ X₃ = 0`. -/
private theorem exists_isSplitting_of_inf_eq_bot (hh : h.Nondegenerate) {X₁ X₂ X₃ : Submodule D V}
    (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂) (h₃ : h.IsLagrangian X₃)
    (h₀ : X₁ ⊓ X₂ ⊓ X₃ = ⊥) : ∃ A B, h.IsSplitting ⊤ A B X₁ X₂ X₃ := by
  set M := X₁ ⊓ X₂
  have hM : h.IsTotallyIsotropic M := h₁.isTotallyIsotropic.mono inf_le_left
  -- `M^⊥ + X₃ = V`
  have htop : h.orthogonal M ⊔ X₃ = ⊤ := by
    rw [sup_comm, h₃.sup_eq_orthogonal_inf hh, orthogonal_orthogonal hh, inf_comm,
      show M ⊓ X₃ = ⊥ from h₀, orthogonal_bot]
  obtain ⟨M', hM'X₃, hM'0, hM'sup⟩ := exists_le_inf_eq_bot_sup_eq (h.orthogonal M) X₃
  have hc : IsCompl (h.orthogonal M) M' := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro v ⟨hv, hv'⟩
      have : v ∈ M' ⊓ (h.orthogonal M ⊓ X₃) := ⟨hv', hv, hM'X₃ hv'⟩
      rwa [hM'0] at this
    · rw [codisjoint_iff, eq_top_iff, ← htop, ← hM'sup]
      exact sup_le le_sup_left (sup_le le_sup_right (inf_le_left.trans le_sup_left))
  have hM'iso : h.IsTotallyIsotropic M' := h₃.isTotallyIsotropic.mono hM'X₃
  set A := M ⊔ M'
  have hA : (h.restrict A).Nondegenerate := restrict_sup_nondegenerate hh hM hc
  set B := h.orthogonal A
  have hAB := isCompl_orthogonal_of_restrict_nondegenerate hh hA
  have hB : (h.restrict B).Nondegenerate := restrict_orthogonal_nondegenerate hh hA
  have hMA : h.orthogonal M ⊓ A = M := orthogonal_inf_sup_eq_left hM hc
  have hM'A : h.orthogonal M' ⊓ A = M' := orthogonal_inf_sup_eq_right hh hM'iso hc
  have hMperp : h.orthogonal M = M ⊔ B := by
    rw [orthogonal_eq_inf_sup hh hA le_sup_left, hMA]
  have hM'perp : h.orthogonal M' = M' ⊔ B := by
    rw [orthogonal_eq_inf_sup hh hA le_sup_right, hM'A]
  -- `Xᵢ ∩ A` for `i = 1, 2`
  have hXA : ∀ {X : Submodule D V}, h.IsLagrangian X → M ≤ X → X ⊓ A = M := by
    intro X hX hMX
    exact le_antisymm (by
      rw [← hMA]
      exact inf_le_inf_right _ (hX.symm.le.trans (orthogonal_le_orthogonal hMX)))
      (le_inf hMX le_sup_left)
  -- commuting, from `X ⊆ N^⊥ = N ⊕ B` with `N ≤ X ⊓ A`
  have hcomm : ∀ {X N : Submodule D V}, h.IsLagrangian X → N ≤ X → N ≤ A →
      h.orthogonal N = N ⊔ B → X ⊓ A ⊔ X ⊓ B = X := by
    intro X N hX hNX hNA hNperp
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    have : x ∈ h.orthogonal N := hX.symm.le.trans (orthogonal_le_orthogonal hNX) hx
    rw [hNperp] at this
    obtain ⟨n, hn, b, hb, rfl⟩ := Submodule.mem_sup.1 this
    have hbX : b ∈ X := by
      have := X.sub_mem hx (hNX hn); rwa [add_sub_cancel_left] at this
    exact Submodule.add_mem_sup ⟨hNX hn, hNA hn⟩ ⟨hbX, hb⟩
  refine ⟨A, B, ?_, ?_, hA, hB, hcomm h₁ inf_le_left le_sup_left hMperp,
    hcomm h₂ inf_le_right le_sup_left hMperp, hcomm h₃ hM'X₃ le_sup_right hM'perp, ?_, ?_⟩
  · exact hAB.sup_eq_top
  · exact le_orthogonal_iff.1 le_rfl
  · rw [hXA h₁ inf_le_left, hXA h₂ inf_le_right]
  · rw [Submodule.disjoint_def]
    rintro v ⟨hv₁, hvB⟩ ⟨hv₂, -⟩
    have hvA : v ∈ A := Submodule.mem_sup_left (show v ∈ M from ⟨hv₁, hv₂⟩)
    exact Submodule.disjoint_def.1 hAB.disjoint v hvA hvB

/-- GKT Lemma 4.21: for a triple of Lagrangians there is an orthogonal decomposition `V = A ⊕ B`
into non-degenerate subspaces with which the three commute, with `X₁ = X₂` on `A` and `X₁`, `X₂`
transverse on `B`. -/
theorem exists_isSplitting (hh : h.Nondegenerate) {X₁ X₂ X₃ : Submodule D V}
    (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂) (h₃ : h.IsLagrangian X₃) :
    ∃ A B, h.IsSplitting ⊤ A B X₁ X₂ X₃ := by
  set M₀ := X₁ ⊓ X₂ ⊓ X₃
  have hM₀ : h.IsTotallyIsotropic M₀ := h₁.isTotallyIsotropic.mono (inf_le_left.trans inf_le_left)
  obtain ⟨M₀', hM₀'iso, -, hc⟩ := exists_isTotallyIsotropic_isCompl hh hM₀
  set V₁ := M₀ ⊔ M₀'
  have hV₁ : (h.restrict V₁).Nondegenerate := restrict_sup_nondegenerate hh hM₀ hc
  set V₂ := h.orthogonal V₁
  have hV₁₂ := isCompl_orthogonal_of_restrict_nondegenerate hh hV₁
  have hV₂ : (h.restrict V₂).Nondegenerate := restrict_orthogonal_nondegenerate hh hV₁
  have hM₀V₁ : h.orthogonal M₀ ⊓ V₁ = M₀ := orthogonal_inf_sup_eq_left hM₀ hc
  have hM₀perp : h.orthogonal M₀ = M₀ ⊔ V₂ := by
    rw [orthogonal_eq_inf_sup hh hV₁ le_sup_left, hM₀V₁]
  have hM₀X₁ : M₀ ≤ X₁ := inf_le_left.trans inf_le_left
  have hM₀X₂ : M₀ ≤ X₂ := inf_le_left.trans inf_le_right
  have hM₀X₃ : M₀ ≤ X₃ := inf_le_right
  -- each `Xᵢ` is `M₀ ⊕ (Xᵢ ∩ V₂)`
  have hXdec : ∀ {X : Submodule D V}, h.IsLagrangian X → M₀ ≤ X → M₀ ⊔ X ⊓ V₂ = X := by
      intro X hX hMX
      apply le_antisymm (sup_le hMX inf_le_left)
      intro x hx
      have : x ∈ h.orthogonal M₀ := hX.symm.le.trans (orthogonal_le_orthogonal hMX) hx
      rw [hM₀perp] at this
      obtain ⟨m, hm, v, hv, rfl⟩ := Submodule.mem_sup.1 this
      have hvX : v ∈ X := by
        have := X.sub_mem hx (hMX hm); rwa [add_sub_cancel_left] at this
      exact Submodule.add_mem_sup hm ⟨hvX, hv⟩
  have hXV₁ : ∀ {X : Submodule D V}, h.IsLagrangian X → M₀ ≤ X → X ⊓ V₁ = M₀ := by
    intro X hX hMX
    exact le_antisymm (by
      rw [← hM₀V₁]
      exact inf_le_inf_right _ (hX.symm.le.trans (orthogonal_le_orthogonal hMX)))
      (le_inf hMX le_sup_left)
  -- the triple restricted to `V₂`
  have hcomV : ∀ {X : Submodule D V}, h.IsLagrangian X → M₀ ≤ X →
      X ⊓ V₁ ⊔ X ⊓ V₂ = X := by
    intro X hX hMX; rw [hXV₁ hX hMX]; exact hXdec hX hMX
  have hLag : ∀ {X : Submodule D V}, h.IsLagrangian X → M₀ ≤ X →
      (h.restrict V₂).IsLagrangian (X.comap V₂.subtype) := by
    intro X hX hMX
    exact isLagrangian_comap_of_le_orthogonal hX (le_orthogonal_iff.1 le_rfl) (hcomV hX hMX)
  have hY₀ : X₁.comap V₂.subtype ⊓ X₂.comap V₂.subtype ⊓ X₃.comap V₂.subtype = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨hv₁, hv₂⟩, hv₃⟩
    have hvM : (v : V) ∈ M₀ := ⟨⟨hv₁, hv₂⟩, hv₃⟩
    have := Submodule.disjoint_def.1 hV₁₂.disjoint _ (Submodule.mem_sup_left hvM) v.2
    exact (Submodule.mem_bot D).2 (Subtype.ext this)
  obtain ⟨A', B', hS'⟩ := exists_isSplitting_of_inf_eq_bot (h := h.restrict V₂)
    (restrict_orthogonal_nondegenerate hh hV₁) (hLag h₁ hM₀X₁) (hLag h₂ hM₀X₂)
    (hLag h₃ hM₀X₃) hY₀
  have hcomapinf : ∀ X : Submodule D V, (X ⊓ V₂).comap V₂.subtype = X.comap V₂.subtype :=
    fun X => by ext v; simp
  have hS := IsSplitting.map_subtype (U := V₂) (X₁ := X₁ ⊓ V₂) (X₂ := X₂ ⊓ V₂) (X₃ := X₃ ⊓ V₂)
    (by rwa [hcomapinf, hcomapinf, hcomapinf]) inf_le_right inf_le_right inf_le_right
  set Z₁ := A'.map V₂.subtype
  set Z₂ := B'.map V₂.subtype
  have hZ₁V₂ : Z₁ ≤ V₂ := hS.le_left
  have hZ₂V₂ : Z₂ ≤ V₂ := hS.le_right
  have hV₁Z : V₁ ≤ h.orthogonal (Z₁ ⊔ Z₂) := by
    rw [hS.sup_eq]; exact le_orthogonal_iff.1 le_rfl
  set A := V₁ ⊔ Z₁
  have hAZ₂ : A ≤ h.orthogonal Z₂ :=
    sup_le (hV₁Z.trans (orthogonal_le_orthogonal le_sup_right)) hS.le_orthogonal
  have hA : (h.restrict A).Nondegenerate :=
    restrict_sup_nondegenerate_of_orthogonal (hV₁Z.trans (orthogonal_le_orthogonal le_sup_left))
      hV₁ hS.nondegenerate_left
  have hAZ₂d : Disjoint A Z₂ := by
    rw [Submodule.disjoint_def]
    intro v hvA hvZ
    exact congrArg Subtype.val (hS.nondegenerate_right ⟨v, hvZ⟩ fun y => hAZ₂ hvA y y.2)
  -- `X ∩ (V₁ ⊕ Z₁) = (X ∩ V₁) ⊕ (X ∩ Z₁)` for the three subspaces
  have hXA : ∀ {X : Submodule D V}, h.IsLagrangian X → M₀ ≤ X →
      X ⊓ V₂ ⊓ Z₁ ⊔ X ⊓ V₂ ⊓ Z₂ = X ⊓ V₂ → X ⊓ A = M₀ ⊔ X ⊓ Z₁ := by
    intro X hX hMX hcX
    apply le_antisymm
    · intro x ⟨hx, hxA⟩
      rw [← hXdec hX hMX, ← hcX] at hx
      obtain ⟨m, hm, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
      have hy₂A : y₂ ∈ A := by
        have := A.sub_mem hxA (A.add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left hm))
          (Submodule.mem_sup_right hy₁.2))
        rwa [show m + (y₁ + y₂) - (m + y₁) = y₂ by abel] at this
      rw [Submodule.disjoint_def.1 hAZ₂d _ hy₂A hy₂.2, add_zero]
      exact Submodule.add_mem_sup hm ⟨hy₁.1.1, hy₁.2⟩
    · exact sup_le (le_inf hMX (le_sup_left.trans le_sup_left))
        (inf_le_inf_left _ le_sup_right)
  have hXfull : ∀ {X : Submodule D V}, h.IsLagrangian X → M₀ ≤ X →
      X ⊓ V₂ ⊓ Z₁ ⊔ X ⊓ V₂ ⊓ Z₂ = X ⊓ V₂ → M₀ ⊔ (X ⊓ Z₁ ⊔ X ⊓ Z₂) = X := by
    intro X hX hMX hcX
    rw [inf_assoc, inf_assoc, inf_eq_right.2 hZ₁V₂, inf_eq_right.2 hZ₂V₂] at hcX
    rw [hcX]; exact hXdec hX hMX
  have hcommF : ∀ {X : Submodule D V}, h.IsLagrangian X → M₀ ≤ X →
      X ⊓ V₂ ⊓ Z₁ ⊔ X ⊓ V₂ ⊓ Z₂ = X ⊓ V₂ → X ⊓ A ⊔ X ⊓ Z₂ = X := by
    intro X hX hMX hcX
    rw [hXA hX hMX hcX, sup_assoc]; exact hXfull hX hMX hcX
  refine ⟨A, Z₂, ?_, hAZ₂, hA, hS.nondegenerate_right, hcommF h₁ hM₀X₁ hS.commutes₁,
    hcommF h₂ hM₀X₂ hS.commutes₂, hcommF h₃ hM₀X₃ hS.commutes₃, ?_, ?_⟩
  · rw [sup_assoc, hS.sup_eq, hV₁₂.sup_eq_top]
  · rw [hXA h₁ hM₀X₁ hS.commutes₁, hXA h₂ hM₀X₂ hS.commutes₂]
    have := hS.inf_left
    rw [inf_assoc, inf_assoc, inf_eq_right.2 hZ₁V₂] at this
    rw [this]
  · have := hS.disjoint_right
    rwa [inf_assoc, inf_assoc, inf_eq_right.2 hZ₂V₂] at this

/-- GKT Lemma 4.21 inside a non-degenerate subspace `U`, for three Lagrangians of `U`. -/
theorem exists_isSplitting_of_le {U : Submodule D V} (hU : (h.restrict U).Nondegenerate)
    {X₁ X₂ X₃ : Submodule D V} (h₁U : X₁ ≤ U) (h₂U : X₂ ≤ U) (h₃U : X₃ ≤ U)
    (h₁ : (h.restrict U).IsLagrangian (X₁.comap U.subtype))
    (h₂ : (h.restrict U).IsLagrangian (X₂.comap U.subtype))
    (h₃ : (h.restrict U).IsLagrangian (X₃.comap U.subtype)) :
    ∃ A B, h.IsSplitting U A B X₁ X₂ X₃ := by
  obtain ⟨A', B', hS⟩ := exists_isSplitting (h := h.restrict U) hU h₁ h₂ h₃
  exact ⟨_, _, hS.map_subtype h₁U h₂U h₃U⟩

end Splitting

/-! ### Rao's five-term decomposition (GKT Proposition 4.22) -/

variable (h) in
/-- A five-term decomposition of a triple of Lagrangians (GKT Proposition 4.22): an orthogonal
decomposition `V = W₀ ⊕ W₁ ⊕ W₂ ⊕ W₃ ⊕ W₄` into non-degenerate subspaces with which `X₁, X₂, X₃`
commute, such that (0) the three agree on `W₀`; (1) `X₁` is transverse to `X₂ = X₃` on `W₁`;
(2) `X₂` is transverse to `X₁ = X₃` on `W₂`; (3) `X₃` is transverse to `X₁ = X₂` on `W₃`;
(4) the three are pairwise transverse on `W₄`. -/
structure FiveTermDecomposition (X₁ X₂ X₃ : Submodule D V) where
  /-- The five pieces. -/
  W : Fin 5 → Submodule D V
  isOrthogonalDecomposition : h.IsOrthogonalDecomposition W
  commutes₁ : CommutesWith W X₁
  commutes₂ : CommutesWith W X₂
  commutes₃ : CommutesWith W X₃
  eq₀₁₂ : X₁ ⊓ W 0 = X₂ ⊓ W 0
  eq₀₁₃ : X₁ ⊓ W 0 = X₃ ⊓ W 0
  disjoint₁ : Disjoint (X₁ ⊓ W 1) (X₂ ⊓ W 1)
  eq₁ : X₂ ⊓ W 1 = X₃ ⊓ W 1
  disjoint₂ : Disjoint (X₂ ⊓ W 2) (X₁ ⊓ W 2)
  eq₂ : X₁ ⊓ W 2 = X₃ ⊓ W 2
  disjoint₃ : Disjoint (X₃ ⊓ W 3) (X₁ ⊓ W 3)
  eq₃ : X₁ ⊓ W 3 = X₂ ⊓ W 3
  disjoint₄₁₂ : Disjoint (X₁ ⊓ W 4) (X₂ ⊓ W 4)
  disjoint₄₂₃ : Disjoint (X₂ ⊓ W 4) (X₃ ⊓ W 4)
  disjoint₄₁₃ : Disjoint (X₁ ⊓ W 4) (X₃ ⊓ W 4)

section Existence

variable [FiniteDimensional D V] [NeZero (2 : D)]

omit [FiniteDimensional D V] [NeZero (2 : D)] in
private theorem inf_inf_of_le {X U W : Submodule D V} (hW : W ≤ U) : X ⊓ U ⊓ W = X ⊓ W := by
  rw [inf_assoc, inf_eq_right.2 hW]

/-- GKT Proposition 4.22: every triple of Lagrangians has a five-term decomposition. -/
theorem nonempty_fiveTermDecomposition (hh : h.Nondegenerate) {X₁ X₂ X₃ : Submodule D V}
    (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂) (h₃ : h.IsLagrangian X₃) :
    Nonempty (h.FiveTermDecomposition X₁ X₂ X₃) := by
  -- step 1: `V = V₁ ⊕ V₂`, `X₁ = X₂` on `V₁`, transverse on `V₂`
  obtain ⟨V₁, V₂, S₁⟩ := exists_isSplitting hh h₁ h₂ h₃
  have hLag : ∀ {X : Submodule D V}, h.IsLagrangian X → h.orthogonal X ⊓ ⊤ = X := by
    intro X hX; rw [inf_top_eq, hX]
  have hV₂₁ : V₂ ≤ h.orthogonal V₁ := le_orthogonal_iff.1 S₁.le_orthogonal
  have hcomm₁' : ∀ {X : Submodule D V}, X ⊓ V₁ ⊔ X ⊓ V₂ = X → X ⊓ V₂ ⊔ X ⊓ V₁ = X := by
    intro X hX; rw [sup_comm]; exact hX
  -- Lagrangians of `V₁` and `V₂`
  have hL₁ : ∀ {X : Submodule D V}, h.IsLagrangian X → X ⊓ V₁ ⊔ X ⊓ V₂ = X →
      h.orthogonal (X ⊓ V₁) ⊓ V₁ = X ⊓ V₁ := by
    intro X hX hc; exact orthogonal_inf_inf_eq (hLag hX) le_top hV₂₁ (hcomm₁' hc)
  have hL₂ : ∀ {X : Submodule D V}, h.IsLagrangian X → X ⊓ V₁ ⊔ X ⊓ V₂ = X →
      h.orthogonal (X ⊓ V₂) ⊓ V₂ = X ⊓ V₂ := by
    intro X hX hc; exact orthogonal_inf_inf_eq (hLag hX) le_top S₁.le_orthogonal hc
  have hsub : ∀ {U X : Submodule D V}, h.orthogonal (X ⊓ U) ⊓ U = X ⊓ U →
      (h.restrict U).IsLagrangian ((X ⊓ U).comap U.subtype) := by
    intro U X hX; exact (isLagrangian_restrict_iff inf_le_right).2 hX
  -- step 2: `V₁ = W₀ ⊕ W₃`, `X₁ = X₃` on `W₀`, transverse on `W₃`
  obtain ⟨W₀, W₃, S₂⟩ := exists_isSplitting_of_le S₁.nondegenerate_left inf_le_right inf_le_right
    inf_le_right (hsub (hL₁ h₁ S₁.commutes₁)) (hsub (hL₁ h₃ S₁.commutes₃))
    (hsub (hL₁ h₂ S₁.commutes₂))
  -- step 3: `V₂ = W₂ ⊕ V₃`, `X₁ = X₃` on `W₂`, transverse on `V₃`
  obtain ⟨W₂, V₃, S₃⟩ := exists_isSplitting_of_le S₁.nondegenerate_right inf_le_right
    inf_le_right inf_le_right (hsub (hL₂ h₁ S₁.commutes₁)) (hsub (hL₂ h₃ S₁.commutes₃))
    (hsub (hL₂ h₂ S₁.commutes₂))
  -- step 4: `V₃ = W₁ ⊕ W₄`, `X₂ = X₃` on `W₁`, transverse on `W₄`
  have hV₃V₂ : V₃ ≤ V₂ := S₃.le_right
  have hL₃ : ∀ {X : Submodule D V}, h.IsLagrangian X → X ⊓ V₁ ⊔ X ⊓ V₂ = X →
      X ⊓ V₂ ⊓ W₂ ⊔ X ⊓ V₂ ⊓ V₃ = X ⊓ V₂ → h.orthogonal (X ⊓ V₃) ⊓ V₃ = X ⊓ V₃ := by
    intro X hX hc hc'
    have := orthogonal_inf_inf_eq (hL₂ hX hc) hV₃V₂ S₃.le_orthogonal hc'
    rwa [inf_inf_of_le hV₃V₂] at this
  obtain ⟨W₁, W₄, S₄⟩ := exists_isSplitting_of_le S₃.nondegenerate_right inf_le_right
    inf_le_right inf_le_right (hsub (hL₃ h₂ S₁.commutes₂ S₃.commutes₃))
    (hsub (hL₃ h₃ S₁.commutes₃ S₃.commutes₂)) (hsub (hL₃ h₁ S₁.commutes₁ S₃.commutes₁))
  -- the pieces and their positions
  have hW₀ : W₀ ≤ V₁ := S₂.le_left
  have hW₃ : W₃ ≤ V₁ := S₂.le_right
  have hW₂ : W₂ ≤ V₂ := S₃.le_left
  have hW₁ : W₁ ≤ V₂ := S₄.le_left.trans hV₃V₂
  have hW₄ : W₄ ≤ V₂ := S₄.le_right.trans hV₃V₂
  have hW₁₃ : W₁ ≤ V₃ := S₄.le_left
  have hW₄₃ : W₄ ≤ V₃ := S₄.le_right
  have o₁₂ : ∀ {A B : Submodule D V}, A ≤ V₁ → B ≤ V₂ → A ≤ h.orthogonal B := by
    intro A B hA hB
    exact hA.trans (S₁.le_orthogonal.trans (orthogonal_le_orthogonal hB))
  have o23 : ∀ {B : Submodule D V}, B ≤ V₃ → W₂ ≤ h.orthogonal B := by
    intro B hB; exact S₃.le_orthogonal.trans (orthogonal_le_orthogonal hB)
  set W : Fin 5 → Submodule D V := ![W₀, W₁, W₂, W₃, W₄]
  have hortho : ∀ i j, i ≠ j → W i ≤ h.orthogonal (W j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [W, ne_eq, not_true_eq_false] at hij ⊢
    · exact o₁₂ hW₀ hW₁
    · exact o₁₂ hW₀ hW₂
    · exact S₂.le_orthogonal
    · exact o₁₂ hW₀ hW₄
    · exact le_orthogonal_iff.1 (o₁₂ hW₀ hW₁)
    · exact le_orthogonal_iff.1 (o23 hW₁₃)
    · exact le_orthogonal_iff.1 (o₁₂ hW₃ hW₁)
    · exact S₄.le_orthogonal
    · exact le_orthogonal_iff.1 (o₁₂ hW₀ hW₂)
    · exact o23 hW₁₃
    · exact le_orthogonal_iff.1 (o₁₂ hW₃ hW₂)
    · exact o23 hW₄₃
    · exact le_orthogonal_iff.1 S₂.le_orthogonal
    · exact o₁₂ hW₃ hW₁
    · exact o₁₂ hW₃ hW₂
    · exact o₁₂ hW₃ hW₄
    · exact le_orthogonal_iff.1 (o₁₂ hW₀ hW₄)
    · exact le_orthogonal_iff.1 S₄.le_orthogonal
    · exact le_orthogonal_iff.1 (o23 hW₄₃)
    · exact le_orthogonal_iff.1 (o₁₂ hW₃ hW₄)
  have hsup : ⨆ i, W i = ⊤ := by
    rw [eq_top_iff, ← S₁.sup_eq, ← S₂.sup_eq, ← S₃.sup_eq, ← S₄.sup_eq]
    exact sup_le (sup_le (le_iSup W 0) (le_iSup W 3))
      (sup_le (le_iSup W 2) (sup_le (le_iSup W 1) (le_iSup W 4)))
  have hnd : ∀ i, (h.restrict (W i)).Nondegenerate := by
    intro i
    fin_cases i
    · exact S₂.nondegenerate_left
    · exact S₄.nondegenerate_left
    · exact S₃.nondegenerate_left
    · exact S₂.nondegenerate_right
    · exact S₄.nondegenerate_right
  -- commuting
  have hcommW : ∀ {X : Submodule D V}, X ⊓ V₁ ⊔ X ⊓ V₂ = X →
      X ⊓ V₁ ⊓ W₀ ⊔ X ⊓ V₁ ⊓ W₃ = X ⊓ V₁ → X ⊓ V₂ ⊓ W₂ ⊔ X ⊓ V₂ ⊓ V₃ = X ⊓ V₂ →
      X ⊓ V₃ ⊓ W₁ ⊔ X ⊓ V₃ ⊓ W₄ = X ⊓ V₃ → CommutesWith W X := by
    intro X c₁ c₂ c₃ c₄
    rw [inf_inf_of_le hW₀, inf_inf_of_le hW₃] at c₂
    rw [inf_inf_of_le hW₂, inf_inf_of_le hV₃V₂] at c₃
    rw [inf_inf_of_le hW₁₃, inf_inf_of_le hW₄₃] at c₄
    apply le_antisymm (iSup_le fun i => inf_le_left)
    have e : X = X ⊓ W₀ ⊔ X ⊓ W₃ ⊔ (X ⊓ W₂ ⊔ (X ⊓ W₁ ⊔ X ⊓ W₄)) := by rw [c₄, c₃, c₂, c₁]
    refine e.le.trans ?_
    exact sup_le (sup_le (le_iSup (fun i => X ⊓ W i) 0) (le_iSup (fun i => X ⊓ W i) 3))
      (sup_le (le_iSup (fun i => X ⊓ W i) 2)
        (sup_le (le_iSup (fun i => X ⊓ W i) 1) (le_iSup (fun i => X ⊓ W i) 4)))
  refine ⟨⟨W, ⟨hortho, hsup, hnd⟩, hcommW S₁.commutes₁ S₂.commutes₁ S₃.commutes₁ S₄.commutes₃,
    hcommW S₁.commutes₂ S₂.commutes₃ S₃.commutes₃ S₄.commutes₁,
    hcommW S₁.commutes₃ S₂.commutes₂ S₃.commutes₂ S₄.commutes₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · -- `X₁ = X₂` on `W₀`
    change X₁ ⊓ W₀ = X₂ ⊓ W₀
    rw [← inf_inf_of_le hW₀, S₁.inf_left, inf_inf_of_le hW₀]
  · change X₁ ⊓ W₀ = X₃ ⊓ W₀
    have := S₂.inf_left
    rwa [inf_inf_of_le hW₀, inf_inf_of_le hW₀] at this
  · change Disjoint (X₁ ⊓ W₁) (X₂ ⊓ W₁)
    exact S₁.disjoint_right.mono (inf_le_inf_left _ hW₁) (inf_le_inf_left _ hW₁)
  · change X₂ ⊓ W₁ = X₃ ⊓ W₁
    have := S₄.inf_left
    rwa [inf_inf_of_le hW₁₃, inf_inf_of_le hW₁₃] at this
  · change Disjoint (X₂ ⊓ W₂) (X₁ ⊓ W₂)
    exact S₁.disjoint_right.symm.mono (inf_le_inf_left _ hW₂) (inf_le_inf_left _ hW₂)
  · change X₁ ⊓ W₂ = X₃ ⊓ W₂
    have := S₃.inf_left
    rwa [inf_inf_of_le hW₂, inf_inf_of_le hW₂] at this
  · change Disjoint (X₃ ⊓ W₃) (X₁ ⊓ W₃)
    have := S₂.disjoint_right
    rw [inf_inf_of_le hW₃, inf_inf_of_le hW₃] at this
    exact this.symm
  · change X₁ ⊓ W₃ = X₂ ⊓ W₃
    rw [← inf_inf_of_le hW₃, S₁.inf_left, inf_inf_of_le hW₃]
  · change Disjoint (X₁ ⊓ W₄) (X₂ ⊓ W₄)
    exact S₁.disjoint_right.mono (inf_le_inf_left _ hW₄) (inf_le_inf_left _ hW₄)
  · change Disjoint (X₂ ⊓ W₄) (X₃ ⊓ W₄)
    have := S₄.disjoint_right
    rwa [inf_inf_of_le hW₄₃, inf_inf_of_le hW₄₃] at this
  · change Disjoint (X₁ ⊓ W₄) (X₃ ⊓ W₄)
    have := S₃.disjoint_right
    rw [inf_inf_of_le hV₃V₂, inf_inf_of_le hV₃V₂] at this
    exact this.mono (inf_le_inf_left _ hW₄₃) (inf_le_inf_left _ hW₄₃)

end Existence

/-! ### The dimension formulas of Proposition 4.22 -/

theorem finrank_comap_subtype (A B : Submodule D V) :
    finrank D (A.comap B.subtype) = finrank D (A ⊓ B : Submodule D V) := by
  have e : A.comap B.subtype = (A ⊓ B).comap B.subtype := by ext v; simp
  rw [e]
  exact (Submodule.comapSubtypeEquivOfLe (inf_le_right : A ⊓ B ≤ B)).finrank_eq

theorem IsOrthogonalDecomposition.disjoint {ι : Type*} {W : ι → Submodule D V}
    (hW : h.IsOrthogonalDecomposition W) {i j : ι} (hij : i ≠ j) : Disjoint (W i) (W j) := by
  rw [Submodule.disjoint_def]
  intro v hvi hvj
  exact congrArg Subtype.val ((hW.nondegenerate j) ⟨v, hvj⟩ fun y =>
    (h.apply_eq_zero_comm).1 (hW.orthogonal j i (Ne.symm hij) y.2 v hvi))

namespace FiveTermDecomposition

variable {X₁ X₂ X₃ : Submodule D V} (F : h.FiveTermDecomposition X₁ X₂ X₃)

/-- The pieces `Xᵢ ∩ W_j` are Lagrangians of `W_j` (GKT Lemma 4.20). -/
theorem isLagrangian_comap₁ (h₁ : h.IsLagrangian X₁) (j : Fin 5) :
    (h.restrict (F.W j)).IsLagrangian (X₁.comap (F.W j).subtype) :=
  F.isOrthogonalDecomposition.isLagrangian_comap h₁ F.commutes₁ j

theorem isLagrangian_comap₂ (h₂ : h.IsLagrangian X₂) (j : Fin 5) :
    (h.restrict (F.W j)).IsLagrangian (X₂.comap (F.W j).subtype) :=
  F.isOrthogonalDecomposition.isLagrangian_comap h₂ F.commutes₂ j

theorem isLagrangian_comap₃ (h₃ : h.IsLagrangian X₃) (j : Fin 5) :
    (h.restrict (F.W j)).IsLagrangian (X₃.comap (F.W j).subtype) :=
  F.isOrthogonalDecomposition.isLagrangian_comap h₃ F.commutes₃ j

variable [FiniteDimensional D V]

theorem finrank_W_eq {X : Submodule D V} (hX : (h.restrict (F.W j)).IsLagrangian
    (X.comap (F.W j).subtype)) : finrank D (F.W j) = 2 * finrank D (X ⊓ F.W j : Submodule D V) := by
  rw [← finrank_comap_subtype, (hX.two_mul_finrank (F.isOrthogonalDecomposition.nondegenerate j))]

omit [FiniteDimensional D V] in
/-- A component of a vector of `X ∩ Y` on a piece where `X`, `Y` are transverse vanishes. -/
private theorem component_eq_zero {X Y : Submodule D V} (hX : CommutesWith F.W X)
    (hY : CommutesWith F.W Y) {j : Fin 5} (hd : Disjoint (X ⊓ F.W j) (Y ⊓ F.W j)) {v : V}
    (hvX : v ∈ X) (hvY : v ∈ Y) : F.isOrthogonalDecomposition.component j v = 0 :=
  Submodule.disjoint_def.1 hd _ (F.isOrthogonalDecomposition.component_mem_inf hX j hvX)
    (F.isOrthogonalDecomposition.component_mem_inf hY j hvY)

omit [FiniteDimensional D V] in
private theorem component_mem {X : Submodule D V} (hX : CommutesWith F.W X) {j : Fin 5} {v : V}
    (hvX : v ∈ X) : F.isOrthogonalDecomposition.component j v ∈ X ⊓ F.W j :=
  F.isOrthogonalDecomposition.component_mem_inf hX j hvX

omit [FiniteDimensional D V] in
private theorem sum_five (v : V) : v = F.isOrthogonalDecomposition.component 0 v +
    F.isOrthogonalDecomposition.component 1 v + F.isOrthogonalDecomposition.component 2 v +
    F.isOrthogonalDecomposition.component 3 v + F.isOrthogonalDecomposition.component 4 v := by
  conv_lhs => rw [← F.isOrthogonalDecomposition.sum_component v]
  rw [Fin.sum_univ_five]

omit [FiniteDimensional D V] in
/-- `X₁ ∩ X₂ ∩ X₃ = X₁ ∩ W₀`. -/
theorem inf_inf_eq : X₁ ⊓ X₂ ⊓ X₃ = X₁ ⊓ F.W 0 := by
  apply le_antisymm
  · rintro v ⟨⟨h1, h2⟩, h3⟩
    have e1 := F.component_eq_zero F.commutes₁ F.commutes₂ F.disjoint₁ h1 h2
    have e2 := F.component_eq_zero F.commutes₂ F.commutes₁ F.disjoint₂ h2 h1
    have e3 := F.component_eq_zero F.commutes₃ F.commutes₁ F.disjoint₃ h3 h1
    have e4 := F.component_eq_zero F.commutes₁ F.commutes₂ F.disjoint₄₁₂ h1 h2
    rw [F.sum_five v]
    simp only [e1, e2, e3, e4, add_zero]
    exact F.component_mem F.commutes₁ h1
  · refine le_inf (le_inf inf_le_left ?_) ?_
    · rw [F.eq₀₁₂]; exact inf_le_left
    · rw [F.eq₀₁₃]; exact inf_le_left

omit [FiniteDimensional D V] in
theorem inf₂₃_eq : X₂ ⊓ X₃ = X₁ ⊓ F.W 0 ⊔ X₂ ⊓ F.W 1 := by
  apply le_antisymm
  · rintro v ⟨h2, h3⟩
    have e2 : F.isOrthogonalDecomposition.component 2 v = 0 :=
      F.component_eq_zero F.commutes₂ F.commutes₃ (by rw [← F.eq₂]; exact F.disjoint₂) h2 h3
    have e3 : F.isOrthogonalDecomposition.component 3 v = 0 :=
      F.component_eq_zero F.commutes₃ F.commutes₂ (by rw [← F.eq₃]; exact F.disjoint₃) h3 h2
    have e4 := F.component_eq_zero F.commutes₂ F.commutes₃ F.disjoint₄₂₃ h2 h3
    rw [F.sum_five v]
    simp only [e2, e3, e4, add_zero]
    refine Submodule.add_mem_sup ?_ (F.component_mem F.commutes₂ h2)
    rw [F.eq₀₁₂]; exact F.component_mem F.commutes₂ h2
  · refine sup_le (le_inf ?_ ?_) (le_inf inf_le_left ?_)
    · rw [F.eq₀₁₂]; exact inf_le_left
    · rw [F.eq₀₁₃]; exact inf_le_left
    · rw [F.eq₁]; exact inf_le_left

omit [FiniteDimensional D V] in
theorem inf₁₃_eq : X₁ ⊓ X₃ = X₁ ⊓ F.W 0 ⊔ X₁ ⊓ F.W 2 := by
  apply le_antisymm
  · rintro v ⟨h1, h3⟩
    have e1 : F.isOrthogonalDecomposition.component 1 v = 0 :=
      F.component_eq_zero F.commutes₁ F.commutes₃ (by rw [← F.eq₁]; exact F.disjoint₁) h1 h3
    have e3 := F.component_eq_zero F.commutes₃ F.commutes₁ F.disjoint₃ h3 h1
    have e4 := F.component_eq_zero F.commutes₁ F.commutes₃ F.disjoint₄₁₃ h1 h3
    rw [F.sum_five v]
    simp only [e1, e3, e4, add_zero]
    exact Submodule.add_mem_sup (F.component_mem F.commutes₁ h1) (F.component_mem F.commutes₁ h1)
  · refine sup_le (le_inf inf_le_left ?_) (le_inf inf_le_left ?_)
    · rw [F.eq₀₁₃]; exact inf_le_left
    · rw [F.eq₂]; exact inf_le_left

omit [FiniteDimensional D V] in
theorem inf₁₂_eq : X₁ ⊓ X₂ = X₁ ⊓ F.W 0 ⊔ X₁ ⊓ F.W 3 := by
  apply le_antisymm
  · rintro v ⟨h1, h2⟩
    have e1 := F.component_eq_zero F.commutes₁ F.commutes₂ F.disjoint₁ h1 h2
    have e2 := F.component_eq_zero F.commutes₂ F.commutes₁ F.disjoint₂ h2 h1
    have e4 := F.component_eq_zero F.commutes₁ F.commutes₂ F.disjoint₄₁₂ h1 h2
    rw [F.sum_five v]
    simp only [e1, e2, e4, add_zero]
    exact Submodule.add_mem_sup (F.component_mem F.commutes₁ h1) (F.component_mem F.commutes₁ h1)
  · refine sup_le (le_inf inf_le_left ?_) (le_inf inf_le_left ?_)
    · rw [F.eq₀₁₂]; exact inf_le_left
    · rw [F.eq₃]; exact inf_le_left

private theorem finrank_sup_of_pieces {A B : Submodule D V} {j k : Fin 5} (hjk : j ≠ k)
    (hA : A ≤ F.W j) (hB : B ≤ F.W k) : finrank D (A ⊔ B : Submodule D V) =
      finrank D A + finrank D B := by
  have hd : A ⊓ B = ⊥ :=
    disjoint_iff.1 ((F.isOrthogonalDecomposition.disjoint hjk).mono hA hB)
  have := Submodule.finrank_sup_add_finrank_inf_eq A B
  rwa [hd, finrank_bot, add_zero] at this

/-- The dimension formulas of GKT Proposition 4.22. -/
theorem finrank_W₀ (h₁ : h.IsLagrangian X₁) :
    finrank D (F.W 0) = 2 * finrank D (X₁ ⊓ X₂ ⊓ X₃ : Submodule D V) := by
  have e := congrArg (fun U : Submodule D V => finrank D U) F.inf_inf_eq
  rw [e]; exact F.finrank_W_eq (F.isLagrangian_comap₁ h₁ 0)

theorem finrank_W₁ (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂) :
    finrank D (F.W 1) + finrank D (F.W 0) = 2 * finrank D (X₂ ⊓ X₃ : Submodule D V) := by
  have e := congrArg (fun U : Submodule D V => finrank D U) F.inf₂₃_eq
  have e' := F.finrank_sup_of_pieces (j := 0) (k := 1) (by decide) (inf_le_right : X₁ ⊓ F.W 0 ≤ _)
    (inf_le_right : X₂ ⊓ F.W 1 ≤ _)
  have a := F.finrank_W_eq (F.isLagrangian_comap₂ h₂ 1)
  have b := F.finrank_W_eq (F.isLagrangian_comap₁ h₁ 0)
  omega

theorem finrank_W₂ (h₁ : h.IsLagrangian X₁) :
    finrank D (F.W 2) + finrank D (F.W 0) = 2 * finrank D (X₁ ⊓ X₃ : Submodule D V) := by
  have e := congrArg (fun U : Submodule D V => finrank D U) F.inf₁₃_eq
  have e' := F.finrank_sup_of_pieces (j := 0) (k := 2) (by decide) (inf_le_right : X₁ ⊓ F.W 0 ≤ _)
    (inf_le_right : X₁ ⊓ F.W 2 ≤ _)
  have a := F.finrank_W_eq (F.isLagrangian_comap₁ h₁ 2)
  have b := F.finrank_W_eq (F.isLagrangian_comap₁ h₁ 0)
  omega

theorem finrank_W₃ (h₁ : h.IsLagrangian X₁) :
    finrank D (F.W 3) + finrank D (F.W 0) = 2 * finrank D (X₁ ⊓ X₂ : Submodule D V) := by
  have e := congrArg (fun U : Submodule D V => finrank D U) F.inf₁₂_eq
  have e' := F.finrank_sup_of_pieces (j := 0) (k := 3) (by decide) (inf_le_right : X₁ ⊓ F.W 0 ≤ _)
    (inf_le_right : X₁ ⊓ F.W 3 ≤ _)
  have a := F.finrank_W_eq (F.isLagrangian_comap₁ h₁ 3)
  have b := F.finrank_W_eq (F.isLagrangian_comap₁ h₁ 0)
  omega

omit [FiniteDimensional D V] in
/-- `M(X₁, X₂, X₃)` is the sum of the common Lagrangians of the first four pieces. -/
theorem lerayM_eq : lerayM X₁ X₂ X₃ =
    X₁ ⊓ F.W 0 ⊔ X₂ ⊓ F.W 1 ⊔ X₁ ⊓ F.W 2 ⊔ X₁ ⊓ F.W 3 := by
  rw [lerayM, F.inf₁₂_eq, F.inf₂₃_eq, inf_comm X₃, F.inf₁₃_eq]
  set L₀ := X₁ ⊓ F.W 0
  set L₁ := X₂ ⊓ F.W 1
  set L₂ := X₁ ⊓ F.W 2
  set L₃ := X₁ ⊓ F.W 3
  have h₀ : L₀ ≤ L₀ ⊔ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have h₁ : L₁ ≤ L₀ ⊔ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have h₂ : L₂ ≤ L₀ ⊔ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have h₃ : L₃ ≤ L₀ ⊔ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have g₀ : L₀ ≤ L₀ ⊔ L₃ ⊔ (L₀ ⊔ L₁) ⊔ (L₀ ⊔ L₂) :=
    le_sup_left.trans (le_sup_left.trans le_sup_left)
  have g₁ : L₁ ≤ L₀ ⊔ L₃ ⊔ (L₀ ⊔ L₁) ⊔ (L₀ ⊔ L₂) :=
    le_sup_right.trans (le_sup_right.trans le_sup_left)
  have g₂ : L₂ ≤ L₀ ⊔ L₃ ⊔ (L₀ ⊔ L₁) ⊔ (L₀ ⊔ L₂) := le_sup_right.trans le_sup_right
  have g₃ : L₃ ≤ L₀ ⊔ L₃ ⊔ (L₀ ⊔ L₁) ⊔ (L₀ ⊔ L₂) :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  exact le_antisymm (sup_le (sup_le (sup_le h₀ h₃) (sup_le h₀ h₁)) (sup_le h₀ h₂))
    (sup_le (sup_le (sup_le g₀ g₁) g₂) g₃)

end FiveTermDecomposition

/-! ### The Leray invariant is computed on `W₄` (GKT Corollary 4.23) -/

section LerayOnW₄

variable {ε : ℤˣ} {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional D V]
  {X₁ X₂ X₃ : Submodule D V}

namespace FiveTermDecomposition

variable (F : h.FiveTermDecomposition X₁ X₂ X₃)

omit [FiniteDimensional D V] in
/-- The three Lagrangians meet `W₄` in a transverse triple of Lagrangians of `W₄`. -/
theorem isTransverseTriple₄ (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) : (h.restrict (F.W 4)).IsTransverseTriple (X₁.comap (F.W 4).subtype)
      (X₂.comap (F.W 4).subtype) (X₃.comap (F.W 4).subtype) := by
  have hd : ∀ {A B : Submodule D V}, Disjoint (A ⊓ F.W 4) (B ⊓ F.W 4) →
      Disjoint (A.comap (F.W 4).subtype) (B.comap (F.W 4).subtype) := by
    intro A B hAB
    rw [Submodule.disjoint_def]
    intro w hwA hwB
    exact Subtype.ext (Submodule.disjoint_def.1 hAB _ ⟨hwA, w.2⟩ ⟨hwB, w.2⟩)
  exact ⟨F.isLagrangian_comap₁ h₁ 4, F.isLagrangian_comap₂ h₂ 4, F.isLagrangian_comap₃ h₃ 4,
    hd F.disjoint₄₁₂, hd F.disjoint₄₂₃, hd F.disjoint₄₁₃⟩

omit [FiniteDimensional D V] in
private theorem component_mem_lagrangian {X : Submodule D V} (hX : h.IsLagrangian X)
    (hXc : CommutesWith F.W X) {j : Fin 5} {x : V}
    (hx : ∀ l ∈ X ⊓ F.W j, h x l = 0) :
    F.isOrthogonalDecomposition.component j x ∈ X ⊓ F.W j := by
  have hL := (isLagrangian_restrict_iff (U := F.W j) (X := X ⊓ F.W j) inf_le_right).1 (by
    have := F.isOrthogonalDecomposition.isLagrangian_comap hX hXc j
    have e : (X ⊓ F.W j).comap (F.W j).subtype = X.comap (F.W j).subtype := by ext v; simp
    rwa [e])
  rw [← hL]
  refine ⟨fun l hl => ?_, F.isOrthogonalDecomposition.component_mem j x⟩
  have e := F.isOrthogonalDecomposition.apply_eq_sum_component x l
  rw [Finset.sum_eq_single j] at e
  · rw [F.isOrthogonalDecomposition.component_of_mem hl.2, ite_eq_left rfl] at e
    rw [← e]; exact hx l hl
  · intro k _ hkj
    rw [F.isOrthogonalDecomposition.component_of_mem hl.2, ite_eq_right hkj, map_zero_right]
  · intro hj; exact absurd (Finset.mem_univ j) hj

omit [FiniteDimensional D V] in
/-- `W₄ ⊆ M^⊥`. -/
theorem W₄_le_orthogonal_lerayM : F.W 4 ≤ h.orthogonal (lerayM X₁ X₂ X₃) := by
  rw [le_orthogonal_iff, F.lerayM_eq]
  have ho : ∀ j : Fin 5, j ≠ 4 → F.W j ≤ h.orthogonal (F.W 4) :=
    fun j hj => F.isOrthogonalDecomposition.orthogonal j 4 hj
  exact sup_le (sup_le (sup_le (inf_le_right.trans (ho 0 (by decide)))
    (inf_le_right.trans (ho 1 (by decide)))) (inf_le_right.trans (ho 2 (by decide))))
    (inf_le_right.trans (ho 3 (by decide)))

omit [FiniteDimensional D V] in
/-- A vector of `M^⊥` is congruent modulo `M` to its component in `W₄`. -/
private theorem sub_component_mem_lerayM (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂)
    {x : V} (hx : x ∈ h.orthogonal (lerayM X₁ X₂ X₃)) :
    x - F.isOrthogonalDecomposition.component 4 x ∈ lerayM X₁ X₂ X₃ := by
  have hxl : ∀ l ∈ lerayM X₁ X₂ X₃, h x l = 0 := hx
  rw [F.lerayM_eq] at hxl ⊢
  have c₀ := F.component_mem_lagrangian h₁ F.commutes₁ (j := 0) fun l hl =>
    hxl l (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hl)))
  have c₁ := F.component_mem_lagrangian h₂ F.commutes₂ (j := 1) fun l hl =>
    hxl l (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right hl)))
  have c₂ := F.component_mem_lagrangian h₁ F.commutes₁ (j := 2) fun l hl =>
    hxl l (Submodule.mem_sup_left (Submodule.mem_sup_right hl))
  have c₃ := F.component_mem_lagrangian h₁ F.commutes₁ (j := 3) fun l hl =>
    hxl l (Submodule.mem_sup_right hl)
  have e := F.sum_five x
  rw [show x - F.isOrthogonalDecomposition.component 4 x =
      F.isOrthogonalDecomposition.component 0 x + F.isOrthogonalDecomposition.component 1 x +
      F.isOrthogonalDecomposition.component 2 x + F.isOrthogonalDecomposition.component 3 x by
    rw [sub_eq_iff_eq_add]; exact e]
  exact Submodule.add_mem_sup (Submodule.add_mem_sup (Submodule.add_mem_sup c₀ c₁) c₂) c₃

/-- The isometry `W₄ ≅ M^⊥/M` of GKT Corollary 4.23, `w ↦ w + M`. -/
def isometryEquivReduction (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂) :
    IsometryEquiv (h.restrict (F.W 4)) (h.reduction (lerayM X₁ X₂ X₃)) :=
  let φ : F.W 4 →ₗ[D] h.ReductionSpace (lerayM X₁ X₂ X₃) :=
    (h.reductionMap _).comp (Submodule.inclusion F.W₄_le_orthogonal_lerayM)
  have hφ : ∀ x y, h.reduction _ (φ x) (φ y) = h.restrict (F.W 4) x y := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    exact (Submodule.mem_bot D).2 ((F.isOrthogonalDecomposition.nondegenerate 4) w fun y => by
      rw [← hφ, hw, map_zero_left])
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨x, rfl⟩ := h.reductionMap_surjective _ a
    refine ⟨⟨_, F.isOrthogonalDecomposition.component_mem 4 x⟩, ?_⟩
    change h.reductionMap _ ⟨_, _⟩ = h.reductionMap _ x
    rw [← sub_eq_zero, ← map_sub, reductionMap_eq_zero_iff]
    have := (lerayM X₁ X₂ X₃).neg_mem (F.sub_component_mem_lerayM h₁ h₂ x.2)
    simpa using this
  { toLinearEquiv := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
    map_app' := hφ }

omit [FiniteDimensional D V] in
theorem map_isometryEquivReduction (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂)
    {X : Submodule D V} (hXc : CommutesWith F.W X) :
    (X.comap (F.W 4).subtype).map (F.isometryEquivReduction h₁ h₂).toLinearEquiv.toLinearMap =
      h.reductionSubmodule (lerayM X₁ X₂ X₃) X := by
  ext a
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_reductionSubmodule.2 ⟨⟨w, F.W₄_le_orthogonal_lerayM w.2⟩, hw, rfl⟩
  · intro ha
    obtain ⟨x, hxX, rfl⟩ := mem_reductionSubmodule.1 ha
    refine ⟨⟨_, F.isOrthogonalDecomposition.component_mem 4 x⟩,
      F.isOrthogonalDecomposition.component_mem_of_commutesWith hXc 4 hxX, ?_⟩
    change h.reductionMap _ ⟨_, _⟩ = h.reductionMap _ x
    rw [← sub_eq_zero, ← map_sub, reductionMap_eq_zero_iff]
    have := (lerayM X₁ X₂ X₃).neg_mem (F.sub_component_mem_lerayM h₁ h₂ x.2)
    simpa using this

/-- GKT Corollary 4.23: the Leray invariant is computed on `W₄`,
`L(X₁, X₂, X₃) = L(X₁ ∩ W₄, X₂ ∩ W₄, X₃ ∩ W₄)`. -/
theorem nonempty_isometryEquiv_lerayInvariant (hh : h.Nondegenerate) (h₁ : h.IsLagrangian X₁)
    (h₂ : h.IsLagrangian X₂) (h₃ : h.IsLagrangian X₃) :
    Nonempty (IsometryEquiv (h.lerayInvariant hh h₁ h₂ h₃)
      ((h.restrict (F.W 4)).lerayForm (F.isTransverseTriple₄ h₁ h₂ h₃)
        (F.isOrthogonalDecomposition.nondegenerate 4))) := by
  set ψ := F.isometryEquivReduction h₁ h₂
  have hmap : ∀ {X : Submodule D V}, CommutesWith F.W X →
      (h.reductionSubmodule (lerayM X₁ X₂ X₃) X).map ψ.symm.toLinearEquiv.toLinearMap =
        X.comap (F.W 4).subtype := by
    intro X hXc
    exact (Submodule.map_symm_eq_iff ψ.toLinearEquiv).2 (F.map_isometryEquivReduction h₁ h₂ hXc)
  exact ⟨lerayFormIsometryEquiv _ _ _ _ ψ.symm (hmap F.commutes₁) (hmap F.commutes₂)
    (hmap F.commutes₃)⟩

end FiveTermDecomposition

end LerayOnW₄

/-! ### Classification of triples up to the isometry group (GKT Lemma 4.24, Corollary 4.25) -/

section Orbits

variable {ε : ℤˣ} {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional D V] [NeZero (2 : D)]

/-- Two non-degenerate spaces of the same dimension with a Lagrangian each are isometric by an
isometry carrying one Lagrangian to the other. -/
theorem exists_isometryEquiv_map_isLagrangian {V' : Type*} [AddCommGroup V'] [Module D V']
    [FiniteDimensional D V'] {ε'' : ℤˣ} {k : EpsilonHermitianForm τ ε'' V}
    {k' : EpsilonHermitianForm τ ε'' V'} (hk : k.Nondegenerate) (hk' : k'.Nondegenerate)
    {L : Submodule D V} {L' : Submodule D V'} (hL : k.IsLagrangian L) (hL' : k'.IsLagrangian L')
    (hd : finrank D V = finrank D V') :
    ∃ φ : IsometryEquiv k k', L.map φ.toLinearEquiv.toLinearMap = L' := by
  obtain ⟨Y, hY, hLY⟩ := hL.exists_isLagrangian_isCompl hk
  obtain ⟨Y', hY', hLY'⟩ := hL'.exists_isLagrangian_isCompl hk'
  have hdL : finrank D L = finrank D L' := by
    have := hL.two_mul_finrank hk; have := hL'.two_mul_finrank hk'; omega
  obtain ⟨φ, hφ, -⟩ := exists_isometryEquiv_extend hk hk' hL hY hLY hL' hY' hLY'
    (LinearEquiv.ofFinrankEq _ _ hdL)
  refine ⟨φ, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, hφ ⟨x, hx⟩]
    exact Submodule.coe_mem _
  · intro y hy
    refine ⟨((LinearEquiv.ofFinrankEq _ _ hdL).symm ⟨y, hy⟩ : L), Submodule.coe_mem _, ?_⟩
    rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, hφ, LinearEquiv.apply_symm_apply]

omit [NeZero (2 : D)] in
/-- For a polarization the Lemma 4.9 isometry carries the two Lagrangians. -/
theorem exists_isometryEquiv_map_polarization {V' : Type*} [AddCommGroup V'] [Module D V']
    [FiniteDimensional D V'] {ε'' : ℤˣ} {k : EpsilonHermitianForm τ ε'' V}
    {k' : EpsilonHermitianForm τ ε'' V'} (hk : k.Nondegenerate) (hk' : k'.Nondegenerate)
    {X Y : Submodule D V} {X' Y' : Submodule D V'} (hX : k.IsLagrangian X) (hY : k.IsLagrangian Y)
    (hXY : Disjoint X Y) (hX' : k'.IsLagrangian X') (hY' : k'.IsLagrangian Y')
    (hXY' : Disjoint X' Y') (hd : finrank D V = finrank D V') :
    ∃ φ : IsometryEquiv k k', X.map φ.toLinearEquiv.toLinearMap = X' ∧
      Y.map φ.toLinearEquiv.toLinearMap = Y' := by
  have hdX : finrank D X = finrank D X' := by
    have := hX.two_mul_finrank hk; have := hX'.two_mul_finrank hk'; omega
  obtain ⟨φ, hφ, hφY⟩ := exists_isometryEquiv_extend hk hk' hX hY
    ((hX.isCompl_iff_disjoint hk hY).2 hXY) hX' hY' ((hX'.isCompl_iff_disjoint hk' hY').2 hXY')
    (LinearEquiv.ofFinrankEq _ _ hdX)
  refine ⟨φ, le_antisymm ?_ ?_, hφY⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, hφ ⟨x, hx⟩]
    exact Submodule.coe_mem _
  · intro y hy
    refine ⟨((LinearEquiv.ofFinrankEq _ _ hdX).symm ⟨y, hy⟩ : X), Submodule.coe_mem _, ?_⟩
    rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, hφ, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional D V] [NeZero (2 : D)] in
private theorem comap_eq_of_inf_eq {W A B : Submodule D V} (hAB : A ⊓ W = B ⊓ W) :
    A.comap W.subtype = B.comap W.subtype := by
  ext w
  simp only [Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · intro hw; exact (show (w : V) ∈ B ⊓ W from hAB ▸ ⟨hw, w.2⟩).1
  · intro hw; exact (show (w : V) ∈ A ⊓ W from hAB.symm ▸ ⟨hw, w.2⟩).1

omit [FiniteDimensional D V] [NeZero (2 : D)] in
private theorem disjoint_comap {W A B : Submodule D V} (hAB : Disjoint (A ⊓ W) (B ⊓ W)) :
    Disjoint (A.comap W.subtype) (B.comap W.subtype) := by
  rw [Submodule.disjoint_def]
  intro w hwA hwB
  exact Subtype.ext (Submodule.disjoint_def.1 hAB _ ⟨hwA, w.2⟩ ⟨hwB, w.2⟩)

/-- GKT Lemma 4.24 and Corollary 4.25: two triples of Lagrangians are conjugate under the isometry
group if and only if they have the same dimensions `dim (X₁ ∩ X₂ ∩ X₃)`, `dim (Xᵢ ∩ Xⱼ)` and
isometric Leray invariants. -/
theorem exists_isometry_map_iff (hh : h.Nondegenerate) {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Submodule D V}
    (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂) (h₃ : h.IsLagrangian X₃)
    (k₁ : h.IsLagrangian Y₁) (k₂ : h.IsLagrangian Y₂) (k₃ : h.IsLagrangian Y₃) :
    (∃ g : h.isometryGroup, X₁.map (g : V ≃ₗ[D] V).toLinearMap = Y₁ ∧
        X₂.map (g : V ≃ₗ[D] V).toLinearMap = Y₂ ∧ X₃.map (g : V ≃ₗ[D] V).toLinearMap = Y₃) ↔
      finrank D (X₁ ⊓ X₂ ⊓ X₃ : Submodule D V) = finrank D (Y₁ ⊓ Y₂ ⊓ Y₃ : Submodule D V) ∧
      finrank D (X₁ ⊓ X₂ : Submodule D V) = finrank D (Y₁ ⊓ Y₂ : Submodule D V) ∧
      finrank D (X₂ ⊓ X₃ : Submodule D V) = finrank D (Y₂ ⊓ Y₃ : Submodule D V) ∧
      finrank D (X₁ ⊓ X₃ : Submodule D V) = finrank D (Y₁ ⊓ Y₃ : Submodule D V) ∧
      Nonempty (IsometryEquiv (h.lerayInvariant hh h₁ h₂ h₃) (h.lerayInvariant hh k₁ k₂ k₃)) := by
  constructor
  · rintro ⟨g, rfl, rfl, rfl⟩
    have hinj := (g : V ≃ₗ[D] V).injective
    have e₂ : ∀ A B : Submodule D V, finrank D (A ⊓ B : Submodule D V) =
        finrank D (A.map (g : V ≃ₗ[D] V).toLinearMap ⊓ B.map (g : V ≃ₗ[D] V).toLinearMap :
          Submodule D V) := fun A B => by
      rw [← Submodule.map_inf _ hinj]; exact (LinearEquiv.finrank_map_eq _ _).symm
    refine ⟨?_, e₂ _ _, e₂ _ _, e₂ _ _,
      nonempty_isometryEquiv_lerayInvariant_map_isometryGroup hh h₁ h₂ h₃ g⟩
    rw [← Submodule.map_inf _ hinj, ← Submodule.map_inf _ hinj]
    exact (LinearEquiv.finrank_map_eq _ _).symm
  · rintro ⟨d₁₂₃, d₁₂, d₂₃, d₁₃, ⟨σ⟩⟩
    obtain ⟨F⟩ := nonempty_fiveTermDecomposition hh h₁ h₂ h₃
    obtain ⟨F'⟩ := nonempty_fiveTermDecomposition hh k₁ k₂ k₃
    have hd₀ : finrank D (F.W 0) = finrank D (F'.W 0) := by
      rw [F.finrank_W₀ h₁, F'.finrank_W₀ k₁, d₁₂₃]
    have hd₁ : finrank D (F.W 1) = finrank D (F'.W 1) := by
      have := F.finrank_W₁ h₁ h₂; have := F'.finrank_W₁ k₁ k₂; omega
    have hd₂ : finrank D (F.W 2) = finrank D (F'.W 2) := by
      have := F.finrank_W₂ h₁; have := F'.finrank_W₂ k₁; omega
    have hd₃ : finrank D (F.W 3) = finrank D (F'.W 3) := by
      have := F.finrank_W₃ h₁; have := F'.finrank_W₃ k₁; omega
    have hnd := F.isOrthogonalDecomposition.nondegenerate
    have hnd' := F'.isOrthogonalDecomposition.nondegenerate
    -- isometries of the pieces
    have P : ∀ j : Fin 5, Prop := fun j =>
      ∃ φ : IsometryEquiv (h.restrict (F.W j)) (h.restrict (F'.W j)),
        (X₁.comap (F.W j).subtype).map φ.toLinearEquiv.toLinearMap = Y₁.comap (F'.W j).subtype ∧
        (X₂.comap (F.W j).subtype).map φ.toLinearEquiv.toLinearMap = Y₂.comap (F'.W j).subtype ∧
        (X₃.comap (F.W j).subtype).map φ.toLinearEquiv.toLinearMap = Y₃.comap (F'.W j).subtype
    have p₀ : ∃ φ : IsometryEquiv (h.restrict (F.W 0)) (h.restrict (F'.W 0)),
        (X₁.comap (F.W 0).subtype).map φ.toLinearEquiv.toLinearMap = Y₁.comap (F'.W 0).subtype ∧
        (X₂.comap (F.W 0).subtype).map φ.toLinearEquiv.toLinearMap = Y₂.comap (F'.W 0).subtype ∧
        (X₃.comap (F.W 0).subtype).map φ.toLinearEquiv.toLinearMap =
          Y₃.comap (F'.W 0).subtype := by
      obtain ⟨φ, hφ⟩ := exists_isometryEquiv_map_isLagrangian (hnd 0) (hnd' 0)
        (F.isLagrangian_comap₁ h₁ 0) (F'.isLagrangian_comap₁ k₁ 0) hd₀
      refine ⟨φ, hφ, ?_, ?_⟩
      · rw [← comap_eq_of_inf_eq F.eq₀₁₂, ← comap_eq_of_inf_eq F'.eq₀₁₂]; exact hφ
      · rw [← comap_eq_of_inf_eq F.eq₀₁₃, ← comap_eq_of_inf_eq F'.eq₀₁₃]; exact hφ
    have p₁ : ∃ φ : IsometryEquiv (h.restrict (F.W 1)) (h.restrict (F'.W 1)),
        (X₁.comap (F.W 1).subtype).map φ.toLinearEquiv.toLinearMap = Y₁.comap (F'.W 1).subtype ∧
        (X₂.comap (F.W 1).subtype).map φ.toLinearEquiv.toLinearMap = Y₂.comap (F'.W 1).subtype ∧
        (X₃.comap (F.W 1).subtype).map φ.toLinearEquiv.toLinearMap =
          Y₃.comap (F'.W 1).subtype := by
      obtain ⟨φ, hφ₁, hφ₂⟩ := exists_isometryEquiv_map_polarization (hnd 1) (hnd' 1)
        (F.isLagrangian_comap₁ h₁ 1) (F.isLagrangian_comap₂ h₂ 1) (disjoint_comap F.disjoint₁)
        (F'.isLagrangian_comap₁ k₁ 1) (F'.isLagrangian_comap₂ k₂ 1)
        (disjoint_comap F'.disjoint₁) hd₁
      refine ⟨φ, hφ₁, hφ₂, ?_⟩
      rw [← comap_eq_of_inf_eq F.eq₁, ← comap_eq_of_inf_eq F'.eq₁]; exact hφ₂
    have p₂ : ∃ φ : IsometryEquiv (h.restrict (F.W 2)) (h.restrict (F'.W 2)),
        (X₁.comap (F.W 2).subtype).map φ.toLinearEquiv.toLinearMap = Y₁.comap (F'.W 2).subtype ∧
        (X₂.comap (F.W 2).subtype).map φ.toLinearEquiv.toLinearMap = Y₂.comap (F'.W 2).subtype ∧
        (X₃.comap (F.W 2).subtype).map φ.toLinearEquiv.toLinearMap =
          Y₃.comap (F'.W 2).subtype := by
      obtain ⟨φ, hφ₂, hφ₁⟩ := exists_isometryEquiv_map_polarization (hnd 2) (hnd' 2)
        (F.isLagrangian_comap₂ h₂ 2) (F.isLagrangian_comap₁ h₁ 2) (disjoint_comap F.disjoint₂)
        (F'.isLagrangian_comap₂ k₂ 2) (F'.isLagrangian_comap₁ k₁ 2)
        (disjoint_comap F'.disjoint₂) hd₂
      refine ⟨φ, hφ₁, hφ₂, ?_⟩
      rw [← comap_eq_of_inf_eq F.eq₂, ← comap_eq_of_inf_eq F'.eq₂]; exact hφ₁
    have p₃ : ∃ φ : IsometryEquiv (h.restrict (F.W 3)) (h.restrict (F'.W 3)),
        (X₁.comap (F.W 3).subtype).map φ.toLinearEquiv.toLinearMap = Y₁.comap (F'.W 3).subtype ∧
        (X₂.comap (F.W 3).subtype).map φ.toLinearEquiv.toLinearMap = Y₂.comap (F'.W 3).subtype ∧
        (X₃.comap (F.W 3).subtype).map φ.toLinearEquiv.toLinearMap =
          Y₃.comap (F'.W 3).subtype := by
      obtain ⟨φ, hφ₃, hφ₁⟩ := exists_isometryEquiv_map_polarization (hnd 3) (hnd' 3)
        (F.isLagrangian_comap₃ h₃ 3) (F.isLagrangian_comap₁ h₁ 3) (disjoint_comap F.disjoint₃)
        (F'.isLagrangian_comap₃ k₃ 3) (F'.isLagrangian_comap₁ k₁ 3)
        (disjoint_comap F'.disjoint₃) hd₃
      refine ⟨φ, hφ₁, ?_, hφ₃⟩
      rw [← comap_eq_of_inf_eq F.eq₃, ← comap_eq_of_inf_eq F'.eq₃]; exact hφ₁
    have p₄ : ∃ φ : IsometryEquiv (h.restrict (F.W 4)) (h.restrict (F'.W 4)),
        (X₁.comap (F.W 4).subtype).map φ.toLinearEquiv.toLinearMap = Y₁.comap (F'.W 4).subtype ∧
        (X₂.comap (F.W 4).subtype).map φ.toLinearEquiv.toLinearMap = Y₂.comap (F'.W 4).subtype ∧
        (X₃.comap (F.W 4).subtype).map φ.toLinearEquiv.toLinearMap =
          Y₃.comap (F'.W 4).subtype := by
      obtain ⟨ψ⟩ := F.nonempty_isometryEquiv_lerayInvariant hh h₁ h₂ h₃
      obtain ⟨ψ'⟩ := F'.nonempty_isometryEquiv_lerayInvariant hh k₁ k₂ k₃
      exact (exists_isometryEquiv_iff_lerayForm (F.isTransverseTriple₄ h₁ h₂ h₃)
        (hnd 4) (F'.isTransverseTriple₄ k₁ k₂ k₃) (hnd' 4)).2 ⟨(ψ.symm.trans σ).trans ψ'⟩
    have hpiece : ∀ j : Fin 5, ∃ φ : IsometryEquiv (h.restrict (F.W j)) (h.restrict (F'.W j)),
        (X₁.comap (F.W j).subtype).map φ.toLinearEquiv.toLinearMap = Y₁.comap (F'.W j).subtype ∧
        (X₂.comap (F.W j).subtype).map φ.toLinearEquiv.toLinearMap = Y₂.comap (F'.W j).subtype ∧
        (X₃.comap (F.W j).subtype).map φ.toLinearEquiv.toLinearMap =
          Y₃.comap (F'.W j).subtype := by
      intro j
      fin_cases j
      exacts [p₀, p₁, p₂, p₃, p₄]
    clear P
    choose φ hφ using hpiece
    obtain ⟨Φ, hΦ⟩ := exists_isometryEquiv_of_decomposition F.isOrthogonalDecomposition
      F'.isOrthogonalDecomposition φ
    -- `Φ` carries `Xᵢ ∩ W_j` onto `Yᵢ ∩ W'_j`
    have hmap : ∀ {X Y : Submodule D V} (j : Fin 5),
        (X.comap (F.W j).subtype).map (φ j).toLinearEquiv.toLinearMap = Y.comap (F'.W j).subtype →
        (X ⊓ F.W j).map Φ.toLinearEquiv.toLinearMap = Y ⊓ F'.W j := by
      intro X Y j hXY
      ext y
      constructor
      · rintro ⟨x, ⟨hxX, hxW⟩, rfl⟩
        have hx : (⟨x, hxW⟩ : F.W j) ∈ X.comap (F.W j).subtype := hxX
        have hmem : φ j ⟨x, hxW⟩ ∈ (X.comap (F.W j).subtype).map
            (φ j).toLinearEquiv.toLinearMap := ⟨⟨x, hxW⟩, hx, rfl⟩
        rw [hXY] at hmem
        rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, hΦ j ⟨x, hxW⟩]
        exact ⟨hmem, (φ j ⟨x, hxW⟩).2⟩
      · rintro ⟨hyY, hyW⟩
        have hy : (⟨y, hyW⟩ : F'.W j) ∈ Y.comap (F'.W j).subtype := hyY
        rw [← hXY] at hy
        obtain ⟨x, hx, hxy⟩ := hy
        refine ⟨x, ⟨hx, x.2⟩, ?_⟩
        rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, hΦ j x]
        exact congrArg Subtype.val hxy
    have hmapX : ∀ {X Y : Submodule D V}, CommutesWith F.W X → CommutesWith F'.W Y →
        (∀ j, (X.comap (F.W j).subtype).map (φ j).toLinearEquiv.toLinearMap =
          Y.comap (F'.W j).subtype) → X.map Φ.toLinearEquiv.toLinearMap = Y := by
      intro X Y hX hY hXY
      rw [← hX, ← hY, Submodule.map_iSup]
      exact iSup_congr fun j => hmap j (hXY j)
    refine ⟨⟨Φ.toLinearEquiv, Φ.map_app⟩, hmapX F.commutes₁ F'.commutes₁ fun j => (hφ j).1,
      hmapX F.commutes₂ F'.commutes₂ fun j => (hφ j).2.1,
      hmapX F.commutes₃ F'.commutes₃ fun j => (hφ j).2.2⟩

end Orbits

end EpsilonHermitianForm

end Langlands

end
