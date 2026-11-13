import Langlands.Representation.CuspidalSupport.NormalHeckeGrading
import Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeDomain

/-!
# The lines `F_x(ρ)` of the Hecke algebra of an open normal subgroup

Let `H` be an open normal subgroup of a topological group `G` and `ρ` an irreducible smooth
complex representation of `H`. For `x ∈ G` the line `F_x(ρ)` consists of the functions of the
Hecke space `H(G, ρ) = heckeSubmodule H ρ` supported in the coset `H x`. This module proves the
structure of `H(G, ρ)` described in Renard VI.4.3 in this generality:

* `φ ↦ φ(x)` identifies `F_x(ρ)` with the twisted intertwiners `ρ^x → ρ`;
* `F_x(ρ)` has dimension at most one (for `ρ` of countable dimension), and is nonzero exactly
  when `ρ^x ≅ ρ`; these `x` form a subgroup containing `H` and the centre of `G`;
* the product rule (VI.4.3.1), the inverses of nonzero elements of a line, and the
  commutation rule (VI.4.3.2) when `G ⧸ H` is commutative;
* `H(G, ρ)` is spanned by the lines, and, when `G ⧸ H` has the two-unique-products property,
  its units are exactly its nonzero elements lying in some line (VI.4.3.3).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable (H : Subgroup G) (ρ : SmoothRep.{0, uG, uV} ℂ H)

/-- Membership in the line `F_x(ρ)`: a function of the Hecke space supported in `H x`. -/
def InLine (x : G) (φ : G → Module.End ℂ ρ) : Prop :=
  φ ∈ heckeSubmodule H ρ ∧ ∀ g, φ g ≠ 0 → g * x⁻¹ ∈ H

/-- `T` intertwines `ρ^x : h ↦ ρ(x⁻¹ h x)` with `ρ`. -/
def IsTwistHom (x : G) (T : Module.End ℂ ρ) : Prop :=
  ∀ h h' : H, (h' : G) = x⁻¹ * h * x → T * ρ.representation h' = ρ.representation h * T

/-- `ρ^x ≅ ρ`: some bijective intertwiner `ρ^x → ρ` exists. -/
def InStab (x : G) : Prop :=
  ∃ T : Module.End ℂ ρ, IsTwistHom H ρ x T ∧ Function.Bijective T

variable {H ρ}

section Algebra

theorem isTwistHom_apply {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) (g : G) :
    IsTwistHom H ρ g (φ g) := by
  intro h h' hh'
  rw [← hecke_mul_right H ρ hφ, ← hecke_mul_left H ρ hφ, hh']
  congr 1
  group

theorem zero_inLine (x : G) : InLine H ρ x 0 :=
  ⟨Submodule.zero_mem _, fun _ hg => (hg rfl).elim⟩

theorem InLine.smul {x : G} {φ : G → Module.End ℂ ρ} (hφ : InLine H ρ x φ) (c : ℂ) :
    InLine H ρ x (c • φ) :=
  ⟨Submodule.smul_mem _ c hφ.1, fun g hg =>
    hφ.2 g fun h => hg (by rw [Pi.smul_apply, h, smul_zero])⟩

theorem InLine.of_mul_inv_mem {x x' : G} {φ : G → Module.End ℂ ρ} (hφ : InLine H ρ x φ)
    (hx : x * x'⁻¹ ∈ H) : InLine H ρ x' φ :=
  ⟨hφ.1, fun g hg => by
    have := H.mul_mem (hφ.2 g hg) hx
    rwa [mul_assoc, inv_mul_cancel_left] at this⟩

/-- Two elements of `F_x(ρ)` agreeing at `x` are equal. -/
theorem eq_of_inLine {x : G} {φ ψ : G → Module.End ℂ ρ} (hφ : InLine H ρ x φ)
    (hψ : InLine H ρ x ψ) (h : φ x = ψ x) : φ = ψ := by
  funext g
  by_cases hg : g * x⁻¹ ∈ H
  · have e : g = ((⟨g * x⁻¹, hg⟩ : H) : G) * x := by simp
    rw [e, hecke_mul_left H ρ hφ.1, hecke_mul_left H ρ hψ.1, h]
  · have h1 : φ g = 0 := by
      by_contra h0
      exact hg (hφ.2 g h0)
    have h2 : ψ g = 0 := by
      by_contra h0
      exact hg (hψ.2 g h0)
    rw [h1, h2]

/-- An element of `F_x(ρ)` vanishing at `x` is zero. -/
theorem eq_zero_of_inLine {x : G} {φ : G → Module.End ℂ ρ} (hφ : InLine H ρ x φ)
    (h : φ x = 0) : φ = 0 :=
  eq_of_inLine hφ (zero_inLine x) h

theorem inLine_apply_ne_zero {x : G} {φ : G → Module.End ℂ ρ} (hφ : InLine H ρ x φ)
    (h0 : φ ≠ 0) : φ x ≠ 0 :=
  fun h => h0 (eq_zero_of_inLine hφ h)

/-- Every twisted intertwiner `T : ρ^x → ρ` is the value at `x` of an element of `F_x(ρ)`:
the function supported on `H x` with value `ρ(g x⁻¹) T` at `g`. -/
theorem exists_inLine_of_isTwistHom [H.Normal] {x : G} {T : Module.End ℂ ρ}
    (hT : IsTwistHom H ρ x T) : ∃ φ, InLine H ρ x φ ∧ φ x = T := by
  have hT' : ∀ h k : H, (k : G) = x⁻¹⁻¹ * h * x⁻¹ →
      ρ.representation k * T = T * ρ.representation h := by
    intro h k hk
    refine (hT k h ?_).symm
    rw [hk]
    group
  refine ⟨_, ⟨inverseFunction_mem x⁻¹ T hT', fun g hg => ?_⟩, ?_⟩
  · by_contra hc
    exact hg (dite_eq_right hc)
  · have hx : x * x⁻¹ ∈ H := by
      rw [mul_inv_cancel]
      exact H.one_mem
    rw [dite_eq_left hx]
    have e : (⟨x * x⁻¹, hx⟩ : H) = 1 := Subtype.ext (mul_inv_cancel x)
    rw [e, map_one, one_mul]

theorem IsTwistHom.map_conj [hN : H.Normal] {x : G} {T : Module.End ℂ ρ}
    (hT : IsTwistHom H ρ x T) (k : H) (v : ρ) :
    T (ρ.representation k v) =
      ρ.representation ⟨x * k * x⁻¹, hN.conj_mem _ k.2 x⟩ (T v) := by
  have := hT ⟨x * k * x⁻¹, hN.conj_mem _ k.2 x⟩ k (by
    change (k : G) = x⁻¹ * (x * k * x⁻¹) * x
    group)
  exact LinearMap.congr_fun this v

theorem IsTwistHom.map_conj' [hN : H.Normal] {x : G} {T : Module.End ℂ ρ}
    (hT : IsTwistHom H ρ x T) (k : H) (v : ρ) :
    ρ.representation k (T v) =
      T (ρ.representation ⟨x⁻¹ * k * x, by simpa using hN.conj_mem _ k.2 x⁻¹⟩ v) := by
  have := hT k ⟨x⁻¹ * k * x, by simpa using hN.conj_mem _ k.2 x⁻¹⟩ rfl
  exact (LinearMap.congr_fun this v).symm

/-- A nonzero twisted intertwiner of the irreducible `ρ` is bijective. -/
theorem IsTwistHom.bijective [hN : H.Normal] [ρ.representation.IsIrreducible] {x : G}
    {T : Module.End ℂ ρ} (hT : IsTwistHom H ρ x T) (h0 : T ≠ 0) : Function.Bijective T := by
  refine ⟨injective_of_twisted ρ.representation T
    (fun k => ⟨x * k * x⁻¹, hN.conj_mem _ k.2 x⟩) (fun k v => hT.map_conj k v) h0,
    fun v => ?_⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u, T u ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (LinearMap.ext hc)
  have hmem := mem_of_isIrreducible ρ.representation (LinearMap.range T)
    (fun k v hv => ?_) (LinearMap.mem_range_self _ u₀) hu₀ v
  · exact LinearMap.mem_range.mp hmem
  · obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    exact ⟨_, (hT.map_conj' k u).symm⟩

theorem ne_zero_of_bijective [ρ.representation.IsIrreducible] {T : Module.End ℂ ρ}
    (hT : Function.Bijective T) : T ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible ρ.representation
  intro h0
  apply hv
  apply hT.1
  rw [h0, LinearMap.zero_apply, LinearMap.zero_apply]

theorem bijective_mul {T S : Module.End ℂ ρ} (hT : Function.Bijective T)
    (hS : Function.Bijective S) : Function.Bijective (T * S) := by
  rw [Module.End.coe_mul]
  exact hT.comp hS

theorem exists_inverse_of_bijective {T : Module.End ℂ ρ} (hT : Function.Bijective T) :
    ∃ U : Module.End ℂ ρ, T * U = 1 ∧ U * T = 1 ∧ Function.Bijective U := by
  let e := LinearEquiv.ofBijective T hT
  exact ⟨e.symm.toLinearMap, LinearMap.ext fun v => e.apply_symm_apply v,
    LinearMap.ext fun v => e.symm_apply_apply v, e.symm.bijective⟩

/-- Schur's lemma for twisted intertwiners: when `T : ρ^x → ρ` is bijective, every twisted
intertwiner `ρ^x → ρ` is a multiple of `T`, for `ρ` of countable dimension. -/
theorem IsTwistHom.exists_eq_smul [H.Normal] [ρ.representation.IsIrreducible]
    (hrank : Module.rank ℂ ρ ≤ Cardinal.aleph0) {x : G} {T S : Module.End ℂ ρ}
    (hT : IsTwistHom H ρ x T) (hTb : Function.Bijective T) (hS : IsTwistHom H ρ x S) :
    ∃ c : ℂ, S = c • T := by
  let e := LinearEquiv.ofBijective T hTb
  let U : ρ.representation.IntertwiningMap ρ.representation :=
    { toLinearMap := e.symm.toLinearMap ∘ₗ S
      isIntertwining' := fun k => by
        refine LinearMap.ext fun v => e.injective ?_
        change e (e.symm (S (ρ.representation k v))) =
          T (ρ.representation k (e.symm (S v)))
        rw [hS.map_conj, hT.map_conj, e.apply_symm_apply]
        change _ = ρ.representation _ (e (e.symm _))
        rw [e.apply_symm_apply] }
  obtain ⟨c, hc, -⟩ := countableDimensionalSchur ρ.representation hrank inferInstance U
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  have h1 := congrArg (fun φ : ρ.representation.IntertwiningMap ρ.representation => φ v) hc
  simp only [Representation.IntertwiningMap.smul_apply] at h1
  change e.symm (S v) = _ at h1
  rw [LinearMap.smul_apply, ← e.apply_symm_apply (S v), h1]
  change e (c • v) = c • e v
  rw [map_smul]

theorem IsTwistHom.mul [hN : H.Normal] {x y : G} {T S : Module.End ℂ ρ}
    (hT : IsTwistHom H ρ x T) (hS : IsTwistHom H ρ y S) : IsTwistHom H ρ (x * y) (T * S) := by
  intro h h' hh'
  let m : H := ⟨x⁻¹ * h * x, by simpa using hN.conj_mem _ h.2 x⁻¹⟩
  have hm : (h' : G) = y⁻¹ * (m : G) * y := by
    rw [hh']
    change (x * y)⁻¹ * (h : G) * (x * y) = y⁻¹ * (x⁻¹ * h * x) * y
    group
  rw [mul_assoc, hS m h' hm, ← mul_assoc, hT h m rfl, mul_assoc]

theorem IsTwistHom.of_inverse {x : G} {T U : Module.End ℂ ρ} (hT : IsTwistHom H ρ x T)
    (h1 : T * U = 1) (h2 : U * T = 1) : IsTwistHom H ρ x⁻¹ U := by
  intro h h' hh'
  have e := hT h' h (by rw [hh']; group)
  calc U * ρ.representation h' = U * ρ.representation h' * (T * U) := by rw [h1, mul_one]
    _ = U * (ρ.representation h' * T) * U := by simp only [mul_assoc]
    _ = U * (T * ρ.representation h) * U := by rw [e]
    _ = U * T * ρ.representation h * U := by simp only [mul_assoc]
    _ = ρ.representation h * U := by rw [h2, one_mul]

variable (H ρ) in
/-- The subgroup `N` of the `x ∈ G` with `ρ^x ≅ ρ`. -/
def stabSubgroup [H.Normal] : Subgroup G where
  carrier := {x | InStab H ρ x}
  one_mem' := ⟨1, fun h h' hh' => by
      have : h' = h := Subtype.ext (by rw [hh']; group)
      rw [this, one_mul, mul_one], fun _ _ hab => hab, fun b => ⟨b, rfl⟩⟩
  mul_mem' := by
    rintro x y ⟨T, hT, hTb⟩ ⟨S, hS, hSb⟩
    exact ⟨T * S, hT.mul hS, bijective_mul hTb hSb⟩
  inv_mem' := by
    rintro x ⟨T, hT, hTb⟩
    obtain ⟨U, h1, h2, hU⟩ := exists_inverse_of_bijective hTb
    exact ⟨U, hT.of_inverse h1 h2, hU⟩

theorem mem_stabSubgroup [H.Normal] {x : G} : x ∈ stabSubgroup H ρ ↔ InStab H ρ x :=
  Iff.rfl

variable (H ρ) in
theorem le_stabSubgroup [H.Normal] : H ≤ stabSubgroup H ρ := by
  intro x hx
  have hinv : ∀ (k : H) (u : ρ), ρ.representation k⁻¹ (ρ.representation k u) = u := by
    intro k u
    have := representation_mul_inv H ρ k⁻¹ u
    rwa [inv_inv] at this
  refine ⟨ρ.representation ⟨x, hx⟩, fun h h' hh' => ?_,
    fun v w hvw => ?_, fun v => ⟨ρ.representation ⟨x, hx⟩⁻¹ v, representation_mul_inv H ρ _ v⟩⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change x * (h' : G) = (h : G) * x
    rw [hh']
    group
  · rw [← hinv ⟨x, hx⟩ v, hvw, hinv]

variable (H ρ) in
theorem center_le_stabSubgroup [H.Normal] : Subgroup.center G ≤ stabSubgroup H ρ := by
  intro z hz
  refine ⟨1, fun h h' hh' => ?_, fun _ _ hab => hab, fun b => ⟨b, rfl⟩⟩
  have : h' = h := Subtype.ext (by
    rw [hh', mul_assoc, Subgroup.mem_center_iff.mp hz (h : G), inv_mul_cancel_left])
  rw [this, one_mul, mul_one]

/-- A nonzero value `φ(g)` of a Hecke function witnesses `ρ^g ≅ ρ`. -/
theorem inStab_of_apply_ne_zero [H.Normal] [ρ.representation.IsIrreducible]
    {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) {g : G} (hg : φ g ≠ 0) :
    InStab H ρ g :=
  ⟨φ g, isTwistHom_apply hφ g, (isTwistHom_apply hφ g).bijective hg⟩

/-- `F_x(ρ)` is nonzero exactly when `ρ^x ≅ ρ`. -/
theorem exists_inLine_ne_zero_iff [H.Normal] [ρ.representation.IsIrreducible] {x : G} :
    (∃ φ, InLine H ρ x φ ∧ φ ≠ 0) ↔ InStab H ρ x := by
  constructor
  · rintro ⟨φ, hφ, h0⟩
    exact inStab_of_apply_ne_zero hφ.1 (inLine_apply_ne_zero hφ h0)
  · rintro ⟨T, hT, hTb⟩
    obtain ⟨φ, hφ, hφx⟩ := exists_inLine_of_isTwistHom hT
    refine ⟨φ, hφ, fun h => ne_zero_of_bijective hTb ?_⟩
    rw [← hφx, h, Pi.zero_apply]

/-- `F_x(ρ)` has dimension at most one, for `ρ` of countable dimension. -/
theorem exists_eq_smul_of_inLine [H.Normal] [ρ.representation.IsIrreducible]
    (hrank : Module.rank ℂ ρ ≤ Cardinal.aleph0) {x : G} {φ ψ : G → Module.End ℂ ρ}
    (hφ : InLine H ρ x φ) (hψ : InLine H ρ x ψ) (h0 : φ ≠ 0) : ∃ c : ℂ, ψ = c • φ := by
  have hT := isTwistHom_apply hφ.1 x
  obtain ⟨c, hc⟩ := hT.exists_eq_smul hrank (hT.bijective (inLine_apply_ne_zero hφ h0))
    (isTwistHom_apply hψ.1 x)
  exact ⟨c, eq_of_inLine hψ (hφ.smul c) hc⟩

variable (H ρ) in
/-- `H(G, ρ)` is spanned by the lines `F_x(ρ)`: a Hecke function is the sum of its
restrictions to the finitely many cosets meeting its support. -/
theorem heckeSubmodule_eq_span [hN : H.Normal] :
    heckeSubmodule H ρ = Submodule.span ℂ {φ | ∃ x, InLine H ρ x φ} := by
  classical
  apply le_antisymm
  · intro φ hφ
    let piece : G ⧸ H → G → Module.End ℂ ρ := fun q g => if (g : G ⧸ H) = q then φ g else 0
    have hpiece : ∀ q, InLine H ρ q.out (piece q) := by
      intro q
      refine ⟨⟨fun h h' g => ?_, ?_⟩, fun g hg => ?_⟩
      · have hm : (((h : G) * g * h' : G) : G ⧸ H) = (g : G ⧸ H) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr h.2,
            (QuotientGroup.eq_one_iff _).mpr h'.2, one_mul, mul_one]
        simp only [piece, hm]
        split_ifs
        · exact hφ.1 h h' g
        · rw [mul_zero, zero_mul]
      · refine (Set.finite_singleton q).subset ?_
        rintro _ ⟨g, hg, rfl⟩
        rw [Set.mem_singleton_iff]
        by_contra hc
        exact hg (ite_eq_right hc)
      · have hq : (g : G ⧸ H) = q := by
          by_contra hc
          exact hg (ite_eq_right hc)
        rw [← QuotientGroup.out_eq' q, QuotientGroup.eq] at hq
        have := H.inv_mem hq
        rw [mul_inv_rev, inv_inv] at this
        exact hN.mem_comm_iff.mp this
    have hsum : φ = ∑ q ∈ hφ.2.toFinset, piece q := by
      funext g
      rw [Finset.sum_apply]
      simp only [piece]
      rw [Finset.sum_ite_eq]
      split_ifs with hg
      · rfl
      · by_contra h0
        exact hg (hφ.2.mem_toFinset.mpr ⟨g, h0, rfl⟩)
    rw [hsum]
    exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨q.out, hpiece q⟩
  · rw [Submodule.span_le]
    rintro φ ⟨x, hφ⟩
    exact hφ.1

theorem heckeConvolution_zero_left (ψ : G → Module.End ℂ ρ) :
    heckeConvolution H ρ 0 ψ = 0 := by
  funext x
  exact finsum_eq_zero_of_forall_eq_zero fun q => zero_mul _

theorem heckeConvolution_zero_right (φ : G → Module.End ℂ ρ) :
    heckeConvolution H ρ φ 0 = 0 := by
  funext x
  exact finsum_eq_zero_of_forall_eq_zero fun q => mul_zero _

/-- At a unique product `a b` of the coset supports of two Hecke functions, their convolution
does not vanish at some point of the coset `a b`. -/
theorem exists_heckeConvolution_ne_zero_of_uniqueMul [H.Normal] [ρ.representation.IsIrreducible]
    {φ ψ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) (hψ : ψ ∈ heckeSubmodule H ρ)
    {a b : G ⧸ H} (ha : a ∈ hφ.2.toFinset) (hb : b ∈ hψ.2.toFinset)
    (hu : UniqueMul hφ.2.toFinset hψ.2.toFinset a b) :
    ∃ z : G, (z : G ⧸ H) = a * b ∧ heckeConvolution H ρ φ ψ z ≠ 0 := by
  obtain ⟨g, hg, rfl⟩ := hφ.2.mem_toFinset.mp ha
  obtain ⟨y, hy, rfl⟩ := hψ.2.mem_toFinset.mp hb
  refine ⟨g * y, QuotientGroup.mk_mul _ _ _, ?_⟩
  have hsum : heckeConvolution H ρ φ ψ (g * y) =
      φ (g : G ⧸ H).out * ψ ((g : G ⧸ H).out⁻¹ * (g * y)) := by
    refine finsum_eq_single _ (g : G ⧸ H) fun q hq => ?_
    by_contra hne
    apply hq
    have h1 : φ q.out ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : ψ (q.out⁻¹ * (g * y)) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hmem1 : q ∈ hφ.2.toFinset := hφ.2.mem_toFinset.mpr ⟨q.out, h1, QuotientGroup.out_eq' q⟩
    have hmem2 : ((q.out⁻¹ * (g * y) : G) : G ⧸ H) ∈ hψ.2.toFinset :=
      hψ.2.mem_toFinset.mpr ⟨_, h2, rfl⟩
    refine (hu hmem1 hmem2 ?_).1
    rw [QuotientGroup.mk_mul (N := H) (a := q.out⁻¹) (b := g * y), QuotientGroup.mk_inv,
      QuotientGroup.out_eq', mul_inv_cancel_left, QuotientGroup.mk_mul]
  have hA : φ (g : G ⧸ H).out ≠ 0 :=
    hecke_ne_zero_of_mk_eq H ρ hφ hg (QuotientGroup.out_eq' _).symm
  have hB : ψ ((g : G ⧸ H).out⁻¹ * (g * y)) ≠ 0 := by
    refine hecke_ne_zero_of_mk_eq H ρ hψ hy ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', QuotientGroup.mk_mul,
      inv_mul_cancel_left]
  obtain ⟨w, hw⟩ : ∃ w, ψ ((g : G ⧸ H).out⁻¹ * (g * y)) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hB (LinearMap.ext h)
  intro h0
  rw [hsum] at h0
  refine hecke_injective H ρ hφ hA |>.ne hw ?_
  rw [map_zero]
  exact LinearMap.congr_fun h0 w

end Algebra

section Unit

variable [IsTopologicalGroup G] (hH : IsOpen (H : Set G)) [hN : H.Normal]
  [ρ.representation.IsIrreducible]

variable (H ρ) in
/-- The unit `ε` of `H(G, ρ)`: the Hecke function of the identity of `ind_H^G ρ`. -/
def unitHecke : G → Module.End ℂ ρ :=
  (heckeEquiv H ρ hH 1 : G → Module.End ℂ ρ)

theorem unitHecke_one : unitHecke H ρ hH 1 = 1 :=
  endValue_one_one H ρ hH

theorem inLine_unitHecke : InLine H ρ 1 (unitHecke H ρ hH) := by
  refine ⟨(heckeEquiv H ρ hH 1).2, fun g hg => ?_⟩
  rw [inv_one, mul_one]
  by_contra hc
  exact hg (endValue_one_of_not_mem H ρ hH hc)

theorem unitHecke_ne_zero : unitHecke H ρ hH ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible ρ.representation
  have := congrArg (fun φ : G → Module.End ℂ ρ => φ 1 v) h
  simp only [unitHecke_one, Pi.zero_apply, LinearMap.zero_apply, Module.End.one_apply] at this
  exact hv this

include hH in
theorem exists_heckeEquiv_eq {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) :
    ∃ α, (heckeEquiv H ρ hH α : G → Module.End ℂ ρ) = φ :=
  ⟨(heckeEquiv H ρ hH).symm ⟨φ, hφ⟩,
    congrArg Subtype.val ((heckeEquiv H ρ hH).apply_symm_apply ⟨φ, hφ⟩)⟩

include hH in
/-- `H(G, ρ)` is closed under convolution. -/
theorem heckeConvolution_mem {φ ψ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ)
    (hψ : ψ ∈ heckeSubmodule H ρ) : heckeConvolution H ρ φ ψ ∈ heckeSubmodule H ρ := by
  obtain ⟨α, rfl⟩ := exists_heckeEquiv_eq hH hφ
  obtain ⟨β, rfl⟩ := exists_heckeEquiv_eq hH hψ
  rw [← heckeEquiv_mul]
  exact (heckeEquiv H ρ hH (α * β)).2

theorem unitHecke_conv {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) :
    heckeConvolution H ρ (unitHecke H ρ hH) φ = φ := by
  obtain ⟨α, rfl⟩ := exists_heckeEquiv_eq hH hφ
  rw [unitHecke, ← heckeEquiv_mul, one_mul]

theorem conv_unitHecke {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) :
    heckeConvolution H ρ φ (unitHecke H ρ hH) = φ := by
  obtain ⟨α, rfl⟩ := exists_heckeEquiv_eq hH hφ
  rw [unitHecke, ← heckeEquiv_mul, mul_one]

include hH in
/-- Renard (VI.4.3.1): for `φ ∈ F_x(ρ)` and `ψ ∈ F_y(ρ)`, `φ ∗ ψ ∈ F_{xy}(ρ)` and
`(φ ∗ ψ)(xy) = φ(x) ψ(y)`. -/
theorem inLine_conv {x y : G} {φ ψ : G → Module.End ℂ ρ} (hφ : InLine H ρ x φ)
    (hψ : InLine H ρ y ψ) :
    InLine H ρ (x * y) (heckeConvolution H ρ φ ψ) ∧
      heckeConvolution H ρ φ ψ (x * y) = φ x * ψ y := by
  refine ⟨⟨heckeConvolution_mem hH hφ.1 hψ.1, fun g hg => ?_⟩, ?_⟩
  · by_contra hc
    apply hg
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    by_cases h1 : φ q.out = 0
    · rw [h1, zero_mul]
    by_cases h2 : ψ (q.out⁻¹ * g) = 0
    · rw [h2, mul_zero]
    exfalso
    apply hc
    have m1 := hφ.2 _ h1
    have m3 := hN.conj_mem _ (hψ.2 _ h2) x
    have e : g * (x * y)⁻¹ = (q.out * x⁻¹) * (x * (q.out⁻¹ * g * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact H.mul_mem m1 m3
  · change ∑ᶠ q : G ⧸ H, φ q.out * ψ (q.out⁻¹ * (x * y)) = φ x * ψ y
    rw [finsum_eq_single _ (x : G ⧸ H)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H x
      rw [hk, hecke_mul_right H ρ hφ.1]
      have e : (x * (k : G))⁻¹ * (x * y) = ((k⁻¹ : H) : G) * y := by
        rw [Subgroup.coe_inv]
        group
      rw [e, hecke_mul_left H ρ hψ.1, mul_assoc, ← mul_assoc (ρ.representation k), ← map_mul,
        mul_inv_cancel, map_one, one_mul]
    · intro q hq
      by_cases h1 : φ q.out = 0
      · rw [h1, zero_mul]
      exfalso
      apply hq
      rw [← QuotientGroup.out_eq' q, QuotientGroup.eq]
      have := H.inv_mem (hφ.2 _ h1)
      rw [mul_inv_rev, inv_inv] at this
      exact hN.mem_comm_iff.mp this

/-- A nonzero element of `F_x(ρ)` is invertible, with inverse in `F_{x⁻¹}(ρ)`. -/
theorem exists_conv_inverse {x : G} {φ : G → Module.End ℂ ρ} (hφ : InLine H ρ x φ)
    (h0 : φ ≠ 0) :
    ∃ ψ, InLine H ρ x⁻¹ ψ ∧ heckeConvolution H ρ φ ψ = unitHecke H ρ hH ∧
      heckeConvolution H ρ ψ φ = unitHecke H ρ hH := by
  have hT := isTwistHom_apply hφ.1 x
  obtain ⟨U, h1, h2, -⟩ := exists_inverse_of_bijective (hT.bijective (inLine_apply_ne_zero hφ h0))
  obtain ⟨ψ, hψ, hψx⟩ := exists_inLine_of_isTwistHom (hT.of_inverse h1 h2)
  refine ⟨ψ, hψ, ?_, ?_⟩
  · obtain ⟨hc, hv⟩ := inLine_conv hH hφ hψ
    rw [mul_inv_cancel] at hc hv
    refine eq_of_inLine hc (inLine_unitHecke hH) ?_
    rw [hv, hψx, h1, unitHecke_one]
  · obtain ⟨hc, hv⟩ := inLine_conv hH hψ hφ
    rw [inv_mul_cancel] at hc hv
    refine eq_of_inLine hc (inLine_unitHecke hH) ?_
    rw [hv, hψx, h2, unitHecke_one]

include hH in
/-- Renard (VI.4.3.2): when `G ⧸ H` is commutative, nonzero `φ ∈ F_x(ρ)` and `ψ ∈ F_y(ρ)`
commute up to a nonzero scalar. -/
theorem exists_conv_eq_smul (hrank : Module.rank ℂ ρ ≤ Cardinal.aleph0)
    (hcomm : ∀ a b : G, a * b * (b * a)⁻¹ ∈ H) {x y : G} {φ ψ : G → Module.End ℂ ρ}
    (hφ : InLine H ρ x φ) (hψ : InLine H ρ y ψ) (hφ0 : φ ≠ 0) (hψ0 : ψ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ heckeConvolution H ρ φ ψ = c • heckeConvolution H ρ ψ φ := by
  obtain ⟨h1, v1⟩ := inLine_conv hH hφ hψ
  obtain ⟨h2, v2⟩ := inLine_conv hH hψ hφ
  have hx := (isTwistHom_apply hφ.1 x).bijective (inLine_apply_ne_zero hφ hφ0)
  have hy := (isTwistHom_apply hψ.1 y).bijective (inLine_apply_ne_zero hψ hψ0)
  have n1 : heckeConvolution H ρ φ ψ ≠ 0 := fun h =>
    ne_zero_of_bijective (bijective_mul hx hy) (by rw [← v1, h, Pi.zero_apply])
  have n2 : heckeConvolution H ρ ψ φ ≠ 0 := fun h =>
    ne_zero_of_bijective (bijective_mul hy hx) (by rw [← v2, h, Pi.zero_apply])
  obtain ⟨c, hc⟩ := exists_eq_smul_of_inLine hrank (h2.of_mul_inv_mem (hcomm y x)) h1 n2
  refine ⟨c, fun hc0 => n1 ?_, hc⟩
  rw [hc, hc0, zero_smul]

/-- When `G ⧸ H` has two unique products, a Hecke function with a convolution inverse on the
right lies in a single line: two distinct unique products of the coset supports would both
equal the trivial coset, the support of the unit. -/
theorem exists_inLine_of_conv_eq_unitHecke [TwoUniqueProds (G ⧸ H)]
    {φ ψ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) (hψ : ψ ∈ heckeSubmodule H ρ)
    (h : heckeConvolution H ρ φ ψ = unitHecke H ρ hH) (hφ0 : φ ≠ 0) :
    ∃ x, InLine H ρ x φ := by
  classical
  have key : ∀ a ∈ hφ.2.toFinset, ∀ b ∈ hψ.2.toFinset,
      UniqueMul hφ.2.toFinset hψ.2.toFinset a b → a * b = 1 := by
    intro a ha b hb hu
    obtain ⟨z, hz, hz0⟩ := exists_heckeConvolution_ne_zero_of_uniqueMul hφ hψ ha hb hu
    rw [h] at hz0
    have hzH := (inLine_unitHecke hH).2 z hz0
    rw [inv_one, mul_one] at hzH
    rw [← hz]
    exact (QuotientGroup.eq_one_iff z).mpr hzH
  have hψ0 : ψ ≠ 0 := fun h0 =>
    unitHecke_ne_zero hH (by rw [← h, h0, heckeConvolution_zero_right])
  obtain ⟨y₀, hy₀⟩ : ∃ g, ψ g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hψ0 (funext hc)
  have hT : hψ.2.toFinset.Nonempty := ⟨y₀, hψ.2.mem_toFinset.mpr ⟨y₀, hy₀, rfl⟩⟩
  have hcard : hφ.2.toFinset.card ≤ 1 := by
    by_contra hc
    push Not at hc
    have h1 : 1 < hφ.2.toFinset.card * hψ.2.toFinset.card :=
      lt_of_lt_of_le hc (Nat.le_mul_of_pos_right _ hT.card_pos)
    obtain ⟨p1, hp1, p2, hp2, hne, hu1, hu2⟩ := TwoUniqueProds.uniqueMul_of_one_lt_card h1
    rw [Finset.mem_product] at hp1 hp2
    have e1 := key _ hp1.1 _ hp1.2 hu1
    have e2 := key _ hp2.1 _ hp2.2 hu2
    obtain ⟨h1', h2'⟩ := hu1 hp2.1 hp2.2 (e2.trans e1.symm)
    exact hne (Prod.ext h1'.symm h2'.symm)
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hφ0 (funext hc)
  have hmem : (g₀ : G ⧸ H) ∈ hφ.2.toFinset := hφ.2.mem_toFinset.mpr ⟨g₀, hg₀, rfl⟩
  refine ⟨g₀, hφ, fun g hg => ?_⟩
  have hg' : (g : G ⧸ H) ∈ hφ.2.toFinset := hφ.2.mem_toFinset.mpr ⟨g, hg, rfl⟩
  have e := Finset.card_le_one.mp hcard _ hg' _ hmem
  rw [QuotientGroup.eq] at e
  have := H.inv_mem e
  rw [mul_inv_rev, inv_inv] at this
  exact hN.mem_comm_iff.mp this

/-- Renard (VI.4.3.3): when `G ⧸ H` has two unique products, the units of `H(G, ρ)` are
exactly its nonzero elements lying in some line `F_x(ρ)`. -/
theorem isUnit_iff_inLine [TwoUniqueProds (G ⧸ H)] {φ : G → Module.End ℂ ρ}
    (hφ : φ ∈ heckeSubmodule H ρ) :
    (∃ ψ ∈ heckeSubmodule H ρ, heckeConvolution H ρ φ ψ = unitHecke H ρ hH ∧
        heckeConvolution H ρ ψ φ = unitHecke H ρ hH) ↔
      (φ ≠ 0 ∧ ∃ x, InLine H ρ x φ) := by
  constructor
  · rintro ⟨ψ, hψ, h1, -⟩
    have hφ0 : φ ≠ 0 := fun h0 =>
      unitHecke_ne_zero hH (by rw [← h1, h0, heckeConvolution_zero_left])
    exact ⟨hφ0, exists_inLine_of_conv_eq_unitHecke hH hφ hψ h1 hφ0⟩
  · rintro ⟨h0, x, hx⟩
    obtain ⟨ψ, hψ, h1, h2⟩ := exists_conv_inverse hH hx h0
    exact ⟨ψ, hψ.1, h1, h2⟩

end Unit

end Langlands.CuspidalSupport.NormalHecke
