import Langlands.LinearAlgebra.EpsilonHermitian.LerayInvariant
import Mathlib.Algebra.DirectSum.Module

/-!
# Orthogonal decompositions of an `ε`-Hermitian space

GKT §4.3.1: orthogonal decompositions `W = W₁ ⊕ ⋯ ⊕ W_k` into non-degenerate subspaces, subspaces
"commuting with the decomposition", and Lemma 4.20; Lemma 4.19 (second part).

* `IsOrthogonalDecomposition h W`: the `W i` are pairwise orthogonal, non-degenerate and span `V`;
  then `V` is their internal direct sum (`isInternal`), with components `component i`;
* `CommutesWith W X`: `X = ⨆ i, X ∩ W i` (GKT: "`X` commutes with the decomposition"); intersections
  of commuting subspaces commute, and components of a vector of `X` lie in `X`;
* GKT Lemma 4.20: a Lagrangian commuting with the decomposition meets each piece in a Lagrangian
  of that piece (`isLagrangian_comap`);
* `exists_isometryEquiv_of_decomposition`: isometries between the pieces of two decompositions glue
  to an isometry;
* transport of the notions along the inclusion `U → V` of a non-degenerate subspace.
-/

noncomputable section

namespace Langlands

open Module

/-- A submodule commutes with a family of submodules: it is the sum of its intersections with them
(GKT §4.3.1). -/
def CommutesWith {D V ι : Type*} [DivisionRing D] [AddCommGroup V] [Module D V]
    (W : ι → Submodule D V) (X : Submodule D V) : Prop :=
  ⨆ i, X ⊓ W i = X

namespace EpsilonHermitianForm

open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε' : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V] {h : EpsilonHermitianForm τ ε' V}

/-! ### Transport along the inclusion of a subspace -/

section Transport

variable (U : Submodule D V)

theorem restrict_orthogonal_comap (A : Submodule D V) :
    (h.restrict U).orthogonal (A.comap U.subtype) = (h.orthogonal (A ⊓ U)).comap U.subtype := by
  ext x
  simp only [mem_orthogonal, Submodule.mem_comap, Submodule.coe_subtype, restrict_apply,
    Submodule.mem_inf]
  exact ⟨fun H v ⟨hvA, hvU⟩ => H ⟨v, hvU⟩ hvA, fun H y hy => H y ⟨hy, y.2⟩⟩

theorem restrict_restrict_nondegenerate_iff (A : Submodule D U) :
    ((h.restrict U).restrict A).Nondegenerate ↔ (h.restrict (A.map U.subtype)).Nondegenerate := by
  constructor
  · intro H x hx
    obtain ⟨y, hyA, hyx⟩ := x.2
    have := H ⟨y, hyA⟩ fun z => by
      have := hx ⟨(z : U), ⟨z, z.2, rfl⟩⟩
      simpa [← hyx] using this
    have hy0 : y = 0 := congrArg Subtype.val this
    exact Subtype.ext (by rw [← hyx, hy0]; rfl)
  · intro H x hx
    have := H ⟨((x : U) : V), ⟨x, x.2, rfl⟩⟩ fun z => by
      obtain ⟨w, hwA, hwz⟩ := z.2
      have := hx ⟨w, hwA⟩
      simpa [← hwz] using this
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val this))

theorem isTotallyIsotropic_map_subtype_iff (A : Submodule D U) :
    h.IsTotallyIsotropic (A.map U.subtype) ↔ (h.restrict U).IsTotallyIsotropic A := by
  constructor
  · intro H x hx y hy
    exact H _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  · rintro H _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact H x hx y hy

end Transport

/-! ### Orthogonal decompositions -/

variable {ι : Type*}

variable (h) in
/-- An orthogonal decomposition of the space into non-degenerate subspaces (GKT §4.3.1). -/
structure IsOrthogonalDecomposition (W : ι → Submodule D V) : Prop where
  orthogonal : ∀ i j, i ≠ j → W i ≤ h.orthogonal (W j)
  iSup_eq_top : ⨆ i, W i = ⊤
  nondegenerate : ∀ i, (h.restrict (W i)).Nondegenerate

namespace IsOrthogonalDecomposition

variable {W : ι → Submodule D V} (hW : h.IsOrthogonalDecomposition W)
include hW

theorem apply_eq_zero {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ W i) (hy : y ∈ W j) :
    h x y = 0 :=
  hW.orthogonal i j hij hx y hy

theorem iSupIndep : iSupIndep W := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ j, ⨆ (_ : j ≠ i), W j) ≤ h.orthogonal (W i) :=
    iSup_le fun j => iSup_le fun hj => hW.orthogonal j i hj
  have hxo := hle hx'
  have := hW.nondegenerate i ⟨x, hx⟩ fun y => hxo y y.2
  exact congrArg Subtype.val this

theorem isInternal [DecidableEq ι] : DirectSum.IsInternal W :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hW.iSupIndep hW.iSup_eq_top

variable [DecidableEq ι] [Fintype ι]

/-- The component in `W i` of a vector, for the internal direct sum `V = ⨁ W i`. -/
def component (i : ι) : V →ₗ[D] V :=
  (W i).subtype ∘ₗ DirectSum.component D ι (fun i => W i) i ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW.isInternal).symm.toLinearMap

omit [Fintype ι] in
theorem component_mem (i : ι) (v : V) : hW.component i v ∈ W i :=
  Submodule.coe_mem _

omit [Fintype ι] in
theorem component_of_mem {i j : ι} {v : V} (hv : v ∈ W j) :
    hW.component i v = if i = j then v else 0 := by
  simp only [component, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Submodule.coe_subtype]
  split_ifs with hij
  · subst hij
    change ((((LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW.isInternal).symm v) i :
      W i) : V) = v
    rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem hW.isInternal hv]
  · change ((((LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW.isInternal).symm v) i :
      W i) : V) = 0
    rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne hW.isInternal (Ne.symm hij) hv,
      Submodule.coe_zero]

theorem sum_component (v : V) : ∑ i, hW.component i v = v := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW.isInternal
  have hv : v = DirectSum.coeLinearMap W (e.symm v) := (e.apply_symm_apply v).symm
  conv_rhs => rw [hv, ← DirectSum.sum_univ_of (e.symm v)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DirectSum.coeLinearMap_of]
  rfl

omit [Fintype ι] in
theorem component_apply_self (i : ι) (v : V) : hW.component i (hW.component i v) =
    hW.component i v := by
  rw [hW.component_of_mem (hW.component_mem i v), ite_eq_left rfl]

/-- The form is computed piece by piece. -/
theorem apply_eq_sum_component (v w : V) :
    h v w = ∑ i, h (hW.component i v) (hW.component i w) := by
  conv_lhs => rw [← hW.sum_component v, ← hW.sum_component w]
  rw [h.map_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h.map_sum_right, Finset.sum_eq_single i]
  · intro j _ hji
    exact hW.apply_eq_zero (Ne.symm hji) (hW.component_mem i v) (hW.component_mem j w)
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem nondegenerate_form : h.Nondegenerate := by
  intro v hv
  have hc : ∀ i, hW.component i v = 0 := by
    intro i
    have := hW.nondegenerate i ⟨_, hW.component_mem i v⟩ fun y => by
      have e := hv y
      rw [hW.apply_eq_sum_component, Finset.sum_eq_single i] at e
      · rwa [hW.component_of_mem y.2, ite_eq_left rfl] at e
      · intro j _ hji
        rw [hW.component_of_mem y.2, ite_eq_right hji, map_zero_right]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    exact congrArg Subtype.val this
  rw [← hW.sum_component v]
  simp [hc]

omit [Fintype ι] in
/-- If `X` commutes with the decomposition, the components of its vectors lie in `X`. -/
theorem component_mem_of_commutesWith {X : Submodule D V} (hX : CommutesWith W X) (i : ι)
    {v : V} (hv : v ∈ X) : hW.component i v ∈ X := by
  rw [← hX] at hv
  refine Submodule.iSup_induction (fun j => X ⊓ W j) (motive := fun v => hW.component i v ∈ X)
    hv (fun j x hx => ?_) (by rw [map_zero]; exact X.zero_mem)
    (fun x y hx hy => by rw [map_add]; exact X.add_mem hx hy)
  rw [hW.component_of_mem hx.2]
  split_ifs
  · exact hx.1
  · exact X.zero_mem

/-- A vector lies in a commuting subspace iff all its components do. -/
theorem mem_iff_component_mem {X : Submodule D V} (hX : CommutesWith W X) {v : V} :
    v ∈ X ↔ ∀ i, hW.component i v ∈ X := by
  refine ⟨fun hv i => hW.component_mem_of_commutesWith hX i hv, fun H => ?_⟩
  rw [← hW.sum_component v]
  exact Submodule.sum_mem _ fun i _ => H i

/-- Intersections of commuting subspaces commute. -/
theorem commutesWith_inf {X Y : Submodule D V} (hX : CommutesWith W X) (hY : CommutesWith W Y) :
    CommutesWith W (X ⊓ Y) := by
  apply le_antisymm (iSup_le fun i => inf_le_left)
  intro v ⟨hvX, hvY⟩
  rw [← hW.sum_component v]
  exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i
    ⟨⟨hW.component_mem_of_commutesWith hX i hvX, hW.component_mem_of_commutesWith hY i hvY⟩,
      hW.component_mem i v⟩

omit [Fintype ι] in
/-- The intersection with a piece of a commuting subspace is the image of its component map. -/
theorem component_mem_inf {X : Submodule D V} (hX : CommutesWith W X) (i : ι) {v : V}
    (hv : v ∈ X) : hW.component i v ∈ X ⊓ W i :=
  ⟨hW.component_mem_of_commutesWith hX i hv, hW.component_mem i v⟩

omit [DecidableEq ι] [Fintype ι] in
/-- GKT Lemma 4.20: a Lagrangian commuting with an orthogonal decomposition meets each piece in a
Lagrangian of that piece. -/
theorem isLagrangian_comap {X : Submodule D V} (hX : h.IsLagrangian X) (hXW : CommutesWith W X)
    (i : ι) : (h.restrict (W i)).IsLagrangian (X.comap (W i).subtype) := by
  rw [IsLagrangian, restrict_orthogonal_comap]
  ext w
  simp only [Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · intro hw
    rw [← hX, ← hXW, orthogonal_iSup, Submodule.mem_iInf]
    intro j
    by_cases hji : j = i
    · subst hji; exact hw
    · exact orthogonal_le_orthogonal inf_le_right (hW.orthogonal i j (Ne.symm hji) w.2)
  · intro hw
    exact orthogonal_le_orthogonal inf_le_left (hX.symm.le hw)

end IsOrthogonalDecomposition

/-! ### Gluing isometries along decompositions -/

section Glue

variable [DecidableEq ι] [Fintype ι] {V' : Type*} [AddCommGroup V'] [Module D V']
  {h' : EpsilonHermitianForm τ ε' V'} {W : ι → Submodule D V} {W' : ι → Submodule D V'}

/-- Isometries `φ i : W i ≅ W' i` between the pieces of two orthogonal decompositions glue to an
isometry `V ≅ V'`. -/
theorem exists_isometryEquiv_of_decomposition (hW : h.IsOrthogonalDecomposition W)
    (hW' : h'.IsOrthogonalDecomposition W')
    (φ : ∀ i, IsometryEquiv (h.restrict (W i)) (h'.restrict (W' i))) :
    ∃ Φ : IsometryEquiv h h', ∀ i (w : W i), Φ w = φ i w := by
  set f : V →ₗ[D] V' := ∑ i, (W' i).subtype ∘ₗ (φ i).toLinearEquiv.toLinearMap ∘ₗ
    ((hW.component i).codRestrict (W i) (hW.component_mem i))
  set g : V' →ₗ[D] V := ∑ i, (W i).subtype ∘ₗ (φ i).symm.toLinearEquiv.toLinearMap ∘ₗ
    ((hW'.component i).codRestrict (W' i) (hW'.component_mem i))
  have hc_self : ∀ i (w : W i), (hW.component i).codRestrict (W i) (hW.component_mem i) w = w :=
    fun i w => Subtype.ext (by
      rw [LinearMap.codRestrict_apply, hW.component_of_mem w.2, ite_eq_left rfl])
  have hc_ne : ∀ i j (w : W i), j ≠ i →
      (hW.component j).codRestrict (W j) (hW.component_mem j) w = 0 :=
    fun i j w hji => Subtype.ext (by
      rw [LinearMap.codRestrict_apply, hW.component_of_mem w.2, ite_eq_right hji]; rfl)
  have hc_self' : ∀ i (w : W' i),
      (hW'.component i).codRestrict (W' i) (hW'.component_mem i) w = w :=
    fun i w => Subtype.ext (by
      rw [LinearMap.codRestrict_apply, hW'.component_of_mem w.2, ite_eq_left rfl])
  have hc_ne' : ∀ i j (w : W' i), j ≠ i →
      (hW'.component j).codRestrict (W' j) (hW'.component_mem j) w = 0 :=
    fun i j w hji => Subtype.ext (by
      rw [LinearMap.codRestrict_apply, hW'.component_of_mem w.2, ite_eq_right hji]; rfl)
  have hf_mem : ∀ i (w : W i), f w = φ i w := by
    intro i w
    simp only [f, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [Finset.sum_eq_single i]
    · rw [hc_self]; rfl
    · intro j _ hji
      rw [hc_ne i j w hji, map_zero, map_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hg_mem : ∀ i (w : W' i), g w = (φ i).symm w := by
    intro i w
    simp only [g, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [Finset.sum_eq_single i]
    · rw [hc_self']; rfl
    · intro j _ hji
      rw [hc_ne' i j w hji, map_zero, map_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hgf : ∀ v, g (f v) = v := by
    intro v
    conv_lhs => rw [← hW.sum_component v]
    conv_rhs => rw [← hW.sum_component v]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hf_mem i ⟨_, hW.component_mem i v⟩
    rw [show hW.component i v = ((⟨_, hW.component_mem i v⟩ : W i) : V) from rfl, this,
      hg_mem i, IsometryEquiv.symm_apply_apply]
  have hfg : ∀ v, f (g v) = v := by
    intro v
    conv_lhs => rw [← hW'.sum_component v]
    conv_rhs => rw [← hW'.sum_component v]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hg_mem i ⟨_, hW'.component_mem i v⟩
    rw [show hW'.component i v = ((⟨_, hW'.component_mem i v⟩ : W' i) : V') from rfl, this,
      hf_mem i, IsometryEquiv.apply_symm_apply]
  refine ⟨⟨{ f with invFun := g, left_inv := hgf, right_inv := hfg }, fun v w => ?_⟩, hf_mem⟩
  change h' (f v) (f w) = h v w
  rw [hW.apply_eq_sum_component v w]
  conv_lhs => rw [← hW.sum_component v, ← hW.sum_component w]
  simp only [map_sum, h'.map_sum_left, h'.map_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [show hW.component i v = ((⟨_, hW.component_mem i v⟩ : W i) : V) from rfl,
      show hW.component i w = ((⟨_, hW.component_mem i w⟩ : W i) : V) from rfl, hf_mem, hf_mem]
    exact (φ i).map_app _ _
  · intro j _ hji
    rw [show hW.component i v = ((⟨_, hW.component_mem i v⟩ : W i) : V) from rfl,
      show hW.component j w = ((⟨_, hW.component_mem j w⟩ : W j) : V) from rfl, hf_mem, hf_mem]
    exact hW'.apply_eq_zero (Ne.symm hji) (φ i _).2 (φ j _).2
  · intro hi; exact absurd (Finset.mem_univ i) hi

end Glue

end EpsilonHermitianForm

end Langlands

end
