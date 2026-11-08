import Langlands.Geometry.Building.RootDepthTorusRestriction

/-! # Actual scalar root functions under restriction between split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

/-- A finite family of positively scaled bounds, at least one finite, has an
attained real threshold. Top-valued bounds impose no restriction. -/
private theorem exists_real_threshold_of_finite_bounds
    {n : ℕ} (q : Fin n → WithTop ℝ) (m : Fin n → ℕ)
    (hm : ∀ j, 0 < m j) (hq : ∃ j, q j ≠ ⊤) :
    ∃ t : ℝ, ∀ r : ℝ, (∀ j, ((m j * r : ℝ) : WithTop ℝ) ≤ q j) ↔ r ≤ t := by
  classical
  let J := {j : Fin n // q j ≠ ⊤}
  have hv : ∀ j : J, ∃ v : ℝ, (v : WithTop ℝ) = q j :=
    fun j => WithTop.ne_top_iff_exists.mp j.property
  choose v hv using hv
  let b : J → ℝ := fun j => v j / m j.val
  have hJ : (Set.univ : Set J).Nonempty := by
    obtain ⟨j, hj⟩ := hq
    exact ⟨⟨j, hj⟩, Set.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Set.exists_min_image Set.univ b (Set.toFinite _) hJ
  refine ⟨b j, fun r => ⟨fun hr => ?_, fun hr l => ?_⟩⟩
  · have h := hr j.val
    rw [← hv j, WithTop.coe_le_coe] at h
    exact (le_div_iff₀ (by exact_mod_cast hm j.val : (0 : ℝ) < m j.val)).mpr
      (by simpa only [mul_comm] using h)
  · by_cases hl : q l = ⊤
    · rw [hl]; exact le_top
    · let l' : J := ⟨l, hl⟩
      rw [← hv l', WithTop.coe_le_coe]
      have hrl : r ≤ b l' := hr.trans (hj l' (Set.mem_univ _))
      have hmul := (le_div_iff₀
        (by exact_mod_cast hm l : (0 : ℝ) < m l)).mp hrl
      simpa only [mul_comm] using hmul

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {φ : RootFunctionFamily T G} [Smooth G.X.hom]

/-- Membership at a lower depth is exactly the corresponding bound on every
fixed intrinsic upper-root coordinate. -/
theorem mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (hα : α ≠ 0) (r : ℝ)
    {n : ℕ} (a : Fin n → characterLattice T) (m : Fin n → ℕ)
    (hinj : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.semigroupIndivisibleRoots i
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail α 1)))
    (hrestrict : ∀ j, f ≫ a j = m j • α)
    (X : ∀ j, (RelativeRoot.subgroup i (a j)).carrier (Over.mk (𝟙 _)))
    (g : rationalPoints G)
    (hX : RelativeRoot.rootPointsProduct i a (Over.mk (𝟙 _)) X = g) :
    g ∈ torusRestrictedRootDepthSubgroup hφ f α r ↔
      ∀ j, ((m j * r : ℝ) : WithTop ℝ) ≤ φ (a j) (X j).val := by
  constructor
  · intro hg
    have hlow := torusRestrictedRootDepthSubgroup_le_rootGroupPoints
      hS hT hφ f α hα r hg
    obtain ⟨Z, hZ, hZu⟩ :=
      (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct
        hS hT f i hE α hα a hinj hrange (Over.mk (𝟙 _)) g).mp hlow
    obtain ⟨y, hy, _⟩ :=
      (mem_torusRestrictedRootDepthSubgroup_iff_existsUnique hS hT hE hφ f α hα r
        a m hinj hrange hrestrict g).mp hg
    let Y : ∀ j, (RelativeRoot.subgroup i (a j)).carrier (Over.mk (𝟙 _)) :=
      fun j => ⟨(y j).val, (y j).property.1⟩
    have hY : RelativeRoot.rootPointsProduct i a (Over.mk (𝟙 _)) Y = g := hy
    have hYX : Y = X := (hZu Y hY).trans (hZu X hX).symm
    intro j
    have heq : (y j).val = (X j).val := congrArg
      (fun z : (RelativeRoot.subgroup i (a j)).carrier (Over.mk (𝟙 _)) => z.val)
      (congrFun hYX j)
    rw [← heq]
    exact (y j).property.2
  · intro hb
    let y : ∀ j, rootFiltration i φ (a j) (m j * r) :=
      fun j => ⟨(X j).val, (X j).property, hb j⟩
    have hy : g ∈ orderedRootFiltrationProduct i φ a (fun j => m j * r) := ⟨y, hX⟩
    rwa [orderedRootFiltrationProduct_eq_torusRestrictedRootDepthSubgroup
      hS hT hE hφ f α hα r a m hrange hrestrict] at hy

/-- Every nonidentity point of the actual lower root group has an attained
finite cutoff in the canonical descending filtration. -/
theorem exists_torusRestrictedRootDepth_threshold
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (hα : α ≠ 0)
    (g : rationalPoints G)
    (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α) (hg1 : g ≠ 1) :
    ∃ t : ℝ, ∀ r : ℝ, g ∈ torusRestrictedRootDepthSubgroup hφ f α r ↔ r ≤ t := by
  classical
  obtain ⟨n, a, m, hinj, hrange, hm⟩ :=
    exists_torusRestrictionRootDepth_enumeration (i := i) hT f α
  obtain ⟨X, hX, _⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct
      hS hT f i hE α hα a hinj hrange (Over.mk (𝟙 _)) g).mp hg
  have hfinite : ∃ j, φ (a j) (X j).val ≠ ⊤ := by
    by_contra h
    push Not at h
    have hone (j : Fin n) : (X j).val = 1 := by
      have hroot : a j ∈ relativeRoots i := (hrange ▸ Set.mem_range_self j).1
      exact (hφ.eq_top_iff (a j) hroot (X j).val (X j).property).mp (h j)
    apply hg1
    rw [← hX]
    unfold RelativeRoot.rootPointsProduct
    simp only [hone, List.ofFn_const, List.prod_replicate, one_pow]
  obtain ⟨t, ht⟩ := exists_real_threshold_of_finite_bounds
    (fun j => φ (a j) (X j).val) m (fun j => (hm j).1) hfinite
  refine ⟨t, fun r => ?_⟩
  rw [mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds
    hS hT hE hφ f α hα r a m hinj hrange (fun j => (hm j).2) X g hX]
  exact ht r

/-- The attained cutoff is uniquely determined by the actual filtration, so it
is independent of all coordinate choices. -/
theorem existsUnique_torusRestrictedRootDepth_threshold
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (hα : α ≠ 0)
    (g : rationalPoints G)
    (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α) (hg1 : g ≠ 1) :
    ∃! t : ℝ, ∀ r : ℝ, g ∈ torusRestrictedRootDepthSubgroup hφ f α r ↔ r ≤ t := by
  obtain ⟨t, ht⟩ := exists_torusRestrictedRootDepth_threshold hS hT hE hφ f α hα g hg hg1
  refine ⟨t, ht, fun s hs => le_antisymm ?_ ?_⟩
  · exact (ht s).mp ((hs s).mpr le_rfl)
  · exact (hs t).mp ((ht t).mpr le_rfl)

open Classical in
/-- The actual lower scalar family: the canonical attained cutoff on nonidentity
root points, and top at the identity, off the root group, and off the roots. -/
def torusRestrictedRootFunctionFamily
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) : RootFunctionFamily S G where
  toFun α g :=
    if h : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i) ∧
        g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α ∧ g ≠ 1 then
      ((Classical.choose (exists_torusRestrictedRootDepth_threshold
        hS hT hE hφ f α h.1.1 g h.2.1 h.2.2) : ℝ) : WithTop ℝ)
    else ⊤

@[simp] theorem torusRestrictedRootFunctionFamily_one
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f α 1 = ⊤ := by
  classical
  simp [torusRestrictedRootFunctionFamily]

/-- The lower scalar family has the prescribed normalization off actual roots. -/
theorem torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∉ relativeRoots (CommGroupScheme.groupHom f ≫ i)) (g : rationalPoints G) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f α g = ⊤ := by
  classical
  simp [torusRestrictedRootFunctionFamily, hα]

/-- The lower scalar family is top off the corresponding actual root group. -/
theorem torusRestrictedRootFunctionFamily_eq_top_of_not_mem
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (g : rationalPoints G)
    (hg : g ∉ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f α g = ⊤ := by
  classical
  simp [torusRestrictedRootFunctionFamily, hg]

/-- On an actual root group only the identity has top value. -/
theorem torusRestrictedRootFunctionFamily_eq_top_iff
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (g : rationalPoints G) (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f α g = ⊤ ↔ g = 1 := by
  classical
  by_cases hg1 : g = 1
  · subst g
    simp only [torusRestrictedRootFunctionFamily_one]
  · simp [torusRestrictedRootFunctionFamily, hα, hg, hg1]

/-- Each finite scalar lower bound is exactly membership in the canonical
multiplier-scaled subgroup, including at the attained endpoint. -/
theorem le_torusRestrictedRootFunctionFamily_iff
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (g : rationalPoints G) (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α)
    (r : ℝ) :
    (r : WithTop ℝ) ≤ torusRestrictedRootFunctionFamily hS hT hE hφ f α g ↔
      g ∈ torusRestrictedRootDepthSubgroup hφ f α r := by
  classical
  by_cases hg1 : g = 1
  · subst g
    simp only [torusRestrictedRootFunctionFamily_one, le_top, Subgroup.one_mem]
  · change (r : WithTop ℝ) ≤ (if h : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i) ∧
        g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α ∧ g ≠ 1 then
      ((Classical.choose (exists_torusRestrictedRootDepth_threshold
        hS hT hE hφ f α h.1.1 g h.2.1 h.2.2) : ℝ) : WithTop ℝ) else ⊤) ↔ _
    rw [dite_eq_left ⟨hα, hg, hg1⟩, WithTop.coe_le_coe]
    exact (Classical.choose_spec (exists_torusRestrictedRootDepth_threshold
      hS hT hE hφ f α hα.1 g hg hg1) r).symm

/-- The lower scalar family recovers the canonical filtration on every actual
lower root. Thus all its finite level sets are actual subgroups. -/
theorem rootFiltration_torusRestrictedRootFunctionFamily
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)) (r : ℝ) :
    rootFiltration (CommGroupScheme.groupHom f ≫ i)
        (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r =
      (torusRestrictedRootDepthSubgroup hφ f α r : Set (rationalPoints G)) := by
  ext g
  constructor
  · rintro ⟨hg, hr⟩
    exact (le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hg r).mp hr
  · intro hr
    have hg := torusRestrictedRootDepthSubgroup_le_rootGroupPoints
      hS hT hφ f α hα.1 r hr
    exact ⟨hg, (le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hg r).mpr hr⟩

/-- V1 identity closure for the actual lower scalar family. -/
theorem torusRestrictedRootFunctionFamily_one_mem
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)) (r : ℝ) :
    (1 : rationalPoints G) ∈ rootFiltration (CommGroupScheme.groupHom f ≫ i)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r := by
  rw [rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f α hα r]
  exact Subgroup.one_mem _

/-- V1 multiplication closure for the actual lower scalar family. -/
theorem torusRestrictedRootFunctionFamily_mul_mem
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)) (r : ℝ)
    (g h : rationalPoints G)
    (hg : g ∈ rootFiltration (CommGroupScheme.groupHom f ≫ i)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r)
    (hh : h ∈ rootFiltration (CommGroupScheme.groupHom f ≫ i)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r) :
    g * h ∈ rootFiltration (CommGroupScheme.groupHom f ≫ i)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r := by
  rw [rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f α hα r] at *
  exact Subgroup.mul_mem _ hg hh

/-- V1 inversion closure for the actual lower scalar family. -/
theorem torusRestrictedRootFunctionFamily_inv_mem
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)) (r : ℝ)
    (g : rationalPoints G)
    (hg : g ∈ rootFiltration (CommGroupScheme.groupHom f ≫ i)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r) :
    g⁻¹ ∈ rootFiltration (CommGroupScheme.groupHom f ≫ i)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r := by
  rw [rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f α hα r] at *
  exact Subgroup.inv_mem _ hg

/-- Normalization and the canonical filtration determine the scalar family
uniquely, without an enumeration or cocharacter choice. -/
theorem torusRestrictedRootFunctionFamily_unique
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (ψ : RootFunctionFamily S G)
    (hroots : ∀ α ∉ relativeRoots (CommGroupScheme.groupHom f ≫ i), ∀ g, ψ α g = ⊤)
    (hoff : ∀ α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i),
      ∀ g ∉ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α, ψ α g = ⊤)
    (hfil : ∀ α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i), ∀ r : ℝ,
      rootFiltration (CommGroupScheme.groupHom f ≫ i) ψ α r =
        (torusRestrictedRootDepthSubgroup hφ f α r : Set (rationalPoints G))) :
    ψ = torusRestrictedRootFunctionFamily hS hT hE hφ f := by
  classical
  ext α g
  by_cases hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)
  · by_cases hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α
    · apply WithTop.eq_of_forall_coe_le_iff
      intro r
      have hlevels := Set.ext_iff.mp (hfil α hα r) g
      simp only [mem_rootFiltration, hg, true_and, SetLike.mem_coe] at hlevels
      exact hlevels.trans
        (le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hg r).symm
    · rw [hoff α hα g hg,
        torusRestrictedRootFunctionFamily_eq_top_of_not_mem hS hT hE hφ f α g hg]
  · rw [hroots α hα g,
      torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots hS hT hE hφ f α hα g]

end Langlands.Geometry.Building
