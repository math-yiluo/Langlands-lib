import Langlands.Geometry.Building.RootValueTorusFieldRestriction
import Langlands.Geometry.Building.RootValuationFieldDescent
import Langlands.Geometry.Building.KPApartment

/-! # Lifting root filtration jumps of non-multipliable relative roots -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- If finitely many extended reals all lie strictly above `r`, then some real `s > r`
lies below all of them. -/
theorem exists_gt_forall_le_of_forall_lt {n : ℕ} (q : Fin n → WithTop ℝ) (r : ℝ)
    (h : ∀ l, (r : WithTop ℝ) < q l) : ∃ s : ℝ, r < s ∧ ∀ l, (s : WithTop ℝ) ≤ q l := by
  classical
  have hlt : (r : WithTop ℝ) < Finset.univ.inf q :=
    (Finset.lt_inf_iff (WithTop.coe_lt_top r)).mpr fun l _ => h l
  obtain ⟨c, hrc, hct⟩ := exists_between hlt
  obtain ⟨s, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hct)
  exact ⟨s, WithTop.coe_lt_coe.mp hrc,
    fun l => hct.le.trans (Finset.inf_le (Finset.mem_univ l))⟩

section Jump

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- `r` is a filtration jump of the character `a` for the family `φ`:
`U_{a,φ,r} ⊈ U_{a,φ,r+} · U_{2a}(k)`, where `U_{a,φ,r+}` is the set of points of `U_a(k)` with
value `> r` and `U_{2a}(k) = doubleRootGroupPoints i a`. For a root `a` and the family `φ = x`
of a point of an apartment, this is KP's condition (Definition 6.3.4) for the affine functional
with derivative `a` and value `r` at `x` to be an affine root. -/
def IsRootFiltrationJump (i : S.toGrp ⟶ G) (φ : RootFunctionFamily S G)
    (a : characterLattice S) (r : ℝ) : Prop :=
  ¬ (rootFiltration i φ a r ⊆
    {g | g ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) < φ a g} *
      (doubleRootGroupPoints i a : Set (rationalPoints G)))

end Jump

section Lift

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private instance rootJumpLiftAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {T : CommGroupScheme (Spec (CommRingCat.of K))}

/-- A root `χ` of the upper torus whose restriction is a positive multiple `m • α_K` of a
relative root `α` with `2α` not a relative root restricts to `α_K` itself: `m = 1`. -/
theorem multiplier_eq_one_of_two_nsmul_not_mem
    {j : T.toGrp ⟶ G_K} (hS : IsSplitTorus S.toGrp)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    {α : characterLattice S} (hα : α ∈ relativeRoots i) (h2α : 2 • α ∉ relativeRoots i)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots j) {m : ℕ} (hm : 0 < m)
    (heq : f ≫ χ = m • (a_K α)) : m = 1 := by
  have : IsAddTorsionFree (TensorProduct ℤ ℚ (characterLattice S)) :=
    IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice S) :=
    Function.Injective.isAddTorsionFree Langlands.LinearAlgebra.RationalSpan.toRat
      hS.character_toRat_injective
  have hmα : m • α ≠ 0 := by
    intro h0
    apply hα.1
    exact IsAddTorsionFree.nsmul_right_injective (Nat.pos_iff_ne_zero.mp hm)
      (h0.trans (smul_zero m).symm)
  have hbase : (a_K (m • α)) = m • (a_K α) := map_nsmul _ m α
  have hne : f ≫ χ ≠ 0 := by
    rw [heq, ← hbase]
    exact (characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr hmα
  have hroot : f ≫ χ ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
    (rootRestriction f j ⟨χ, hχ, hne⟩).property
  rw [hfactor, heq, ← hbase] at hroot
  have hmroot : m • α ∈ relativeRoots i :=
    (mem_roots_baseChange_iff (K := K) G S hS i _).mp hroot
  have hle := RelativeRoot.HasOppositeFactorPairs.nat_multiple_le_two i hS hEbase hα hm hmroot
  interval_cases m
  · rfl
  · exact absurd hmroot h2α

/-- Under the same hypotheses, `2χ` is not a root, so `U_{2χ}(K)` is trivial. -/
theorem doubleRootGroupPoints_eq_bot_of_two_nsmul_not_mem
    {j : T.toGrp ⟶ G_K} (hS : IsSplitTorus S.toGrp)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    {α : characterLattice S} (hα : α ∈ relativeRoots i) (h2α : 2 • α ∉ relativeRoots i)
    {χ : characterLattice T} (heq : f ≫ χ = (a_K α)) :
    doubleRootGroupPoints j χ = ⊥ := by
  have h2χ : 2 • χ ∉ relativeRoots j := by
    intro h2
    have h21 := multiplier_eq_one_of_two_nsmul_not_mem i hS f hfactor hEbase hα h2α h2
      (m := 2) two_pos (by rw [Preadditive.comp_nsmul, heq])
    omega
  unfold doubleRootGroupPoints
  simp [h2χ]

/-- **Root filtration jumps of non-multipliable relative roots lift.** Let `T` be a split
torus of `G_K` through which `S_K` factors, `φ` a root-datum valuation for `(G_K, T)`, and
`ψ` the actual torus-then-field restriction of `φ` to `(G, S)`. If `α` is a relative root
with `2α` not a relative root and `α` has a filtration jump at `r` for `ψ`, that is
`U_{α,ψ,r} ⊈ U_{α,ψ,r+} · U_{2α}(k)`, then some root `χ` of `(G_K, T)` restricting to `α`
has a filtration jump at `r` for `φ`: `U_{χ,φ,r} ⊈ U_{χ,φ,r+} · U_{2χ}(K)`.
Both jumps are expressed with `IsRootFiltrationJump`. -/
theorem exists_rootJump_lift_of_two_nsmul_not_mem
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left] {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    {α : characterLattice S} (hα : α ∈ relativeRoots i) (h2α : 2 • α ∉ relativeRoots i)
    (r : ℝ)
    (hjump : IsRootFiltrationJump i
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) α r) :
    ∃ χ ∈ relativeRoots j, f ≫ χ = (a_K α) ∧ IsRootFiltrationJump j φ χ r := by
  classical
  unfold IsRootFiltrationJump at hjump ⊢
  set ψ := torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f with hψ
  rw [Set.not_subset] at hjump
  obtain ⟨u, hu, hnot⟩ := hjump
  have hdbl : doubleRootGroupPoints i α = ⊥ := by
    unfold doubleRootGroupPoints
    simp [h2α]
  have hupos : ¬ ((r : WithTop ℝ) < ψ α u) := by
    intro hlt
    apply hnot
    refine Set.mem_mul.mpr ⟨u, ⟨hu.1, hlt⟩, 1, ?_, mul_one u⟩
    rw [hdbl]
    exact Subgroup.one_mem _
  have hαK : (a_K α) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS i α).mpr hα
  have hlevel (s : ℝ) : ((s : WithTop ℝ) ≤ ψ α u) ↔
      rationalExtend k K G u ∈ torusRestrictedRootDepthSubgroup hφ f (a_K α) s := by
    have h := Set.ext_iff.mp
      (rootFiltration_torusFieldRestrictedRootFunctionFamily i hS hT hE hφ f hfactor α hα s) u
    exact ⟨fun hs => h.mp ⟨hu.1, hs⟩, fun hs => (h.mpr hs).2⟩
  have hr := (hlevel r).mp hu.2
  have hroot := torusRestrictedRootDepthSubgroup_le_rootGroupPoints (hS.baseChange b) hT hφ f
    _ hαK.1 r hr
  obtain ⟨n, a, m, hinj, hrange, hm⟩ :=
    exists_torusRestrictionRootDepth_enumeration (i := j) hT f (a_K α)
  obtain ⟨X, hX, _⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct
      (hS.baseChange b) hT f j hE (a_K α) hαK.1 a hinj hrange (Over.mk (𝟙 _)) _).mp hroot
  have haroot (l : Fin n) : a l ∈ relativeRoots j := (hrange ▸ Set.mem_range_self l).1
  have hm1 (l : Fin n) : m l = 1 :=
    multiplier_eq_one_of_two_nsmul_not_mem i hS f hfactor hEbase hα h2α (haroot l) (hm l).1
      (hm l).2
  have hbound (s : ℝ) := mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds
    (hS.baseChange b) hT hE hφ f (a_K α) hαK.1 s a m hinj hrange (fun l => (hm l).2) X _ hX
  have hex : ∃ l, ¬ ((r : WithTop ℝ) < φ (a l) (X l).val) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hrs, hs⟩ :=
      exists_gt_forall_le_of_forall_lt (fun l => φ (a l) (X l).val) r hcon
    have hmem := (hbound s).mpr (fun l => by simpa [hm1 l] using hs l)
    exact hupos (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hrs) ((hlevel s).mpr hmem))
  obtain ⟨l, hl⟩ := hex
  have hfl : f ≫ a l = (a_K α) := by rw [(hm l).2, hm1 l, one_smul]
  refine ⟨a l, haroot l, hfl, fun hsub => ?_⟩
  have hXmem : (X l).val ∈ rootFiltration j φ (a l) r :=
    mem_rootFiltration.mpr ⟨(X l).property, by simpa [hm1 l] using (hbound r).mp hr l⟩
  obtain ⟨v, hv, d, hd, hvd⟩ := Set.mem_mul.mp (hsub hXmem)
  rw [doubleRootGroupPoints_eq_bot_of_two_nsmul_not_mem i hS f hfactor hEbase hα h2α hfl] at hd
  have hd1 : d = 1 := Subgroup.mem_bot.mp hd
  rw [hd1, mul_one] at hvd
  exact hl (hvd ▸ hv.2)

end Lift

end Langlands.Geometry.Building
