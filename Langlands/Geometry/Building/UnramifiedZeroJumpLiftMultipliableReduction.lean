import Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonStatement
import Langlands.Geometry.Building.RootJumpLiftNonMultipliable
import Langlands.GroupScheme.Rational.RankOneParabolicCovering
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveProof
import Langlands.GroupScheme.Rational.RootSubgroupCentrality
import Langlands.GroupScheme.Rational.RelativeRootGroupAbsoluteGenerationProof
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.SemigroupCommutatorProof
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof

/-! # Reduction of the multipliable zero-value lift to a field-comparison statement

Over a field extension `K/k`, a filtration jump of the torus restriction of a root-datum
valuation lifts to a filtration jump of some root of the larger torus
(`exists_rootJump_lift_of_torusRestrictedJump`). For `K = F^ur`, this reduces
`UnramifiedZeroJumpLiftMultipliableStatement` to `UnramifiedZeroJumpFieldComparisonStatement`:
a zero-value jump of a relative root `α` for `φ x` is a zero-value jump of `α_K` for the
torus restriction of `x` to `S_K`. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- An ordered product of products `v l * z l` splits as `(∏ v l) * (∏ z l)` when every
`v l` lies in a subgroup `P` whose elements commute with every `z l`. -/
theorem list_ofFn_prod_mul_of_commute {M : Type*} [Group M] (P : Subgroup M) {n : ℕ}
    (v z : Fin n → M) (hv : ∀ l, v l ∈ P) (hz : ∀ l, ∀ w ∈ P, Commute (z l) w) :
    (List.ofFn fun l => v l * z l).prod = (List.ofFn v).prod * (List.ofFn z).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih (fun l => v l.succ) (fun l => z l.succ) (fun l => hv l.succ) (fun l => hz l.succ)]
    have hV : (List.ofFn fun l : Fin n => v l.succ).prod ∈ P :=
      P.list_prod_mem (fun w hw => by
        obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hw
        exact hv l.succ)
    have hc := (hz 0 _ hV).eq
    calc v 0 * z 0 * ((List.ofFn fun l : Fin n => v l.succ).prod *
          (List.ofFn fun l : Fin n => z l.succ).prod)
        = v 0 * (z 0 * (List.ofFn fun l : Fin n => v l.succ).prod) *
            (List.ofFn fun l : Fin n => z l.succ).prod := by simp only [mul_assoc]
      _ = v 0 * ((List.ofFn fun l : Fin n => v l.succ).prod * z 0) *
            (List.ofFn fun l : Fin n => z l.succ).prod := by rw [hc]
      _ = v 0 * (List.ofFn fun l : Fin n => v l.succ).prod *
            (z 0 * (List.ofFn fun l : Fin n => z l.succ).prod) := by simp only [mul_assoc]

section SameField

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {j : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono j.hom.hom.left]
  {φ : RootFunctionFamily T G}

/-- The filtration of a root `χ` of the larger torus at depth `m * s` lies in the restricted
depth subgroup of `β` at depth `s`, when `f ≫ χ = m • β` with `m > 0`. -/
theorem filtrationSubgroup_le_torusRestrictedRootDepthSubgroup
    (hφ : IsRootDatumValuation j φ) (f : S ⟶ T) {χ : characterLattice T}
    (hχ : χ ∈ relativeRoots j) {β : characterLattice S} {m : ℕ} (hm : 0 < m)
    (heq : f ≫ χ = m • β) (s : ℝ) :
    hφ.filtrationSubgroup χ (m * s) ≤ torusRestrictedRootDepthSubgroup hφ f β s :=
  le_iSup_of_le χ (le_iSup_of_le hχ (le_iSup_of_le m (le_iSup_of_le hm
    (le_iSup_of_le heq le_rfl))))

end SameField

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

private instance multipliableLiftAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {T : CommGroupScheme (Spec (CommRingCat.of K))}

/-- A root `χ` of the larger torus restricting to a positive multiple `m • α_K` of a relative
root `α` has `m • α ∈ Φ(S)` and `m ≤ 2`. -/
theorem nsmul_mem_and_le_two_of_restrict_eq
    {j : T.toGrp ⟶ G_K} (hS : IsSplitTorus S.toGrp)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    {α : characterLattice S} (hα : α ∈ relativeRoots i)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots j) {m : ℕ} (hm : 0 < m)
    (heq : f ≫ χ = m • (a_K α)) : m • α ∈ relativeRoots i ∧ m ≤ 2 := by
  have hmα : m • α ≠ 0 := hS.nsmul_ne_zero hα.1 (Nat.pos_iff_ne_zero.mp hm)
  have hbase : (a_K (m • α)) = m • (a_K α) := map_nsmul _ m α
  have hne : f ≫ χ ≠ 0 := by
    rw [heq, ← hbase]
    exact (characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr hmα
  have hroot : f ≫ χ ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
    (rootRestriction f j ⟨χ, hχ, hne⟩).property
  rw [hfactor, heq, ← hbase] at hroot
  have hmroot : m • α ∈ relativeRoots i :=
    (mem_roots_baseChange_iff (K := K) G S hS i _).mp hroot
  exact ⟨hmroot, RelativeRoot.HasOppositeFactorPairs.nat_multiple_le_two i hS hEbase hα hm hmroot⟩

omit [Smooth G.X.hom] in
/-- If a root `χ` of the larger torus restricts to `2 • α_K`, then `U_χ(K)` lies in the
double-root group `U_{2α_K}(K)` of the restricted torus. -/
theorem rootGroupPoints_le_doubleRootGroupPoints_of_restrict_eq_two_nsmul
    {j : T.toGrp ⟶ G_K} (hS : IsSplitTorus S.toGrp) (f : S_K ⟶ T)
    {α : characterLattice S} (hα : α ≠ 0)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots j) (heq : f ≫ χ = 2 • (a_K α)) :
    rootGroupPoints j χ ≤
      doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α) := by
  have hαK : (a_K α) ≠ 0 := (characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr hα
  have hne : f ≫ χ ≠ 0 := by
    rw [heq]
    exact (hS.baseChange b).nsmul_ne_zero hαK two_ne_zero
  have hroot : 2 • (a_K α) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [← heq]
    exact (rootRestriction f j ⟨χ, hχ, hne⟩).property
  unfold doubleRootGroupPoints
  rw [ite_eq_left hroot]
  intro g hg
  have h := RelativeRoot.subgroup_le_subgroup_comp_torusHom f j χ (Over.mk (𝟙 _)) hg
  rw [heq] at h
  exact h

omit [Smooth G.X.hom] in
/-- If a root `χ` of the larger torus restricts to `α_K`, then `U_{2χ}(K)` lies in the
double-root group `U_{2α_K}(K)` of the restricted torus. -/
theorem doubleRootGroupPoints_le_of_restrict_eq
    {j : T.toGrp ⟶ G_K} (hS : IsSplitTorus S.toGrp) (f : S_K ⟶ T)
    {α : characterLattice S} (hα : α ≠ 0)
    {χ : characterLattice T} (heq : f ≫ χ = (a_K α)) :
    doubleRootGroupPoints j χ ≤
      doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α) := by
  by_cases h2χ : 2 • χ ∈ relativeRoots j
  · have hd : doubleRootGroupPoints j χ = rootGroupPoints j (2 • χ) := by
      unfold doubleRootGroupPoints
      rw [ite_eq_left h2χ]
    rw [hd]
    exact rootGroupPoints_le_doubleRootGroupPoints_of_restrict_eq_two_nsmul hS f hα h2χ
      (by rw [Preadditive.comp_nsmul, heq])
  · have hd : doubleRootGroupPoints j χ = ⊥ := by
      unfold doubleRootGroupPoints
      rw [ite_eq_right h2χ]
    rw [hd]
    exact bot_le

/-- The double-root group `U_{2α_K}(K)` of the restricted torus centralizes `U_{α_K}(K)`. -/
theorem doubleRootGroupPoints_commute_of_restrict
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left] (hS : IsSplitTorus S.toGrp)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    {α : characterLattice S} (hα : α ∈ relativeRoots i) :
    ∀ z ∈ doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α),
      ∀ w ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α), Commute z w := by
  intro z hz w hw
  have hαK : (a_K α) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS i α).mpr hα
  by_cases h2 : 2 • (a_K α) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j)
  · have hd : doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α) =
        rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • (a_K α)) := by
      unfold doubleRootGroupPoints
      rw [ite_eq_left h2]
    rw [hd] at hz
    have hhigh : ∀ n : ℕ, 3 ≤ n →
        n • (a_K α) ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
      intro n hn hnroot
      have hbase : (a_K (n • α)) = n • (a_K α) := map_nsmul _ n α
      rw [hfactor, ← hbase] at hnroot
      have hnα := (mem_roots_baseChange_iff (K := K) G S hS i _).mp hnroot
      have hle := RelativeRoot.HasOppositeFactorPairs.nat_multiple_le_two i hS hEbase hα
        (by omega) hnα
      omega
    exact RelativeRoot.double_subgroup_commute_of_noHigherRoots
      RelativeRoot.semigroupRealization RelativeRoot.semigroupCommutator
      RelativeRoot.cyclicRootFunctorComparison inferInstance (hS.baseChange b)
      (CommGroupScheme.groupHom f ≫ j) hαK.1 hhigh (Over.mk (𝟙 _)) z w hz hw
  · have hd : doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α) = ⊥ := by
      unfold doubleRootGroupPoints
      rw [ite_eq_right h2]
    rw [hd] at hz
    rw [Subgroup.mem_bot.mp hz]
    exact Commute.one_left w

/-- **Filtration jumps of a torus restriction lift.** Let `T` be a split torus of `G_K`
through which `S_K` factors, `φ` a root-datum valuation for `(G_K, T)`, and
`ψ = torusRestrictedRootFunctionFamily .. φ f` its torus restriction to `(G_K, S_K)`. If `α`
is a relative root of `(G, S)` and `α_K` has a filtration jump at `r` for `ψ`, that is
`U_{α_K,ψ,r} ⊈ U_{α_K,ψ,r+} · U_{2α_K}(K)`, then some root `χ` of `(G_K, T)` restricting to
`α_K` has a filtration jump at `r` for `φ`. Both jumps are expressed with
`IsRootFiltrationJump`. -/
theorem exists_rootJump_lift_of_torusRestrictedJump
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left] {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    {α : characterLattice S} (hα : α ∈ relativeRoots i) (r : ℝ)
    (hjump : IsRootFiltrationJump (CommGroupScheme.groupHom f ≫ j)
      (torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f) (a_K α) r) :
    ∃ χ ∈ relativeRoots j, f ≫ χ = (a_K α) ∧ IsRootFiltrationJump j φ χ r := by
  classical
  by_contra hno
  push Not at hno
  apply hjump
  intro v hv
  set ψ := torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f with hψ
  have hαK : (a_K α) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS i α).mpr hα
  have hvr : v ∈ torusRestrictedRootDepthSubgroup hφ f (a_K α) r := by
    have h := rootFiltration_torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE
      hφ f (a_K α) hαK r
    rw [h] at hv
    exact hv
  have hroot := torusRestrictedRootDepthSubgroup_le_rootGroupPoints (hS.baseChange b) hT hφ f
    _ hαK.1 r hvr
  obtain ⟨n, a, m, hinj, hrange, hm⟩ :=
    exists_torusRestrictionRootDepth_enumeration (i := j) hT f (a_K α)
  obtain ⟨X, hX, _⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct
      (hS.baseChange b) hT f j hE (a_K α) hαK.1 a hinj hrange (Over.mk (𝟙 _)) _).mp hroot
  have haroot (l : Fin n) : a l ∈ relativeRoots j := (hrange ▸ Set.mem_range_self l).1
  have hbound := (mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds
    (hS.baseChange b) hT hE hφ f (a_K α) hαK.1 r a m hinj hrange (fun l => (hm l).2) X _
      hX).mp hvr
  -- Each coordinate is a point of depth `> r` times a point of `U_{2α_K}(K)`.
  have hcoord : ∀ l, ∃ s : ℝ, r < s ∧
      ∃ w ∈ torusRestrictedRootDepthSubgroup hφ f (a_K α) s,
        ∃ z ∈ doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α),
          (X l).val = w * z := by
    intro l
    obtain ⟨_, hle⟩ :=
      nsmul_mem_and_le_two_of_restrict_eq i hS f hfactor hEbase hα (haroot l) (hm l).1 (hm l).2
    have hm12 : m l = 1 ∨ m l = 2 := by
      have := (hm l).1
      omega
    rcases hm12 with h1 | h2
    · have hfl : f ≫ a l = (a_K α) := by rw [(hm l).2, h1, one_smul]
      have hXmem : (X l).val ∈ rootFiltration j φ (a l) r :=
        mem_rootFiltration.mpr ⟨(X l).property, by simpa [h1] using hbound l⟩
      have hsub := hno (a l) (haroot l) hfl
      unfold IsRootFiltrationJump at hsub
      push Not at hsub
      obtain ⟨w, hw, d, hd, hwd⟩ := Set.mem_mul.mp (hsub hXmem)
      obtain ⟨s, hrs, hs⟩ :=
        exists_gt_forall_le_of_forall_lt (fun _ : Fin 1 => φ (a l) w) r (fun _ => hw.2)
      refine ⟨s, hrs, w, ?_, d, doubleRootGroupPoints_le_of_restrict_eq hS f hα.1 hfl hd,
        hwd.symm⟩
      have hws : w ∈ hφ.filtrationSubgroup (a l) (((1 : ℕ) : ℝ) * s) :=
        mem_rootFiltration.mpr ⟨hw.1, by simpa using hs 0⟩
      exact filtrationSubgroup_le_torusRestrictedRootDepthSubgroup hφ f (haroot l) one_pos
        (by rw [hfl, one_smul]) s hws
    · refine ⟨r + 1, by linarith, 1, Subgroup.one_mem _, (X l).val, ?_, (one_mul _).symm⟩
      exact rootGroupPoints_le_doubleRootGroupPoints_of_restrict_eq_two_nsmul hS f hα.1
        (haroot l) (by rw [(hm l).2, h2]) (X l).property
  choose s hs w hw z hz hwz using hcoord
  obtain ⟨s0, hrs0, hs0⟩ :=
    exists_gt_forall_le_of_forall_lt (fun l => (s l : WithTop ℝ)) r
      (fun l => WithTop.coe_lt_coe.mpr (hs l))
  have hw0 (l : Fin n) : w l ∈ torusRestrictedRootDepthSubgroup hφ f (a_K α) s0 :=
    torusRestrictedRootDepthSubgroup_antitone hφ f (a_K α) (WithTop.coe_le_coe.mp (hs0 l)) (hw l)
  set P := rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α) with hP
  set Z := doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K α) with hZ
  have hcomm := doubleRootGroupPoints_commute_of_restrict i hS f hfactor hEbase hα
  have hwP (l : Fin n) : w l ∈ P :=
    torusRestrictedRootDepthSubgroup_le_rootGroupPoints (hS.baseChange b) hT hφ f _ hαK.1 s0
      (hw0 l)
  have hprod : v = (List.ofFn w).prod * (List.ofFn z).prod := by
    rw [← hX]
    unfold RelativeRoot.rootPointsProduct
    simp_rw [hwz]
    exact list_ofFn_prod_mul_of_commute P w z hwP (fun l y hy => hcomm (z l) (hz l) y hy)
  have hWdepth : (List.ofFn w).prod ∈ torusRestrictedRootDepthSubgroup hφ f (a_K α) s0 :=
    Subgroup.list_prod_mem _ (fun y hy => by
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy
      exact hw0 l)
  have hWP : (List.ofFn w).prod ∈ P :=
    torusRestrictedRootDepthSubgroup_le_rootGroupPoints (hS.baseChange b) hT hφ f _ hαK.1 s0
      hWdepth
  have hZmem : (List.ofFn z).prod ∈ Z :=
    Subgroup.list_prod_mem _ (fun y hy => by
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy
      exact hz l)
  rw [hprod]
  refine Set.mem_mul.mpr ⟨_, ⟨hWP, ?_⟩, _, hZmem, rfl⟩
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hrs0)
    ((le_torusRestrictedRootFunctionFamily_iff (hS.baseChange b) hT hE hφ f (a_K α) hαK _ hWP
      s0).mpr hWdepth)

end Lift

set_option maxHeartbeats 1600000 in
/-- **Reduction of the multipliable zero-value lift.** `UnramifiedZeroJumpFieldComparisonStatement`
implies `UnramifiedZeroJumpLiftMultipliableStatement`: a zero-value jump of `α` for `φ x` is a
zero-value jump of `α_K` for the torus restriction of `x` to `S_K`, which lifts to a root of
`(G_K, T_K)` by `exists_rootJump_lift_of_torusRestrictedJump`. -/
theorem unramifiedZeroJumpLiftMultipliable_of_fieldComparison
    (hcmp : UnramifiedZeroJumpFieldComparisonStatement.{u}) :
    UnramifiedZeroJumpLiftMultipliableStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  intro hE D C hΩ fixed φ x hx α hα _ hjump
  have hEbase : RelativeRoot.HasOppositeFactorPairs iS := fun a ha g hg _ =>
    RelativeRoot.exists_oppositeFactorPair_of_componentReductivity
      RelativeRoot.kernelCentralizerComponentReductive F G hG S iS hiS a ha.1 g hg
  have hfactor : CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  have hK := hcmp F G hG S iS hiS T iT f hf hiT hE D C hΩ x hx (φ x)
    (torusRestrictedRootFunctionFamily
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      (i := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (hiS.isSplitSubtorus.1.baseChange (algebraBaseMap F (inertiaFixedField F)))
      hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f))
    rfl rfl α hα
  have hjK : IsRootFiltrationJump
      (CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
          (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (torusRestrictedRootFunctionFamily
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        (i := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
        (hiS.isSplitSubtorus.1.baseChange (algebraBaseMap F (inertiaFixedField F)))
        hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f))
      (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) 0 := by
    rw [hfactor]
    exact hK.mp hjump
  exact exists_rootJump_lift_of_torusRestrictedJump (K := inertiaFixedField F) iS
    hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
    _ hfactor hEbase hα 0 hjK

end Langlands.Geometry.Building
