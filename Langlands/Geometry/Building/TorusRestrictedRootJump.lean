import Langlands.Geometry.Building.RootJumpLiftNonMultipliable
import Langlands.Geometry.Building.RootValueTorusRestriction
import Langlands.GroupScheme.Rational.RootSubgroupCentrality
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.SemigroupCommutatorProof
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion
import Langlands.GroupScheme.Rational.RelativeRootGroupAbsoluteGenerationProof

/-! # Root filtration jumps pass from a root of a larger split torus to its restriction -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Multiplying an ordered product on the right by an element that commutes with all of its
factors multiplies one chosen factor instead. -/
theorem list_ofFn_prod_mul_eq_prod_update {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (X : Fin n → M) (l : Fin n) (y : M), (∀ k, Commute y (X k)) →
      (List.ofFn X).prod * y = (List.ofFn (Function.update X l (X l * y))).prod
  | 0, _, l, _, _ => l.elim0
  | n + 1, X, l, y, hy => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    cases l using Fin.cases with
    | zero =>
      have htail : (fun i : Fin n => Function.update X 0 (X 0 * y) i.succ) =
          fun i => X i.succ := by
        funext i
        exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
      rw [htail, Function.update_self]
      have hc : Commute y (List.ofFn fun i : Fin n => X i.succ).prod := by
        apply Commute.list_prod_right
        intro z hz
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
        exact hy i.succ
      rw [mul_assoc, ← hc.eq, ← mul_assoc]
    | succ l' =>
      have h0 : Function.update X l'.succ (X l'.succ * y) 0 = X 0 :=
        Function.update_of_ne (Fin.succ_ne_zero l').symm _ _
      have htail : (fun i : Fin n => Function.update X l'.succ (X l'.succ * y) i.succ) =
          Function.update (fun i => X i.succ) l' (X l'.succ * y) := by
        funext i
        by_cases hi : i = l'
        · subst hi
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hi, Function.update_of_ne
            (fun h => hi (Fin.succ_injective _ h))]
      rw [h0, htail, mul_assoc]
      congr 1
      exact list_ofFn_prod_mul_eq_prod_update (fun i => X i.succ) l' y (fun k => hy k.succ)

/-- An ordered product whose factors are all `1` except one factor `u` equals `u`. -/
theorem list_ofFn_prod_update_one {M : Type*} [Monoid M] {n : ℕ} (l : Fin n) (u : M) :
    (List.ofFn (Function.update (1 : Fin n → M) l u)).prod = u := by
  have h := list_ofFn_prod_mul_eq_prod_update (1 : Fin n → M) l u
    (fun k => Commute.one_right u)
  have h1 : (List.ofFn (1 : Fin n → M)).prod = 1 := by
    rw [show (1 : Fin n → M) = fun _ => 1 from rfl, List.ofFn_const, List.prod_replicate,
      one_pow]
  rw [h1, one_mul, Pi.one_apply, one_mul] at h
  exact h.symm

section Restriction

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {j : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono j.hom.hom.left] [Smooth G.X.hom]
  {φ : RootFunctionFamily T G}

/-- Distinct natural multiples of a nonzero character of a split torus are distinct. -/
theorem nsmul_injective_of_isSplitTorus (hS : IsSplitTorus S.toGrp)
    {α : characterLattice S} (hα : α ≠ 0) {n m : ℕ} (h : n • α = m • α) : n = m := by
  obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos hα
  have hp := congrArg (fun c => latticePairing S c ν) h
  simp only [map_nsmul, LinearMap.smul_apply, hν, nsmul_eq_mul] at hp
  have hD' : ((D : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  exact_mod_cast mul_right_cancel₀ hD' hp

omit [Mono j.hom.hom.left] [Smooth G.X.hom] in
/-- A root of the larger torus restricting to `α` itself is indivisible in the restriction
fibre of `α`. -/
theorem mem_semigroupIndivisibleRoots_of_restrict_eq
    (hS : IsSplitTorus S.toGrp) (f : S ⟶ T) {α : characterLattice S} (hα : α ≠ 0)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots j) (hfχ : f ≫ χ = α) :
    χ ∈ RelativeRoot.semigroupIndivisibleRoots j
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail α 1)) := by
  refine ⟨hχ, ⟨1, le_rfl, one_pos, by rw [one_smul]; exact hfχ.symm⟩, ?_⟩
  intro b _ hbA m hm hmb
  obtain ⟨p, _, hp, hpb⟩ := hbA
  change p • α = f ≫ b at hpb
  have hmul : (m * p) • α = 1 • α := by
    rw [mul_nsmul', hpb, ← Preadditive.comp_nsmul, hmb, hfχ, one_smul]
  have h1 := nsmul_injective_of_isSplitTorus hS hα hmul
  have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right h1
  omega

/-- **Moving a doubled-root factor into ordered coordinates.** Let `a` enumerate the roots of
the larger torus that are indivisible in the restriction fibre of `α`, let `a l = χ` with
`f ≫ χ = α`, and assume no multiple `n • α` with `n ≥ 3` is a root of the restricted torus.
Right multiplication of an ordered product `∏ X k` (with `X k ∈ U_{a k}`) by a point of
`U_{2α}` gives another ordered product `∏ X' k` with `X' k ∈ U_{a k}`, whose `l`-th factor
differs from `X l` by a point of `U_{2χ}` (trivial if `2χ` is not a root). -/
theorem exists_rootCoordinates_mul_doubleRootGroupPoints
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (f : S ⟶ T) {α : characterLattice S}
    (hα : α ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • α ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    {n : ℕ} (a : Fin n → characterLattice T)
    (hrange : Set.range a = RelativeRoot.semigroupIndivisibleRoots j
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail α 1)))
    {χ : characterLattice T} (hfχ : f ≫ χ = α) (l : Fin n) (hl : a l = χ)
    {w : rationalPoints G}
    (hw : w ∈ doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) α)
    (X : Fin n → rationalPoints G) (hX : ∀ k, X k ∈ rootGroupPoints j (a k)) :
    ∃ X' : Fin n → rationalPoints G, (∀ k, X' k ∈ rootGroupPoints j (a k)) ∧
      (List.ofFn X').prod = (List.ofFn X).prod * w ∧
      ∃ d ∈ doubleRootGroupPoints j χ, X' l = X l * d := by
  classical
  by_cases h2 : 2 • α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j)
  swap
  · have hw1 : w = 1 := by
      unfold doubleRootGroupPoints at hw
      simp only [h2, ↓reduceIte] at hw
      exact Subgroup.mem_bot.mp hw
    exact ⟨X, hX, by rw [hw1, mul_one], 1, Subgroup.one_mem _, (mul_one _).symm⟩
  have hw' : w ∈ (RelativeRoot.subgroup (CommGroupScheme.groupHom f ≫ j) (2 • α)).carrier
      (Over.mk (𝟙 _)) := by
    unfold doubleRootGroupPoints at hw
    simp only [h2, ↓reduceIte] at hw
    exact hw
  rw [RelativeRoot.subgroup_comp_torusHom_carrier_eq_iSup hS hT f j hE (2 • α) h2.1
    (Over.mk (𝟙 _))] at hw'
  -- every coordinate group lies in the restricted root group of `α`
  have hacoord (k : Fin n) : rootGroupPoints j (a k) ≤
      rootGroupPoints (CommGroupScheme.groupHom f ≫ j) α := by
    have hk : a k ∈ RelativeRoot.semigroupIndivisibleRoots j
        (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail α 1)) :=
      hrange ▸ Set.mem_range_self k
    obtain ⟨p, _, hp, hpk⟩ := hk.2.1
    exact RelativeRoot.subgroup_le_subgroup_comp_torusHom_of_nsmul f j hp hpk.symm
      (Over.mk (𝟙 _))
  -- the generator step
  have hgen : ∀ (c : {c : characterLattice T |
      c ∈ relativeRoots j ∧ f ≫ c ∈ RelativeRoot.cyclicTail (2 • α) 1})
      (y : rationalPoints G), y ∈ (RelativeRoot.subgroup j c.val).carrier (Over.mk (𝟙 _)) →
      ∀ X : Fin n → rationalPoints G, (∀ k, X k ∈ rootGroupPoints j (a k)) →
      ∃ X' : Fin n → rationalPoints G, (∀ k, X' k ∈ rootGroupPoints j (a k)) ∧
        (List.ofFn X').prod = (List.ofFn X).prod * y ∧
        ∃ d ∈ doubleRootGroupPoints j χ, X' l = X l * d := by
    rintro ⟨c, hc, hcA⟩ y hy X hX
    obtain ⟨q, _, hq, hqc⟩ := hcA
    -- `y` lies in the restricted doubled root group, hence is central in `U_α`
    have hy2 : y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • α) :=
      RelativeRoot.subgroup_le_subgroup_comp_torusHom_of_nsmul f j hq hqc.symm
        (Over.mk (𝟙 _)) hy
    have hcomm (k : Fin n) : Commute y (X k) :=
      RelativeRoot.double_subgroup_commute_of_noHigherRoots
        RelativeRoot.semigroupRealization RelativeRoot.semigroupCommutator
        RelativeRoot.cyclicRootFunctorComparison inferInstance hS
        (CommGroupScheme.groupHom f ≫ j) hα hhigh (Over.mk (𝟙 _)) y (X k) hy2
        (hacoord k (hX k))
    -- `c` is a positive multiple of an indivisible root of the fibre of `α`
    have hcF : c ∈ RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail α 1) :=
      ⟨q * 2, by omega, by omega, by rw [mul_nsmul', hqc]; rfl⟩
    obtain ⟨b, hb, p, _, hp, hpb⟩ :=
      RelativeRoot.exists_semigroupIndivisibleRoot_ray j hT hE _ hc hcF
    obtain ⟨kk, hkk⟩ : b ∈ Set.range a := by rw [hrange]; exact hb
    have hyk : y ∈ rootGroupPoints j (a kk) := by
      rw [hkk]
      exact RelativeRoot.subgroup_nsmul_le j b hp (Over.mk (𝟙 _)) (hpb ▸ hy)
    refine ⟨Function.update X kk (X kk * y), fun k' => ?_,
      (list_ofFn_prod_mul_eq_prod_update X kk y hcomm).symm, ?_⟩
    · by_cases hk' : k' = kk
      · subst hk'
        rw [Function.update_self]
        exact Subgroup.mul_mem _ (hX k') hyk
      · rw [Function.update_of_ne hk']
        exact hX k'
    · by_cases hkl : kk = l
      · subst hkl
        -- here `c = p • χ` and `p = 2`
        have hbχ : b = χ := hkk.symm.trans hl
        subst hbχ
        have hpq : p = q * 2 := by
          apply nsmul_injective_of_isSplitTorus hS hα
          rw [← hfχ, ← Preadditive.comp_nsmul, hpb, ← hqc, hfχ, mul_nsmul']
        have hproot : p • b ∈ relativeRoots j := hpb ▸ hc
        have hp2 : p = 2 := by
          rcases hE.eq_one_or_two_of_nsmul_mem j hT hproot with h | h <;> omega
        subst hp2
        refine ⟨y, ?_, by rw [Function.update_self]⟩
        unfold doubleRootGroupPoints
        simp only [hproot, ↓reduceIte]
        exact hpb ▸ hy
      · refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [Function.update_of_ne (Ne.symm hkl), mul_one]
  -- induction over the generated subgroup
  revert X
  refine Subgroup.iSup_induction _ hw' (C := fun w => ∀ X : Fin n → rationalPoints G,
      (∀ k, X k ∈ rootGroupPoints j (a k)) →
      ∃ X' : Fin n → rationalPoints G, (∀ k, X' k ∈ rootGroupPoints j (a k)) ∧
        (List.ofFn X').prod = (List.ofFn X).prod * w ∧
        ∃ d ∈ doubleRootGroupPoints j χ, X' l = X l * d) hgen ?_ ?_
  · intro X hX
    exact ⟨X, hX, (mul_one _).symm, 1, Subgroup.one_mem _, (mul_one _).symm⟩
  · intro x y hx hy X hX
    obtain ⟨X₁, hX₁, hprod₁, d₁, hd₁, hl₁⟩ := hx X hX
    obtain ⟨X₂, hX₂, hprod₂, d₂, hd₂, hl₂⟩ := hy X₁ hX₁
    refine ⟨X₂, hX₂, by rw [hprod₂, hprod₁, mul_assoc], d₁ * d₂, Subgroup.mul_mem _ hd₁ hd₂,
      by rw [hl₂, hl₁, mul_assoc]⟩

/-- **Root filtration jumps pass to the restricted torus.** Let `S → T` be split tori acting
on `G` through `f` and `j`, `φ` a root-datum valuation for `(G, T)` and `ψ` its restriction
`torusRestrictedRootFunctionFamily` to `(G, S)`. Let `α` be a root of `(G, S)` such that no
multiple `n • α` with `n ≥ 3` is a root, and `χ` a root of `(G, T)` with `f ≫ χ = α`. If `χ`
has a filtration jump at `r` for `φ`, that is `U_{χ,φ,r} ⊈ U_{χ,φ,r+} · U_{2χ}`, then `α` has
a filtration jump at `r` for `ψ`: `U_{α,ψ,r} ⊈ U_{α,ψ,r+} · U_{2α}`. -/
theorem isRootFiltrationJump_torusRestricted_of_isRootFiltrationJump
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S ⟶ T) {α : characterLattice S}
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • α ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots j) (hfχ : f ≫ χ = α) (r : ℝ)
    (hjump : IsRootFiltrationJump j φ χ r) :
    IsRootFiltrationJump (CommGroupScheme.groupHom f ≫ j)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r := by
  classical
  have hα0 : α ≠ 0 := hα.1
  unfold IsRootFiltrationJump at hjump ⊢
  rw [Set.not_subset] at hjump
  obtain ⟨u, hu, hnot⟩ := hjump
  intro hsub
  apply hnot
  -- `u` lies in the restricted filtration at `r`
  have huD : u ∈ torusRestrictedRootDepthSubgroup hφ f α r := by
    have hle : hφ.filtrationSubgroup χ (((1 : ℕ) : ℝ) * r) ≤
        torusRestrictedRootDepthSubgroup hφ f α r :=
      le_iSup_of_le χ (le_iSup_of_le hχ (le_iSup_of_le 1 (le_iSup_of_le one_pos
        (le_iSup_of_le (by rw [one_smul, hfχ]) le_rfl))))
    apply hle
    change u ∈ rootFiltration j φ χ (((1 : ℕ) : ℝ) * r)
    rw [Nat.cast_one, one_mul]
    exact hu
  have huα : u ∈ rootFiltration (CommGroupScheme.groupHom f ≫ j)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) α r := by
    rw [rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f α hα r]
    exact huD
  obtain ⟨h, ⟨hhU, hhpos⟩, w, hw, hhw⟩ := Set.mem_mul.mp (hsub huα)
  -- an enumeration of the indivisible roots of the fibre, and the index of `χ`
  obtain ⟨n, a, m, hinj, hrange, hm⟩ :=
    exists_torusRestrictionRootDepth_enumeration (i := j) hT f α
  obtain ⟨l, hl⟩ : χ ∈ Set.range a := by
    rw [hrange]
    exact mem_semigroupIndivisibleRoots_of_restrict_eq hS f hα0 hχ hfχ
  have hml : m l = 1 := by
    apply nsmul_injective_of_isSplitTorus hS hα0
    rw [← (hm l).2, hl, hfχ, one_smul]
  -- the coordinates of `h`
  obtain ⟨Xs, hXs, -⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct
      hS hT f j hE α hα0 a hinj hrange (Over.mk (𝟙 _)) h).mp hhU
  -- the `χ`-coordinate of `h` has value `> r`
  obtain ⟨c, hrc, hch⟩ := exists_between hhpos
  obtain ⟨s, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hch)
  have hrs : r < s := WithTop.coe_lt_coe.mp hrc
  have hhs : h ∈ torusRestrictedRootDepthSubgroup hφ f α s :=
    (le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα h hhU s).mp hch.le
  have hXl : ((s : ℝ) : WithTop ℝ) ≤ φ (a l) (Xs l).val := by
    have hb := (mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds hS hT hE hφ f α
      hα0 s a m hinj hrange (fun k => (hm k).2) Xs h hXs).mp hhs l
    rwa [hml, Nat.cast_one, one_mul] at hb
  -- move `w` into the coordinates
  obtain ⟨X', hX', hprod, d, hd, hX'l⟩ :=
    exists_rootCoordinates_mul_doubleRootGroupPoints hS hT hE f hα0 hhigh a hrange hfχ l hl
      hw (fun k => (Xs k).val) (fun k => (Xs k).property)
  have hXs' : (List.ofFn fun k => (Xs k).val).prod = h := hXs
  have hprod' : (List.ofFn X').prod = u := by
    rw [hprod, hXs', hhw]
  -- uniqueness of coordinates of `u`
  have huU : u ∈ (RelativeRoot.subgroup (CommGroupScheme.groupHom f ≫ j) α).carrier
      (Over.mk (𝟙 _)) := huα.1
  obtain ⟨Z, -, hZu⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct
      hS hT f j hE α hα0 a hinj hrange (Over.mk (𝟙 _)) u).mp huU
  let Y₁ : ∀ k, (RelativeRoot.subgroup j (a k)).carrier (Over.mk (𝟙 _)) :=
    fun k => ⟨X' k, hX' k⟩
  have hsingle (k : Fin n) :
      Function.update (1 : Fin n → rationalPoints G) l u k ∈ rootGroupPoints j (a k) := by
    by_cases hk : k = l
    · subst hk
      rw [Function.update_self, hl]
      exact hu.1
    · rw [Function.update_of_ne hk]
      exact Subgroup.one_mem _
  let Y₂ : ∀ k, (RelativeRoot.subgroup j (a k)).carrier (Over.mk (𝟙 _)) :=
    fun k => ⟨Function.update (1 : Fin n → rationalPoints G) l u k, hsingle k⟩
  have hY₁ : RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) Y₁ = u := hprod'
  have hY₂ : RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) Y₂ = u :=
    list_ofFn_prod_update_one (M := rationalPoints G) l u
  have hY : Y₁ = Y₂ := (hZu Y₁ hY₁).trans (hZu Y₂ hY₂).symm
  have hXu : X' l = u := by
    have := congrArg
      (fun z : (RelativeRoot.subgroup j (a l)).carrier (Over.mk (𝟙 _)) => z.val)
      (congrFun hY l)
    simpa only [Y₁, Y₂, Function.update_self] using this
  -- conclusion
  have hmem : ∀ x : rationalPoints G, x ∈ rootGroupPoints j (a l) →
      x ∈ rootGroupPoints j χ := fun x hx => hl ▸ hx
  have hXlU : (Xs l).val ∈ rootGroupPoints j χ := hmem _ (Xs l).property
  have hXlpos : ((r : ℝ) : WithTop ℝ) < φ χ (Xs l).val := by
    rw [← hl]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hrs) hXl
  exact Set.mem_mul.mpr ⟨(Xs l).val, ⟨hXlU, hXlpos⟩, d, hd, by rw [← hX'l, hXu]⟩

end Restriction

end Langlands.Geometry.Building
