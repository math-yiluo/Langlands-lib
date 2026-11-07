import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.SplitExistence.LieWeights
import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Lie.KernelTargetMaps

/-! # Weight decomposition of the Lie algebra under a generic point of a cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelPointContainment

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- Over an infinite field, for finitely many nonzero exponents there is a unit avoiding all of
their roots of unity. -/
theorem exists_unit_zpow_ne_one [Infinite k] {S : Set ℤ} (hS : S.Finite) :
    ∃ c₀ : kˣ, ∀ n ∈ S, n ≠ 0 → c₀ ^ n ≠ 1 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (α := k)
    (hS.toFinset.biUnion (fun n => (Polynomial.nthRoots n.natAbs (1 : k)).toFinset) ∪ {0})
  have hx0 : x ≠ 0 := fun h => hx (Finset.mem_union_right _ (Finset.mem_singleton.2 h))
  refine ⟨Units.mk0 x hx0, fun n hn hn0 h => hx (Finset.mem_union_left _ ?_)⟩
  refine Finset.mem_biUnion.2 ⟨n, hS.mem_toFinset.2 hn, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (Int.natAbs_pos.2 hn0)]
  have h' : Units.mk0 x hx0 ^ n.natAbs = 1 := by
    rcases Int.natAbs_eq n with h₁ | h₁
    · rw [h₁, zpow_natCast] at h
      exact h
    · rw [h₁, zpow_neg, zpow_natCast, inv_eq_one] at h
      exact h
  simpa using congrArg Units.val h'

variable {G Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- Over an infinite field, some `k`-point `u` of `𝔾_m` has `u ^ n ≠ 1` for every nonzero
exponent `n` whose weight space for `χ` is nonzero. -/
theorem exists_generic_affinePoint [Infinite k] :
    ∃ u : Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp k,
      ∀ n : ℤ, n ≠ 0 → weightSpace χ (Gm.powerHom _ n) ≠ ⊥ →
        Lie.characterValue (Gm.powerHom _ n) u ≠ 1 := by
  have hS : {n : ℤ | weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n) ≠ ⊥}.Finite :=
    (IsSplitTorus.finite_weightSupport χ isSplitTorus_gm).preimage
      (Gm.powerHom_injective k).injOn
  obtain ⟨c₀, hc₀⟩ := exists_unit_zpow_ne_one (k := k) hS
  refine ⟨(Gm.affinePointsEquiv (R := CommRingCat.of k)
    ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k))).hom).symm c₀,
    fun n hn hw => ?_⟩
  rw [SplitExistence.ChevalleyData.ChevGroup.characterValue_powerHom]
  erw [MulEquiv.apply_symm_apply]
  exact hc₀ n hw hn

variable [IsAffineHom Z.X.hom] (iZ : Z ⟶ G)

/-- **Weight decomposition.** Let `Z` represent the dynamic centralizer of `χ` and let `u` be a
`k`-point of `𝔾_m` with `χ`-eigenvalue different from `1` on every nonzero weight space. Then every
Lie vector `W` of `G` has the form `Ad(χ(u)) X - X + dι(ξ)`. -/
theorem exists_adjoint_sub_add_eq (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
    (u : Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp k)
    (hu : ∀ n : ℤ, n ≠ 0 → weightSpace χ (Gm.powerHom _ n) ≠ ⊥ →
      Lie.characterValue (Gm.powerHom _ n) u ≠ 1)
    (W : Additive (lieKernel G k)) :
    ∃ (X : Additive (lieKernel G k)) (ξ : Additive (lieKernel Z k)),
      adjoint G k (u ≫ χ.hom.hom) X - X + Lie.targetMapLinear iZ k ξ = W := by
  classical
  have hid : ∀ y : Additive (lieKernel G k),
      lieKernelMapLinear G (Algebra.ofId (CommRingCat.of k) k) y = y := fun y => by
    apply Additive.toMul.injective
    change lieKernelMap G (AlgHom.id (CommRingCat.of k) k) _ = _
    exact lieKernelMap_id G _
  have heig : ∀ (n : ℤ) (y : Additive (lieKernel G k)),
      y ∈ weightSpace χ (Gm.powerHom _ n) →
        adjoint G k (u ≫ χ.hom.hom) y = (Lie.characterValue (Gm.powerHom _ n) u : k) • y := by
    intro n y hy
    have h := (mem_weightSpace.1 hy) k u
    rwa [hid] at h
  set wc := DynamicLie.weightCoeffs k G χ W with hwc
  have hmem : ∀ m : PUnit.{u + 1} → ℤ,
      wc m ∈ weightSpace χ (Gm.powerHom _ (m PUnit.unit)) :=
    fun m => DynamicLie.weightCoeffs_mem k G χ W (m PUnit.unit)
  let c : (PUnit.{u + 1} → ℤ) → k := fun m =>
    (Lie.characterValue (Gm.powerHom (Spec (CommRingCat.of k)) (m PUnit.unit)) u : k)
  let f : (PUnit.{u + 1} → ℤ) → Additive (lieKernel G k) → Additive (lieKernel G k) :=
    fun m y => if m = 0 then 0 else (c m - 1)⁻¹ • y
  have hterm : ∀ m ∈ wc.support,
      adjoint G k (u ≫ χ.hom.hom) (f m (wc m)) - f m (wc m) =
        (fun m y => if m = 0 then 0 else y) m (wc m) := by
    intro m hm
    by_cases h0 : m = 0
    · simp only [f, h0, ↓reduceIte, map_zero, sub_zero]
    · simp only [f, h0, ↓reduceIte]
      have hn : m PUnit.unit ≠ 0 := fun h => h0 (funext fun _ => h)
      have hne : wc m ≠ 0 := Finsupp.mem_support_iff.1 hm
      have hc : c m ≠ 1 := fun h1 =>
        hu _ hn ((Submodule.ne_bot_iff _).2 ⟨_, hmem m, hne⟩) (Units.ext h1)
      have hsc : (c m - 1)⁻¹ * c m - (c m - 1)⁻¹ = 1 := by
        rw [← mul_sub_one, inv_mul_cancel₀ (sub_ne_zero.2 hc)]
      rw [LinearMap.map_smul, heig _ _ (hmem m), smul_smul, ← sub_smul]
      change ((c m - 1)⁻¹ * c m - (c m - 1)⁻¹) • wc m = wc m
      rw [hsc, one_smul]
  have h0mem : wc 0 ∈ weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) 0) := hmem 0
  have hcent := ((dynamicLie k G χ (Additive.toMul (wc 0))).1).2 h0mem
  rw [← hZ.2] at hcent
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.1 hcent
  have := hZ.1
  have hxk : x ∈ lieKernel Z k :=
    (Lie.mem_lieKernel_comp_hom_iff iZ x).1 (by rw [hx]; exact (Additive.toMul (wc 0)).property)
  refine ⟨wc.sum f, Additive.ofMul ⟨x, hxk⟩, ?_⟩
  have htarget : Lie.targetMapLinear iZ k (Additive.ofMul ⟨x, hxk⟩) = wc 0 := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hx
  rw [htarget, map_finsuppSum, ← Finsupp.sum_sub, Finsupp.sum_congr hterm]
  calc wc.sum (fun m y => if m = 0 then 0 else y) + wc 0
      = wc.sum (fun m y => if m = 0 then 0 else y) +
          wc.sum (fun m y => if m = 0 then y else 0) := by
        rw [Finsupp.sum_ite_self_eq']
    _ = wc.sum (fun _ y => y) := by
        rw [← Finsupp.sum_add]
        exact Finsupp.sum_congr (fun m _ => by split_ifs <;> simp)
    _ = W := DynamicLie.weightCoeffs_sum k G χ W

end BorelPointContainment

end Langlands.GroupScheme
