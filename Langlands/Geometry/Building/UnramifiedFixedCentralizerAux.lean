import Langlands.Geometry.Building.KPCentralizerCompatibility
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.LinearAlgebra.RationalRealSpan
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Rational.RootFactorPairReflection
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel

/-! # Auxiliary lemmas for V 6 at Galois-fixed points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.Geometry.Building

section Integral

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {Z : GroupScheme (Spec (CommRingCat.of k))}

/-- On a split torus, `χ ↦ 1 ⊗ χ` into the rationalized character lattice is injective. -/
theorem toRat_injective_of_isSplitTorus (hS : IsSplitTorus S.toGrp) :
    Function.Injective (toRat : characterLattice S → ℚ ⊗[ℤ] characterLattice S) := by
  intro x y hxy
  have h := congrArg (toReal (characterLattice S)) hxy
  rw [toReal_toRat, toReal_toRat] at h
  rw [← sub_eq_zero]
  apply hS.isPerfPair_latticePairing.separatingLeft (x - y)
  intro ν
  have hp := congrArg (fun c => pair S c ((1 : ℝ) ⊗ₜ[ℤ] ν)) h
  simp only [pair_tmul_tmul, one_mul] at hp
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  exact_mod_cast hp

/-- Elements of the rational span of an additive subgroup are rational multiples of
elements of the subgroup. -/
theorem exists_nsmul_eq_toRat_of_mem_ratSpan {M : Type*} [AddCommGroup M] (A : AddSubgroup M)
    {x : ℚ ⊗[ℤ] M} (hx : x ∈ ratSpan (A : Set M)) :
    ∃ m : ℕ, 0 < m ∧ ∃ r ∈ A, m • x = toRat r := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    exact ⟨1, one_pos, r, hr, one_smul _ _⟩
  | zero => exact ⟨1, one_pos, 0, A.zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, r, hr, hmr⟩ := hy
    obtain ⟨n, hn, s, hs, hns⟩ := hz
    refine ⟨m * n, Nat.mul_pos hm hn, n • r + m • s, A.add_mem (A.nsmul_mem hr n)
      (A.nsmul_mem hs m), ?_⟩
    rw [smul_add, map_add, map_nsmul, map_nsmul, ← hmr, ← hns, smul_smul, smul_smul,
      mul_comm n m]
  | smul q y _ hy =>
    obtain ⟨m, hm, r, hr, hmr⟩ := hy
    refine ⟨q.den * m, Nat.mul_pos q.den_pos hm, q.num • r, A.zsmul_mem hr q.num, ?_⟩
    rw [map_zsmul, ← hmr]
    have hq : ((q.den * m : ℕ) : ℚ) * q = (q.num : ℚ) * m := by
      push_cast
      rw [mul_comm (q.den : ℚ) m, mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hq, ← smul_smul, Nat.cast_smul_eq_nsmul,
      Int.cast_smul_eq_zsmul]

/-- **Characters of `Z` restricting to a multiple of a given character.** If the restriction
evaluation of `s : S → Z` is bijective and `S` is split, every character `a` of `S` has a
positive multiple that is the restriction of a rational character of `Z`. -/
theorem exists_characterRestriction_eq_nsmul (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ Z)
    (hs : Function.Bijective (BruhatTits.Cartan.restrictionEvaluation s))
    (a : characterLattice S) :
    ∃ (χ : rationalCharacters Z) (m : ℕ), 0 < m ∧
      BruhatTits.Cartan.characterRestriction s χ = m • a := by
  classical
  set A : AddSubgroup (characterLattice S) :=
    (BruhatTits.Cartan.characterRestriction s).range with hA
  have hreal : (1 : ℝ) ⊗ₜ[ℤ] a ∈
      Submodule.span ℝ ((fun m : characterLattice S => (1 : ℝ) ⊗ₜ[ℤ] m) '' (A : Set _)) := by
    by_contra hna
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hna inferInstance
    have hp := isPerfPair_of_isSplitTorus hS
    obtain ⟨v, hv⟩ := (LinearMap.IsPerfPair.bijective_right (pair S)).2 f
    have hzero : BruhatTits.Cartan.restrictionEvaluation s v = 0 := by
      ext χ
      change eval S (BruhatTits.Cartan.characterRestriction s χ) v = 0
      rw [eval_eq_pair]
      have h1 := LinearMap.congr_fun hv ((1 : ℝ) ⊗ₜ[ℤ] BruhatTits.Cartan.characterRestriction s χ)
      rw [LinearMap.flip_apply] at h1
      rw [h1]
      have hmem : (1 : ℝ) ⊗ₜ[ℤ] BruhatTits.Cartan.characterRestriction s χ ∈
          Submodule.span ℝ ((fun m : characterLattice S => (1 : ℝ) ⊗ₜ[ℤ] m) '' (A : Set _)) :=
        Submodule.subset_span ⟨_, ⟨χ, rfl⟩, rfl⟩
      have hmap := Submodule.mem_map_of_mem (f := f) hmem
      rw [hf0] at hmap
      exact (Submodule.mem_bot ℝ).1 hmap
    have hv0 : v = 0 := hs.1 (hzero.trans (map_zero _).symm)
    apply hf
    have h1 := LinearMap.congr_fun hv ((1 : ℝ) ⊗ₜ[ℤ] a)
    rw [LinearMap.flip_apply, hv0, map_zero] at h1
    exact h1.symm
  have hrat : toRat a ∈ ratSpan (A : Set (characterLattice S)) := by
    rw [← toReal_mem_span_iff, toReal_toRat]
    exact hreal
  obtain ⟨m, hm, r, hr, hmr⟩ := exists_nsmul_eq_toRat_of_mem_ratSpan A hrat
  obtain ⟨χ, rfl⟩ := hr
  refine ⟨χ, m, hm, ?_⟩
  apply toRat_injective_of_isSplitTorus hS
  rw [map_nsmul, hmr]

end Integral

section Translation

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- If `w • φ = t + φ`, then `w ^ N • φ = (t + w t + ⋯ + w ^ (N - 1) t) + φ`. -/
theorem RootFunctionFamily.pow_smul_eq_sum_vadd (w : normalizerPoints i)
    (φ : RootFunctionFamily T G) (t : V T) (hw : w • φ = t +ᵥ φ) (N : ℕ) :
    w ^ N • φ = (∑ j ∈ Finset.range N, w ^ j • t) +ᵥ φ := by
  induction N with
  | zero => rw [pow_zero, one_smul, Finset.sum_range_zero, zero_vadd]
  | succ N ih =>
    rw [pow_succ, mul_smul, hw, RootFunctionFamily.smul_vadd, ih, vadd_vadd,
      Finset.sum_range_succ, add_comm]

/-- A character fixed by `w⁻¹` is fixed by every `(w ^ j)⁻¹`. -/
theorem weylAction_inv_pow_apply_of_inv_apply (w : normalizerPoints i) {ξ : characterLattice T}
    (hinv : weylAction i w⁻¹ ξ = ξ) (j : ℕ) : weylAction i (w ^ j)⁻¹ ξ = ξ := by
  induction j with
  | zero => rw [pow_zero, inv_one, map_one, LinearEquiv.coe_one, id]
  | succ j ih => rw [pow_succ, mul_inv_rev, map_mul, LinearEquiv.mul_apply, ih, hinv]

variable [IsAffineHom G.X.hom]

/-- **The translation part of a normalizer element along a Weyl-invariant character.** Let
`φ` be a valuation, `w • φ = t + φ` and `w ^ N • φ = ν + φ`. If a character `ξ` is fixed by
`w⁻¹` and vanishes on the common kernel of the roots, then `N ξ(t) = ξ(ν)`. -/
theorem natCast_mul_eval_eq_of_pow_smul {φ : RootFunctionFamily T G}
    (hφ : IsRootDatumValuation i φ) (w : normalizerPoints i) {t ν : V T} {N : ℕ}
    (ht : w • φ = t +ᵥ φ) (hN : w ^ N • φ = ν +ᵥ φ) {ξ : characterLattice T}
    (hker : ∀ r ∈ rootAnnihilator i, eval T ξ r = 0) (hinv : weylAction i w⁻¹ ξ = ξ) :
    (N : ℝ) * eval T ξ t = eval T ξ ν := by
  have h1 := RootFunctionFamily.pow_smul_eq_sum_vadd w φ t ht N
  rw [hN] at h1
  have hmem := hφ.vadd_eq_vadd_iff.1 h1
  have h0 := hker _ hmem
  rw [map_sub, sub_eq_zero, map_sum] at h0
  rw [h0]
  have hterm : ∀ j ∈ Finset.range N, eval T ξ (w ^ j • t) = eval T ξ t := by
    intro j _
    rw [eval_normalizer_smul, weylAction_inv_pow_apply_of_inv_apply w hinv j]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Translation

section WeylInvariance

variable {B : Scheme.{u}} {T : CommGroupScheme B} {M G : GroupScheme B}

/-- A normalizing point lying in a subgroup `M` fixes the restrictions of the characters of
`M` to the torus. -/
theorem weylAction_torusCharacterRestrict_of_comp (τ : T.toGrp ⟶ M) (j : M ⟶ G)
    [Mono j.hom.hom] {iT : T.toGrp ⟶ G} (hτ : τ ≫ j = iT) [Mono iT.hom.hom.left]
    (w : normalizerPoints iT) (m : Over.mk (𝟙 B) ⟶ M.X)
    (hm : m ≫ j.hom.hom = (w : Over.mk (𝟙 B) ⟶ G.X)) (ψ : rationalCharacters M) :
    weylAction iT w (torusCharacterRestrict τ ψ) = torusCharacterRestrict τ ψ := by
  subst hτ
  have hσ := isNormalizingPoint_normalizingAut (τ ≫ j) w
  rw [← hm] at hσ
  have hστ := hσ.of_comp j
  have hn := hστ.inv
  change τ ≫ (M.innerIso m⁻¹).hom =
    CommGroupScheme.groupHom (normalizingAut (τ ≫ j) w).inv ≫ τ at hn
  rw [weylAction_apply]
  change Additive.ofMul
      (CommGroupScheme.groupHom (normalizingAut (τ ≫ j) w).inv ≫ τ ≫ ψ.toMul) =
    Additive.ofMul (τ ≫ ψ.toMul)
  congr 1
  rw [← Category.assoc, ← hn, Category.assoc, ψ.comp_innerIso_hom]

end WeylInvariance

section Centralizer

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- **Powers of normalizer elements centralize.** For a closed split torus in an affine group
of finite type, some positive power of every normalizing point centralizes the torus. -/
theorem exists_pow_mem_centralizerPoints [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    [Mono i.hom.hom.left] (w : normalizerPoints i) :
    ∃ N : ℕ, 0 < N ∧ ((w ^ N : normalizerPoints i) : rationalPoints G) ∈ centralizerPoints i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Finite (weylImage i) := splitTorusWeylImageFinite k G T hT i hi
  let x : weylImage i := ⟨weylAction i w, w, rfl⟩
  obtain ⟨N, hN, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 (isOfFinOrder_of_finite x)
  refine ⟨N, hN, (hT.weylAction_eq_one_iff i (w ^ N)).1 ?_⟩
  rw [map_pow]
  exact congrArg Subtype.val hpow

end Centralizer

section Points

variable {B : Scheme.{u}} {T : CommGroupScheme B} {M G : GroupScheme B}

/-- The points of a represented torus centralizer are the images of the points of its
representative. -/
theorem exists_comp_eq_of_mem_centralizerPoints {i : T.toGrp ⟶ G} {j : M ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) {g : Over.mk (𝟙 B) ⟶ G.X}
    (hg : g ∈ centralizerPoints i) : ∃ m : Over.mk (𝟙 B) ⟶ M.X, m ≫ j.hom.hom = g := by
  rw [← torusCentralizer_carrier_base, ← hj.2] at hg
  exact SubgroupFunctor.mem_range.1 hg

/-- The full kernel centralizer of a character vanishing on `S` centralizes `S`. -/
theorem kernelCentralizer_le_torusCentralizer {S : CommGroupScheme B} (iT : T.toGrp ⟶ G)
    (f : S ⟶ T) {χ : characterLattice T} (hf : f ≫ χ = 0) :
    RelativeRoot.kernelCentralizer iT χ ≤ torusCentralizer (CommGroupScheme.groupHom f ≫ iT) := by
  intro U g hg V b t
  rw [RelativeRoot.mem_kernelCentralizer] at hg
  let s : V ⟶ T.X := t ≫ (CommGroupScheme.groupHom f).hom.hom
  have hs : s ≫ (CommGroupScheme.groupHom χ).hom.hom = 1 := by
    change (t ≫ (CommGroupScheme.groupHom f).hom.hom) ≫ (CommGroupScheme.groupHom χ).hom.hom = 1
    rw [← comp_groupHom_comp, hf, comp_groupHom_zero]
  let c : V ⟶ (RelativeRoot.characterKernel χ).X :=
    (kernelPointsEquiv (CommGroupScheme.groupHom χ) V).symm ⟨s, hs⟩
  have hc : c ≫ (RelativeRoot.characterKernelι χ).hom.hom = s :=
    congrArg Subtype.val ((kernelPointsEquiv (CommGroupScheme.groupHom χ) V).apply_symm_apply
      ⟨s, hs⟩)
  have h := hg V b c
  simpa only [Grp.comp_hom_hom, ← Category.assoc, hc] using h

end Points

section Unipotent

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M : GroupScheme (Spec (CommRingCat.of k))}

/-- A nonzero character of a split torus is positive on some cocharacter. -/
theorem exists_latticePairing_pos_of_ne_zero_of_isSplitTorus (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ≠ 0) :
    ∃ ν : cocharacterLattice T, 0 < latticePairing T α ν := by
  by_contra h
  simp only [not_exists, not_lt] at h
  apply hα
  apply hT.isPerfPair_latticePairing.separatingLeft α
  intro ν
  have h1 := h ν
  have h2 := h (-ν)
  rw [map_neg] at h2
  omega

/-- **Characters of a centralizer kill root groups inside it.** Let `j : M → G` be a closed
representative of the centralizer of `f ≫ iT` for a split torus `iT : T → G`, through which
`iT` factors as `τ ≫ j`, with `M` smooth and affine. Every point of the root group of a
nonzero character `χ` of `T` vanishing on `S` is the image of a point of `M` on which every
rational character of `M` takes the value `1`. -/
theorem exists_map_eq_and_eval_eq_one_of_mem_rootGroupPoints [Smooth M.X.hom]
    [IsAffineHom M.X.hom] (hT : IsSplitTorus T.toGrp) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (τ : T.toGrp ⟶ M) (j : M ⟶ G) (hτ : τ ≫ j = iT)
    (hj : (torusCentralizer (CommGroupScheme.groupHom f ≫ iT)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) {χ : characterLattice T} (hχ : χ ≠ 0) (hf : f ≫ χ = 0)
    (ψ : rationalCharacters M) {u : rationalPoints G} (hu : u ∈ rootGroupPoints iT χ) :
    ∃ m : rationalPoints M, rationalPoints.map j m = u ∧ rationalCharacterEval ψ m = 1 := by
  have hcent : u ∈ (torusCentralizer (CommGroupScheme.groupHom f ≫ iT)).carrier
      (Over.mk (𝟙 _)) :=
    kernelCentralizer_le_torusCentralizer iT f hf _
      (RelativeRoot.subgroup_le_kernelCentralizer iT χ _ hu)
  rw [← hj.2] at hcent
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.1 hcent
  obtain ⟨ν, hν⟩ := exists_latticePairing_pos_of_ne_zero_of_isSplitTorus hT hχ
  have hU := RelativeRoot.subgroup_le_dynamicUnipotent iT ν hν (Over.mk (𝟙 _)) hu
  have hmU : m ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ τ)).carrier
      (Over.mk (𝟙 _)) := by
    rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup (CommGroupScheme.groupHom ν ≫ τ) j hjc,
      SubgroupFunctor.mem_comap, hm, Category.assoc, hτ]
    exact hU
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have hρ := Dynamic.Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom ν ≫ τ)
  rw [← hρ.2] at hmU
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hmU
  have hUn := Dynamic.isUnipotent_unipotentRepresentative (CommGroupScheme.groupHom ν ≫ τ) hρ
  refine ⟨m, hm, ?_⟩
  have h0 : characterRestrict (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ τ))
      ψ = 0 :=
    congrArg Additive.ofMul (hUn.hom_eq_zero_of_isSplitTorus isSplitTorus_gm
      (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ τ) ≫ ψ.toMul))
  have h1 := rationalCharacterEval_characterRestrict
    (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ τ)) ψ y
  rw [h0, rationalCharacterEval_zero, rationalPoints.map_apply, hy] at h1
  exact h1.symm

/-- The subgroup generated by root-group points of roots vanishing on `S` lies in the image
of the points of `M` killed by a given rational character of `M`. -/
theorem exists_map_eq_and_eval_eq_one_of_mem_iSup [IsAffineHom G.X.hom] [Smooth M.X.hom]
    [IsAffineHom M.X.hom] (hT : IsSplitTorus T.toGrp) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (τ : T.toGrp ⟶ M) (j : M ⟶ G) (hτ : τ ≫ j = iT)
    (hj : (torusCentralizer (CommGroupScheme.groupHom f ≫ iT)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (ψ : rationalCharacters M)
    (A : characterLattice T → Subgroup (rationalPoints G))
    (hA : ∀ χ, A χ ≤ rootGroupPoints iT χ) {h : rationalPoints G}
    (hh : h ∈ ⨆ (χ : characterLattice T) (_ : χ ∈ relativeRoots iT) (_ : f ≫ χ = 0), A χ) :
    ∃ m : rationalPoints M, rationalPoints.map j m = h ∧ rationalCharacterEval ψ m = 1 := by
  let H0 : Subgroup (rationalPoints G) :=
    (rationalCharacterEval ψ).ker.map (rationalPoints.map j)
  have hle : (⨆ (χ : characterLattice T) (_ : χ ∈ relativeRoots iT) (_ : f ≫ χ = 0), A χ) ≤
      H0 := by
    refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun hf => fun u hu => ?_
    obtain ⟨m, hm, h1⟩ := exists_map_eq_and_eval_eq_one_of_mem_rootGroupPoints hT iT f τ j hτ
      hj hjc (mem_relativeRoots.1 hχ).1 hf ψ (hA χ hu)
    exact ⟨m, h1, hm⟩
  obtain ⟨m, hm1, hm⟩ := hle hh
  exact ⟨m, hm, hm1⟩

end Unipotent

end Langlands.Geometry.Building
