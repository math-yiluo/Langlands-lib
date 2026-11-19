import Langlands.Global.Factors.WeilPoleRegionStatement
import Langlands.LocalFactor.WeilDeligneEulerSum
import Langlands.LocalFactor.WeilDeligneBlockPair
import Langlands.WeilDeligne.BlockDualProof
import Langlands.Correspondence.AssemblyZeroMonodromyWitness
import Langlands.Correspondence.AssemblyDual

/-!
# Pole regions of Weil–Deligne L-polynomials: the non-juxtaposed case

Proof of `Langlands.Global.NonJuxtaposedPoleRegionStatement`, the second case of
Henniart 1986, Proposition 4.5(i). Both L-polynomials are factored over the blocks
`ρ_i ⊗ Sp(n_i)`; a common zero gives eigenvectors in `(ρ_i ⊗ B)^I` and
`(ρ_j^∨ ⊗ B^∨)^I`, from which a twisted Schur argument yields `ρ_j ≅ ν^(n_i) ρ_i`.
That contradicts non-juxtaposition when `i ≠ j`, and a determinant comparison
when `i = j`.
-/

noncomputable section

universe u v w uG uV uW

namespace Langlands.Global.WeilPoleRegionNonJuxtaposed

open Langlands.LocalFactor.WeilDeligne
open scoped TensorProduct

section Reduction

variable {G : Type uG} [Group G] (ν : G →* ℂˣ) (I : Subgroup G) [I.Normal]
  (hν : ∀ i : I, ν i = 1)

/-- The Euler polynomial of a tensor with a parameter equivalent to a direct sum. -/
theorem eulerPolynomial_tensor_of_equiv_directSum {k : ℕ}
    (σ : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (A : Fin k → WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (e : WeilDeligneRepresentation.Equiv σ (WeilDeligneRepresentation.directSum A))
    (Z : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν) (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.tensor σ Z) I g =
      ∏ i, eulerPolynomial (WeilDeligneRepresentation.tensor (A i) Z) I g := by
  rw [eulerPolynomial_eq_of_equiv I
      (WeilDeligneRepresentation.tensorEquiv e (WeilDeligneRepresentation.Equiv.refl Z)) g,
    eulerPolynomial_eq_of_equiv I (tensorDirectSumLeft A Z) g, eulerPolynomial_directSum]

/-- The Euler polynomial of a tensor of the dual of a parameter equivalent to a direct sum. -/
theorem eulerPolynomial_tensor_dual_of_equiv_directSum {k : ℕ}
    (σ : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (A : Fin k → WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (e : WeilDeligneRepresentation.Equiv σ (WeilDeligneRepresentation.directSum A))
    (Z : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν) (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.dual σ) Z) I g =
      ∏ i, eulerPolynomial
        (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.dual (A i)) Z) I g := by
  rw [eulerPolynomial_eq_of_equiv I
      (WeilDeligneRepresentation.tensorEquiv
        ((WeilDeligneRepresentation.dualEquiv e).symm.trans
          (Langlands.Correspondence.AssemblyDual.dualDirectSumEquiv A))
        (WeilDeligneRepresentation.Equiv.refl Z)) g,
    eulerPolynomial_eq_of_equiv I (tensorDirectSumLeft _ Z) g, eulerPolynomial_directSum]

include hν in
/-- A block tensored with a zero-monodromy pair. -/
theorem eulerPolynomial_block_zeroMonodromy
    (ρ : FiniteRepresentation.{0, uG, uV} ℂ G) (B : FiniteRepresentation.{0, uG, uW} ℂ G)
    (a : ℕ) (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν ρ (a + 1))
        (WeilDeligneRepresentation.zeroMonodromy ν B)) I g =
      LocalFactor.eulerPolynomial (blockPairKernelOperator ν ρ B a 0 I g) := by
  rw [eulerPolynomial_eq_of_equiv I
      (WeilDeligneRepresentation.tensorEquiv (WeilDeligneRepresentation.Equiv.refl _)
        (WeilDeligneRepresentation.blockOneEquiv ν B).symm) g]
  exact eulerPolynomial_block_block ν ρ B a 0 I hν g

include hν in
/-- The dual of a block tensored with the dual of a zero-monodromy pair. -/
theorem eulerPolynomial_dual_block_dual_zeroMonodromy
    (ρ : FiniteRepresentation.{0, uG, uV} ℂ G) (B : FiniteRepresentation.{0, uG, uW} ℂ G)
    (a : ℕ) (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.block ν ρ (a + 1)))
        (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.zeroMonodromy ν B))) I g =
      LocalFactor.eulerPolynomial (blockPairKernelOperator ν
        (FiniteRepresentation.twist (ν ^ (1 - ((a + 1 : ℕ) : ℤ))) (FiniteRepresentation.dual ρ))
        (FiniteRepresentation.dual B) a 0 I g) := by
  rw [eulerPolynomial_eq_of_equiv I
      (WeilDeligneRepresentation.tensorEquiv
        (WeilDeligneRepresentation.Blocks.blockDualEquiv ν ρ (a + 1))
        ((WeilDeligneRepresentation.dualZeroMonodromyEquiv B).trans
          (WeilDeligneRepresentation.blockOneEquiv ν (FiniteRepresentation.dual B)).symm)) g]
  exact eulerPolynomial_block_block ν _ _ a 0 I hν g

end Reduction

section Contraction

open TensorProduct

variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A tensor all of whose values under products of functionals vanish is zero. -/
theorem eq_zero_of_dualDistrib [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (t : V ⊗[ℂ] W)
    (h : ∀ (α : Module.Dual ℂ V) (β : Module.Dual ℂ W), dualDistrib ℂ V W (α ⊗ₜ β) t = 0) :
    t = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ t]
  intro φ
  obtain ⟨x, rfl⟩ := (dualDistribEquiv ℂ V W).surjective φ
  induction x with
  | tmul α β =>
    have hx := LinearMap.congr_fun (toLinearMap_dualDistribEquiv (R := ℂ) (M := V) (N := W))
      (α ⊗ₜ β)
    rw [LinearEquiv.coe_coe] at hx
    rw [hx]
    exact h α β
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

/-- Contraction of the first factor of `V ⊗ W` against a functional on `V`. -/
def contrLeft (t : V ⊗[ℂ] W) : Module.Dual ℂ V →ₗ[ℂ] W where
  toFun α := TensorProduct.lid ℂ W (TensorProduct.map α LinearMap.id t)
  map_add' α α' := by simp [TensorProduct.map_add_left]
  map_smul' c α := by simp [TensorProduct.map_smul_left]

/-- Contraction of the second factor of `V ⊗ W` against a functional on `W`. -/
def contrRight (t : V ⊗[ℂ] W) : Module.Dual ℂ W →ₗ[ℂ] V where
  toFun β := TensorProduct.rid ℂ V (TensorProduct.map LinearMap.id β t)
  map_add' β β' := by simp [TensorProduct.map_add_right]
  map_smul' c β := by simp [TensorProduct.map_smul_right]

theorem apply_contrLeft (t : V ⊗[ℂ] W) (α : Module.Dual ℂ V) (β : Module.Dual ℂ W) :
    β (contrLeft t α) = dualDistrib ℂ V W (α ⊗ₜ β) t := by
  induction t with
  | tmul x y => simp [contrLeft, dualDistrib_apply]
  | add x y hx hy =>
    simp only [contrLeft, LinearMap.coe_mk, AddHom.coe_mk, map_add] at hx hy ⊢
    rw [hx, hy]

theorem apply_contrRight (t : V ⊗[ℂ] W) (α : Module.Dual ℂ V) (β : Module.Dual ℂ W) :
    α (contrRight t β) = dualDistrib ℂ V W (α ⊗ₜ β) t := by
  induction t with
  | tmul x y => simp [contrRight, dualDistrib_apply, mul_comm]
  | add x y hx hy =>
    simp only [contrRight, LinearMap.coe_mk, AddHom.coe_mk, map_add] at hx hy ⊢
    rw [hx, hy]

theorem contrLeft_map (t : V ⊗[ℂ] W) (α : Module.Dual ℂ V) (f : V →ₗ[ℂ] V) (h : W →ₗ[ℂ] W) :
    contrLeft (TensorProduct.map f h t) α = h (contrLeft t (α ∘ₗ f)) := by
  induction t with
  | tmul x y => simp [contrLeft]
  | add x y hx hy =>
    simp only [contrLeft, LinearMap.coe_mk, AddHom.coe_mk, map_add] at hx hy ⊢
    rw [hx, hy]

theorem contrRight_map (t : V ⊗[ℂ] W) (β : Module.Dual ℂ W) (f : V →ₗ[ℂ] V) (h : W →ₗ[ℂ] W) :
    contrRight (TensorProduct.map f h t) β = f (contrRight t (β ∘ₗ h)) := by
  induction t with
  | tmul x y => simp [contrRight]
  | add x y hx hy =>
    simp only [contrRight, LinearMap.coe_mk, AddHom.coe_mk, map_add] at hx hy ⊢
    rw [hx, hy]

theorem contrLeft_smul (t : V ⊗[ℂ] W) (c : ℂ) (α : Module.Dual ℂ V) :
    contrLeft (c • t) α = c • contrLeft t α := by
  simp [contrLeft]

theorem contrRight_smul (t : V ⊗[ℂ] W) (c : ℂ) (β : Module.Dual ℂ W) :
    contrRight (c • t) β = c • contrRight t β := by
  simp [contrRight]

end Contraction

section Irreducible

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A subspace stable under an irreducible representation is zero or everything. -/
theorem stable_eq_bot_or_eq_top (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible)
    (S : Submodule ℂ V) (hS : ∀ g : G, ∀ v ∈ S, ρ g v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  rcases hρ.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-- The carrier of an irreducible representation is nonzero. -/
theorem nontrivial_of_isIrreducible (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) :
    Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply hρ.toNontrivial.exists_pair_ne.elim
  intro a ha
  obtain ⟨b, hab⟩ := ha
  apply hab
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

end Irreducible

section Eigen

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An eigenvector of `Φ` fixed by `I` is an eigenvector of every element, when every
element is an integer power of `Φ` modulo `I`. -/
theorem zpow_eigen (π : Representation ℂ G V) (Φ : G) (x : V) (c : ℂ) (hc : c ≠ 0)
    (hΦ : π Φ x = c • x) : ∀ k : ℤ, π (Φ ^ k) x = c ^ k • x := by
  have hinv : π Φ⁻¹ x = c⁻¹ • x := by
    have h1 : π Φ⁻¹ (π Φ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hΦ, map_smul] at h1
    calc π Φ⁻¹ x = c⁻¹ • (c • π Φ⁻¹ x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • x := by rw [h1]
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, map_mul, Module.End.mul_apply, hΦ, map_smul, ih, smul_smul,
      zpow_add_one₀ hc, mul_comm]
  | pred k ih =>
    rw [zpow_sub_one, map_mul, Module.End.mul_apply, hinv, map_smul, ih, smul_smul,
      zpow_sub_one₀ hc, mul_comm]

theorem eigen_of_mem (π : Representation ℂ G V) (I : Subgroup G) (Φ : G) (x : V) (c : ℂ)
    (hc : c ≠ 0) (hI : ∀ i ∈ I, π i x = x) (hΦ : π Φ x = c • x) (g : G) (k : ℤ)
    (hk : g * (Φ ^ k)⁻¹ ∈ I) : π g x = c ^ k • x := by
  have hg : g = (g * (Φ ^ k)⁻¹) * Φ ^ k := by group
  rw [hg, map_mul, Module.End.mul_apply, zpow_eigen π Φ x c hc hΦ k, map_smul, hI _ hk]

end Eigen

section BlockEigen

variable {G : Type uG} [Group G] (ν : G →* ℂˣ) (I : Subgroup G) [I.Normal]

/-- A zero of the Euler polynomial of `blockPairKernelOperator ν ρ B a 0 I g` at `z`
gives a nonzero `I`-fixed vector `x` of `ρ ⊗ B` with `x = z ν(g)^a g x`. -/
theorem exists_eigen_of_blockPair (ρ : FiniteRepresentation.{0, uG, uV} ℂ G)
    (B : FiniteRepresentation.{0, uG, uW} ℂ G) (a : ℕ) (g : G) (z : ℂ)
    (h : (LocalFactor.eulerPolynomial (blockPairKernelOperator ν ρ B a 0 I g)).eval z = 0) :
    ∃ x : ρ ⊗[ℂ] B, x ≠ 0 ∧ (∀ i ∈ I, ρ.representation.tprod B.representation i x = x) ∧
      x = (z * (ν g : ℂ) ^ a) • ρ.representation.tprod B.representation g x := by
  rw [LocalFactor.eulerPolynomial_eval] at h
  have hker := LinearMap.bot_lt_ker_of_det_eq_zero h
  rw [bot_lt_iff_ne_bot, Submodule.ne_bot_iff] at hker
  obtain ⟨w, hw, hw0⟩ := hker
  rw [LinearMap.mem_ker] at hw
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    apply hw0
    funext j
    by_contra hj
    exact hcon ⟨j, hj⟩
  have hj0 : j.val = 0 := by
    have := j.isLt
    omega
  have hwj := congrFun hw j
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.zero_apply, sub_eq_zero] at hwj
  refine ⟨(w j).val, fun h0 => hj (Subtype.ext h0), fun i hi => (w j).property ⟨i, hi⟩, ?_⟩
  have hval := congrArg Subtype.val hwj
  rw [blockPairKernelOperator, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    hj0] at hval
  simp only [Nat.add_zero, Nat.sub_zero] at hval
  rw [mul_smul]
  exact hval

/-- The dual-side version of `exists_eigen_of_blockPair`: a zero at `w` of the Euler
polynomial of `blockPairKernelOperator ν (χ ⊗ ρ'^∨) B^∨ a 0 I g`, with `χ` trivial on `I`,
gives a nonzero `I`-fixed vector `x` of `ρ'^∨ ⊗ B^∨` with `x = w ν(g)^a χ(g) g x`. -/
theorem exists_eigen_of_dualBlockPair (ρ' : FiniteRepresentation.{0, uG, uV} ℂ G)
    (B : FiniteRepresentation.{0, uG, uW} ℂ G) (χ : G →* ℂˣ) (hχ : ∀ i ∈ I, χ i = 1)
    (a : ℕ) (g : G) (w : ℂ)
    (h : (LocalFactor.eulerPolynomial (blockPairKernelOperator ν
      (FiniteRepresentation.twist χ (FiniteRepresentation.dual ρ'))
      (FiniteRepresentation.dual B) a 0 I g)).eval w = 0) :
    ∃ x : Module.Dual ℂ ρ' ⊗[ℂ] Module.Dual ℂ B, x ≠ 0 ∧
      (∀ i ∈ I, ρ'.representation.dual.tprod B.representation.dual i x = x) ∧
      x = (w * (ν g : ℂ) ^ a * (χ g : ℂ)) • ρ'.representation.dual.tprod B.representation.dual g x := by
  obtain ⟨x, hx0, hxI, hxg⟩ := exists_eigen_of_blockPair ν I
    (FiniteRepresentation.twist χ (FiniteRepresentation.dual ρ')) (FiniteRepresentation.dual B)
    a g w h
  have htw : ∀ g' : G, (FiniteRepresentation.twist χ (FiniteRepresentation.dual ρ')).representation.tprod
      (FiniteRepresentation.dual B).representation g' x =
        (χ g' : ℂ) • ρ'.representation.dual.tprod B.representation.dual g' x := by
    intro g'
    change TensorProduct.map ((χ g' : ℂ) • ρ'.representation.dual g')
      (B.representation.dual g') x = _
    rw [TensorProduct.map_smul_left]
    rfl
  refine ⟨x, hx0, fun i hi => ?_, ?_⟩
  · have hi' := hxI i hi
    rw [htw, hχ i hi, Units.val_one, one_smul] at hi'
    exact hi'
  · rw [htw] at hxg
    rw [mul_smul]
    exact hxg

end BlockEigen

section Core

open TensorProduct

variable {G : Type uG} [Group G]

/-- **Twisted Schur argument.** Let `ρ, ρ', B` be irreducible, let `t ∈ ρ ⊗ B` and
`s ∈ ρ'^∨ ⊗ B^∨` be nonzero vectors fixed by `I` on which `Φ` acts by `c₁` and `c₂`,
where every element is a power of `Φ` modulo `I` and `ν` is trivial on `I`.
If `ν(Φ)^m c₁ c₂ = 1`, then `ρ' ≅ ν^m ρ`. -/
theorem isIsomorphic_twist_of_eigenvectors (I : Subgroup G) (Φ : G) (ν : G →* ℂˣ)
    (hν : ∀ i ∈ I, ν i = 1) (hdec : ∀ g : G, ∃ k : ℤ, g * (Φ ^ k)⁻¹ ∈ I)
    (ρ ρ' : FiniteRepresentation.{0, uG, uV} ℂ G) (B : FiniteRepresentation.{0, uG, uW} ℂ G)
    (hρ : ρ.IsIrreducible) (hρ' : ρ'.IsIrreducible) (hB : B.IsIrreducible) (m : ℕ)
    (c₁ c₂ : ℂ) (hc : (ν Φ : ℂ) ^ m * (c₁ * c₂) = 1)
    (t : ρ ⊗[ℂ] B) (ht : t ≠ 0)
    (htI : ∀ i ∈ I, ρ.representation.tprod B.representation i t = t)
    (htΦ : ρ.representation.tprod B.representation Φ t = c₁ • t)
    (s : Module.Dual ℂ ρ' ⊗[ℂ] Module.Dual ℂ B) (hs : s ≠ 0)
    (hsI : ∀ i ∈ I, ρ'.representation.dual.tprod B.representation.dual i s = s)
    (hsΦ : ρ'.representation.dual.tprod B.representation.dual Φ s = c₂ • s) :
    FiniteRepresentation.IsIsomorphic ρ' (FiniteRepresentation.twist (ν ^ m) ρ) := by
  have hc₁ : c₁ ≠ 0 := by rintro rfl; simp at hc
  have hc₂ : c₂ ≠ 0 := by rintro rfl; simp at hc
  have hνm : (ν Φ : ℂ) ^ m = (c₁ * c₂)⁻¹ := eq_inv_of_mul_eq_one_left hc
  -- every element acts on `t` and `s` by scalars `c`, `d` with `(c d)⁻¹ = ν(g)^m`
  have hscal : ∀ g : G, ∃ c d : ℂ, c ≠ 0 ∧ d ≠ 0 ∧ (c * d)⁻¹ = (ν g : ℂ) ^ m ∧
      TensorProduct.map (ρ.representation g) (B.representation g) t = c • t ∧
      TensorProduct.map (ρ'.representation.dual g) (B.representation.dual g) s = d • s := by
    intro g
    obtain ⟨k, hk⟩ := hdec g
    refine ⟨c₁ ^ k, c₂ ^ k, zpow_ne_zero k hc₁, zpow_ne_zero k hc₂, ?_,
      eigen_of_mem _ I Φ t c₁ hc₁ htI htΦ g k hk,
      eigen_of_mem _ I Φ s c₂ hc₂ hsI hsΦ g k hk⟩
    have hνg : (ν g : ℂ) = (ν Φ : ℂ) ^ k := by
      have hg : g = (g * (Φ ^ k)⁻¹) * Φ ^ k := by group
      rw [hg, map_mul, hν _ hk, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
    have hcomm : ((ν Φ : ℂ) ^ k) ^ m = ((ν Φ : ℂ) ^ m) ^ k := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast (ν Φ : ℂ) m, ← zpow_mul, mul_comm]
    rw [hνg, hcomm, hνm, inv_zpow, mul_zpow]
  -- the contraction maps
  let gt : Module.Dual ℂ ρ →ₗ[ℂ] B := contrLeft t
  let ft : Module.Dual ℂ B →ₗ[ℂ] ρ := contrRight t
  let hs' : ρ' →ₗ[ℂ] Module.Dual ℂ B := contrLeft s ∘ₗ Module.Dual.eval ℂ ρ'
  -- equivariance of `gt`
  have hgt : ∀ g α, ∃ c : ℂ, B.representation g (gt α) = gt (c • (α ∘ₗ ρ.representation g⁻¹)) := by
    intro g α
    obtain ⟨c, d, -, -, -, htg, -⟩ := hscal g
    refine ⟨c, ?_⟩
    have h := contrLeft_map t (α ∘ₗ ρ.representation g⁻¹) (ρ.representation g) (B.representation g)
    rw [htg, contrLeft_smul, LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_eq_id, LinearMap.comp_id] at h
    rw [map_smul]
    exact h.symm
  -- equivariance of the composite `ft ∘ hs'`
  have hHg : ∀ g a, ft (hs' (ρ'.representation g a)) =
      ((ν g : ℂ) ^ m) • ρ.representation g (ft (hs' a)) := by
    intro g a
    obtain ⟨c, d, hc0, hd0, hcd, htg, hsg⟩ := hscal g
    have h1 := contrRight_map t (hs' a ∘ₗ B.representation g⁻¹) (ρ.representation g)
      (B.representation g)
    rw [htg, contrRight_smul, LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_eq_id, LinearMap.comp_id] at h1
    have h2 := contrLeft_map s (Module.Dual.eval ℂ ρ' (ρ'.representation g a))
      (ρ'.representation.dual g) (B.representation.dual g)
    have he : Module.Dual.eval ℂ ρ' (ρ'.representation g a) ∘ₗ ρ'.representation.dual g =
        Module.Dual.eval ℂ ρ' a := by
      ext φ
      change φ (ρ'.representation g⁻¹ (ρ'.representation g a)) = φ a
      rw [Representation.inv_self_apply]
    rw [hsg, contrLeft_smul, he] at h2
    have h3 : hs' (ρ'.representation g a) = d⁻¹ • B.representation.dual g (hs' a) := by
      change contrLeft s (Module.Dual.eval ℂ ρ' (ρ'.representation g a)) =
        d⁻¹ • B.representation.dual g (contrLeft s (Module.Dual.eval ℂ ρ' a))
      rw [← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have h4 : B.representation.dual g (hs' a) = hs' a ∘ₗ B.representation g⁻¹ := rfl
    rw [h3, map_smul, h4, ← hcd, ← h1, smul_smul]
    congr 1
    field_simp
  -- `gt` is surjective, since its range is a nonzero subrepresentation of `B`
  have hrange : LinearMap.range gt = ⊤ := by
    rcases stable_eq_bot_or_eq_top B.representation hB (LinearMap.range gt) (by
      rintro g v ⟨α, rfl⟩
      obtain ⟨c, hcα⟩ := hgt g α
      exact ⟨_, hcα.symm⟩) with h | h
    · exfalso
      apply ht
      apply eq_zero_of_dualDistrib t
      intro α β
      rw [← apply_contrLeft]
      change β (gt α) = 0
      rw [LinearMap.range_eq_bot.mp h, LinearMap.zero_apply, map_zero]
    · exact h
  -- hence `ft` is injective
  have hftinj : Function.Injective ft := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    refine LinearMap.ext fun w => ?_
    obtain ⟨α, rfl⟩ : w ∈ LinearMap.range gt := hrange ▸ Submodule.mem_top
    change β (contrLeft t α) = 0
    rw [apply_contrLeft, ← apply_contrRight]
    change α (ft β) = 0
    rw [hβ, map_zero]
  -- `hs'` is nonzero
  have hs'ne : ∃ a, hs' a ≠ 0 := by
    by_contra hcon'
    have hcon : ∀ a, hs' a = 0 := fun a => by
      by_contra h
      exact hcon' ⟨a, h⟩
    apply hs
    apply eq_zero_of_dualDistrib s
    intro Φ₁ Φ₂
    obtain ⟨a, rfl⟩ := (Module.evalEquiv ℂ ρ').surjective Φ₁
    obtain ⟨b, rfl⟩ := (Module.evalEquiv ℂ B).surjective Φ₂
    rw [← apply_contrLeft, Module.evalEquiv_apply, Module.evalEquiv_apply]
    change Module.Dual.eval ℂ B b (hs' a) = 0
    rw [hcon a, map_zero]
  -- the composite is a nonzero twisted intertwiner, hence bijective
  let H : ρ' →ₗ[ℂ] ρ := ft ∘ₗ hs'
  obtain ⟨a₀, ha₀⟩ := hs'ne
  have hH0 : H a₀ ≠ 0 := fun h => ha₀ (hftinj (by rw [map_zero]; exact h))
  have hinj : Function.Injective H := by
    rcases stable_eq_bot_or_eq_top ρ'.representation hρ' (LinearMap.ker H) (by
      intro g v hv
      rw [LinearMap.mem_ker] at hv ⊢
      change ft (hs' (ρ'.representation g v)) = 0
      rw [hHg]
      change _ • ρ.representation g (H v) = 0
      rw [hv, map_zero, smul_zero]) with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exfalso
      apply hH0
      rw [← LinearMap.mem_ker, h]
      exact Submodule.mem_top
  have hsurj : Function.Surjective H := by
    rcases stable_eq_bot_or_eq_top ρ.representation hρ (LinearMap.range H) (by
      rintro g v ⟨a, rfl⟩
      refine ⟨((ν g : ℂ) ^ m)⁻¹ • ρ'.representation g a, ?_⟩
      change ft (hs' (((ν g : ℂ) ^ m)⁻¹ • ρ'.representation g a)) =
        ρ.representation g (ft (hs' a))
      rw [map_smul, map_smul, hHg, smul_smul,
        inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), one_smul]) with h | h
    · exfalso
      apply hH0
      have hmem : H a₀ ∈ LinearMap.range H := ⟨a₀, rfl⟩
      rw [h] at hmem
      exact hmem
    · exact LinearMap.range_eq_top.mp h
  refine ⟨Representation.IntertwiningMap.ofBijective
    ⟨H, fun g => LinearMap.ext fun a => ?_⟩ ⟨hinj, hsurj⟩⟩
  change ft (hs' (ρ'.representation g a)) = ((ν ^ m) g : ℂ) • ρ.representation g (ft (hs' a))
  rw [hHg, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]

/-- A representation with an element of norm-`< 1` twist eigenvalue relation is not
isomorphic to its twist: comparing determinants at `Φ` gives `χ(Φ)^d = 1`. -/
theorem not_isIsomorphic_twist_self (ρ : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hρ : ρ.IsIrreducible) (χ : G →* ℂˣ) (Φ : G) (hχ : ‖(χ Φ : ℂ)‖ < 1) :
    ¬ FiniteRepresentation.IsIsomorphic ρ (FiniteRepresentation.twist χ ρ) := by
  rintro ⟨e⟩
  have := nontrivial_of_isIrreducible ρ.representation hρ
  have h := congrArg LinearMap.det (e.conj_apply_self Φ)
  rw [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj] at h
  change _ = LinearMap.det ((χ Φ : ℂ) • ρ.representation Φ) at h
  rw [LinearMap.det_smul] at h
  have hne : LinearMap.det (ρ.representation Φ) ≠ 0 := by
    have h1 : ρ.representation Φ * ρ.representation Φ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h2 := congrArg LinearMap.det h1
    rw [map_mul, map_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have h1 : (χ Φ : ℂ) ^ Module.finrank ℂ ρ = 1 := by
    apply mul_right_cancel₀ hne
    rw [one_mul]
    exact h.symm
  have hpos : 0 < Module.finrank ℂ ρ := Module.finrank_pos
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_lt_one₀ (norm_nonneg _) hχ hpos.ne').ne h2

end Core

section Generic

variable {G : Type uG} [Group G] (ν : G →* ℂˣ) (I : Subgroup G) [I.Normal] (Φ : G)

/-- The Euler polynomial of `σ ⊗ (B, 0)` for `σ` equivalent to a sum of blocks. -/
theorem eulerPolynomial_tensor_eq_prod (hν : ∀ i : I, ν i = 1) {k : ℕ}
    (ρ : Fin k → FiniteRepresentation.{0, uG, uV} ℂ G) (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (σ : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (e : WeilDeligneRepresentation.Equiv σ
      (WeilDeligneRepresentation.directSum fun i => WeilDeligneRepresentation.block ν (ρ i) (n i)))
    (B : FiniteRepresentation.{0, uG, uW} ℂ G) :
    eulerPolynomial (WeilDeligneRepresentation.tensor σ
        (WeilDeligneRepresentation.zeroMonodromy ν B)) I Φ =
      ∏ i, LocalFactor.eulerPolynomial (blockPairKernelOperator ν (ρ i) B (n i - 1) 0 I Φ) := by
  rw [eulerPolynomial_tensor_of_equiv_directSum ν I σ _ e]
  refine Finset.prod_congr rfl fun i _ => ?_
  have key : ∀ m : ℕ, 0 < m →
      eulerPolynomial (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν (ρ i) m)
        (WeilDeligneRepresentation.zeroMonodromy ν B)) I Φ =
      LocalFactor.eulerPolynomial (blockPairKernelOperator ν (ρ i) B (m - 1) 0 I Φ) := by
    intro m hm
    cases m with
    | zero => omega
    | succ a => exact eulerPolynomial_block_zeroMonodromy ν I hν _ _ a Φ
  exact key (n i) (hn i)

/-- The Euler polynomial of `σ^∨ ⊗ (B, 0)^∨` for `σ` equivalent to a sum of blocks. -/
theorem eulerPolynomial_tensor_dual_eq_prod (hν : ∀ i : I, ν i = 1) {k : ℕ}
    (ρ : Fin k → FiniteRepresentation.{0, uG, uV} ℂ G) (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (σ : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (e : WeilDeligneRepresentation.Equiv σ
      (WeilDeligneRepresentation.directSum fun i => WeilDeligneRepresentation.block ν (ρ i) (n i)))
    (B : FiniteRepresentation.{0, uG, uW} ℂ G) :
    eulerPolynomial (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.dual σ)
        (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.zeroMonodromy ν B))) I Φ =
      ∏ i, LocalFactor.eulerPolynomial (blockPairKernelOperator ν
        (FiniteRepresentation.twist (ν ^ (1 - (n i : ℤ))) (FiniteRepresentation.dual (ρ i)))
        (FiniteRepresentation.dual B) (n i - 1) 0 I Φ) := by
  rw [eulerPolynomial_tensor_dual_of_equiv_directSum ν I σ _ e]
  refine Finset.prod_congr rfl fun i _ => ?_
  have key : ∀ m : ℕ, 0 < m →
      eulerPolynomial (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.block ν (ρ i) m))
        (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.zeroMonodromy ν B))) I Φ =
      LocalFactor.eulerPolynomial (blockPairKernelOperator ν
        (FiniteRepresentation.twist (ν ^ (1 - (m : ℤ))) (FiniteRepresentation.dual (ρ i)))
        (FiniteRepresentation.dual B) (m - 1) 0 I Φ) := by
    intro m hm
    cases m with
    | zero => omega
    | succ a => exact eulerPolynomial_dual_block_dual_zeroMonodromy ν I hν _ _ a Φ
  exact key (n i) (hn i)

/-- **The non-juxtaposed case over an abstract Weil-type group.** Let every element be a
power of `Φ` modulo the normal subgroup `I`, let `ν` be trivial on `I` with
`ν(Φ) = q⁻¹`, `q > 1`. If `σ ≅ ⊕ ρ_i ⊗ Sp(n_i)` with `ρ_i` irreducible, `n_i ≥ 1` and
`ρ_j ≇ ν^(n_i) ρ_i` for `i ≠ j`, and `B` is irreducible, then the Euler polynomials of
`σ ⊗ (B, 0)` at `z ≠ 0` and of `σ^∨ ⊗ (B, 0)^∨` at `q⁻¹ z⁻¹` do not both vanish. -/
theorem not_common_zero (hν : ∀ i ∈ I, ν i = 1) (hdec : ∀ g : G, ∃ k : ℤ, g * (Φ ^ k)⁻¹ ∈ I)
    (q : ℕ) (hq : 1 < q) (hνΦ : (ν Φ : ℂ) = (q : ℂ)⁻¹) {k : ℕ}
    (ρ : Fin k → FiniteRepresentation.{0, uG, uV} ℂ G) (n : Fin k → ℕ)
    (hirr : ∀ i, (ρ i).IsIrreducible) (hn : ∀ i, 0 < n i)
    (hjux : ∀ i j, i ≠ j →
      ¬ FiniteRepresentation.IsIsomorphic (ρ j) (FiniteRepresentation.twist (ν ^ n i) (ρ i)))
    (σ : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (e : WeilDeligneRepresentation.Equiv σ
      (WeilDeligneRepresentation.directSum fun i => WeilDeligneRepresentation.block ν (ρ i) (n i)))
    (B : FiniteRepresentation.{0, uG, uW} ℂ G) (hB : B.IsIrreducible) (z : ℂ) (hz : z ≠ 0)
    (h1 : (eulerPolynomial (WeilDeligneRepresentation.tensor σ
      (WeilDeligneRepresentation.zeroMonodromy ν B)) I Φ).eval z = 0)
    (h2 : (eulerPolynomial (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.dual σ)
      (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.zeroMonodromy ν B))) I Φ).eval
        ((q : ℂ)⁻¹ * z⁻¹) = 0) :
    False := by
  have hν' : ∀ i : I, ν i = 1 := fun i => hν i i.2
  have hu : (ν Φ : ℂ) ≠ 0 := Units.ne_zero _
  -- a vanishing block factor on each side
  rw [eulerPolynomial_tensor_eq_prod ν I Φ hν' ρ n hn σ e B, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at h1
  obtain ⟨i, -, hi⟩ := h1
  rw [eulerPolynomial_tensor_dual_eq_prod ν I Φ hν' ρ n hn σ e B, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at h2
  obtain ⟨j, -, hj⟩ := h2
  -- the eigenvector in `ρ_i ⊗ B`
  obtain ⟨t, ht0, htI, htΦ⟩ := exists_eigen_of_blockPair ν I (ρ i) B (n i - 1) Φ z hi
  have hne₁ : z * (ν Φ : ℂ) ^ (n i - 1) ≠ 0 := mul_ne_zero hz (pow_ne_zero _ hu)
  have htΦ' : (ρ i).representation.tprod B.representation Φ t =
      (z * (ν Φ : ℂ) ^ (n i - 1))⁻¹ • t := by
    calc (ρ i).representation.tprod B.representation Φ t
        = (z * (ν Φ : ℂ) ^ (n i - 1))⁻¹ • ((z * (ν Φ : ℂ) ^ (n i - 1)) •
            (ρ i).representation.tprod B.representation Φ t) := by
          rw [smul_smul, inv_mul_cancel₀ hne₁, one_smul]
      _ = (z * (ν Φ : ℂ) ^ (n i - 1))⁻¹ • t := by rw [← htΦ]
  -- the eigenvector in `ρ_j^∨ ⊗ B^∨`
  have hw' : (q : ℂ)⁻¹ * z⁻¹ ≠ 0 :=
    mul_ne_zero (inv_ne_zero (by exact_mod_cast (by omega : q ≠ 0))) (inv_ne_zero hz)
  obtain ⟨s, hs0, hsI, hsΦ⟩ := exists_eigen_of_dualBlockPair ν I (ρ j) B
    (ν ^ (1 - (n j : ℤ))) (fun i hi => by rw [MonoidHom.zpow_apply, hν i hi, one_zpow])
    (n j - 1) Φ _ hj
  have hcancel : (ν Φ : ℂ) ^ (n j - 1) * ((ν ^ (1 - (n j : ℤ))) Φ : ℂ) = 1 := by
    rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val, ← zpow_natCast, ← zpow_add₀ hu]
    have hexp : ((n j - 1 : ℕ) : ℤ) + (1 - (n j : ℤ)) = 0 := by
      have := hn j
      omega
    rw [hexp, zpow_zero]
  rw [mul_assoc, hcancel, mul_one] at hsΦ
  have hsΦ' : (ρ j).representation.dual.tprod B.representation.dual Φ s =
      ((q : ℂ)⁻¹ * z⁻¹)⁻¹ • s := by
    calc (ρ j).representation.dual.tprod B.representation.dual Φ s
        = ((q : ℂ)⁻¹ * z⁻¹)⁻¹ • (((q : ℂ)⁻¹ * z⁻¹) •
            (ρ j).representation.dual.tprod B.representation.dual Φ s) := by
          rw [smul_smul, inv_mul_cancel₀ hw', one_smul]
      _ = ((q : ℂ)⁻¹ * z⁻¹)⁻¹ • s := by rw [← hsΦ]
  -- the scalar relation `ν(Φ)^(n_i) c₁ c₂ = 1`
  have hc : (ν Φ : ℂ) ^ n i * ((z * (ν Φ : ℂ) ^ (n i - 1))⁻¹ * ((q : ℂ)⁻¹ * z⁻¹)⁻¹) = 1 := by
    obtain ⟨a, ha⟩ : ∃ a, n i = a + 1 := ⟨n i - 1, by have := hn i; omega⟩
    rw [ha, Nat.add_sub_cancel, pow_succ, ← hνΦ]
    field_simp
  -- the twisted Schur argument
  have hiso := isIsomorphic_twist_of_eigenvectors I Φ ν hν hdec (ρ i) (ρ j) B
    (hirr i) (hirr j) hB (n i) _ _ hc t ht0 htI htΦ' s hs0 hsI hsΦ'
  by_cases hij : i = j
  · subst hij
    have hnorm : ‖(((ν ^ n i) Φ : ℂˣ) : ℂ)‖ < 1 := by
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hνΦ, norm_pow, norm_inv,
        Complex.norm_natCast]
      have hq' : (1 : ℝ) < q := by exact_mod_cast hq
      exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hq')
        (by have := hn i; omega)
    exact not_isIsomorphic_twist_self (ρ i) (hirr i) (ν ^ n i) Φ hnorm hiso
  · exact hjux i j hij hiso

end Generic

section Local

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Every element of the local Weil group is a power of the chosen geometric Frobenius
modulo inertia. -/
theorem mul_inv_frobenius_zpow_mem_inertia (g : localWeilGroup F) :
    g * (localGeometricFrobenius F ^ localDegreeInt F g)⁻¹ ∈ localInertia F := by
  have hd : localDegree F (localGeometricFrobenius F ^ localDegreeInt F g) = localDegree F g := by
    rw [map_zpow, localGeometricFrobenius_degree]
    apply Multiplicative.toAdd.injective
    simp [localDegreeInt]
  change localDegree F (g * (localGeometricFrobenius F ^ localDegreeInt F g)⁻¹) = 1
  rw [map_mul, map_inv, hd, mul_inv_cancel]

end Local

end Langlands.Global.WeilPoleRegionNonJuxtaposed

namespace Langlands.Global

open Langlands.Weil.Local WeilPoleRegion WeilPoleRegionNonJuxtaposed

/-- **Henniart 1986, Proposition 4.5(i), second case.** If `σ ≅ ⊕ ρ_i ⊗ Sp(n_i)` with
`ρ_i` irreducible, `n_i ≥ 1` and no two blocks juxtaposed, and `B` is irreducible, then
`P_{σ ⊗ (B, 0)}` and the reflected `P_{σ^∨ ⊗ (B, 0)^∨}` have no common zero. -/
theorem nonJuxtaposedPoleRegionStatement : NonJuxtaposedPoleRegionStatement.{u, v, w} := by
  intro p _ F k ρ n hirr hn hjux σ ⟨e⟩ B hB σ' z hz hboth
  exact not_common_zero (localNormCharacter F).toMonoidHom (localInertia F)
    (localGeometricFrobenius F) (fun i hi => localNormCharacter_on_inertia F ⟨i, hi⟩)
    (fun g => ⟨_, mul_inv_frobenius_zpow_mem_inertia F g⟩) (residueCardinality F)
    F.canonicalTopologicalData.residueCardinality_gt_one
    (localNormCharacter_geometricFrobenius F) (fun i => (ρ i).val) n hirr hn
    (fun i j hij hiso => hjux i j hij (Or.inl hiso)) σ.val e B.val hB z hz hboth.1 hboth.2

end Langlands.Global
