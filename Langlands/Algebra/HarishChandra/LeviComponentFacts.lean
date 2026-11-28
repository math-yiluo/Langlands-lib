import Langlands.Algebra.HarishChandra.SplitCartanLevi
import Langlands.Algebra.HarishChandra.ParabolicIndependenceStatement
import Langlands.Algebra.EnvelopingMapInjective
import Langlands.Algebra.LieCasimir

/-! # Facts on Levi components used for the independence of the parabolic

This file collects the ingredients of the proof of `ParabolicIndependenceStatement` that do not
involve Verma modules: the trace of a diagonalizable endomorphism on a span of eigenvectors, the
description of the positive eigenspaces of `ad X` through a weight basis, the centrality of the
Levi component of a central element (Knapp–Vogan, Lemma 4.123 (c), mirrored), and the behaviour
of the shift `τ_λ` on centres and on mirror Verma right ideals. -/

noncomputable section

universe v w

set_option autoImplicit false

namespace Langlands.Algebra.HarishChandra

open LieModule Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

section Trace

variable {L : Type v} [AddCommGroup L] [Module ℂ L]

/-- The trace of an endomorphism on the span of some of its eigenvectors from a basis is the sum
of the corresponding eigenvalues. -/
theorem trace_restrict_span_eigen {n : ℕ} (b : Module.Basis (Fin n) ℂ L) (c : Fin n → ℂ)
    (T : L →ₗ[ℂ] L) (hT : ∀ a, T (b a) = c a • b a) (S : Finset (Fin n))
    {V : Submodule ℂ L} (hV : V = Submodule.span ℂ (b '' ↑S)) (hmaps : Set.MapsTo T V V) :
    LinearMap.trace ℂ V (T.restrict hmaps) = ∑ a ∈ S, c a := by
  subst hV
  have hli : LinearIndependent ℂ (fun a : S => b a) :=
    b.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun a : S => b a) = b '' ↑S := by
    ext x
    simp
  let bV : Module.Basis S ℂ (Submodule.span ℂ (b '' ↑S)) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ (by rw [hrange]))
  have hbV : ∀ a : S, (bV a : L) = b a := fun a => by
    simp [bV]
  rw [LinearMap.trace_eq_matrix_trace ℂ bV, Matrix.trace, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have h1 : T.restrict hmaps (bV a) = c a • bV a := by
    apply Subtype.ext
    show T (bV a : L) = c a • (bV a : L)
    rw [hbV, hT]
  rw [h1, map_smul, bV.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one]

end Trace

section Eigen

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L] {H : LieSubalgebra ℂ L} {n : ℕ}
  (b : Module.Basis (Fin n) ℂ L) (w : Fin n → H → ℂ)
  (hw : ∀ a (h : H), ⁅(h : L), b a⁆ = w a h • b a)

include hw in
/-- For integral weights at `X`, the positive eigenspaces of `ad X` are spanned by the basis
vectors of positive weight at `X`. -/
theorem positiveEigenSubmodule_eq_span (X : H) (hint : ∀ a, ∃ k : ℤ, w a X = k) :
    positiveEigenSubmodule (X : L) = Submodule.span ℂ (b '' {a | 0 < (w a X).re}) := by
  apply le_antisymm
  · refine iSup₂_le fun k hk x hx => ?_
    rw [Module.End.mem_eigenspace_iff, LieAlgebra.ad_apply] at hx
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ?_, rfl⟩)
    change 0 < (w a X).re
    have h1 := repr_lie_basis b w hw X x a
    rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h2 : w a X = k := (mul_right_cancel₀ (Finsupp.mem_support_iff.mp ha) h1).symm
    rw [h2, Complex.natCast_re]
    exact_mod_cast hk
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨k, hk⟩ := hint a
    have hk0 : 0 < k := by
      have : (0 : ℝ) < (k : ℂ).re := hk ▸ ha
      rw [Complex.intCast_re] at this
      exact_mod_cast this
    have hkn : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0.le]
    have hmem : b a ∈ (LieAlgebra.ad ℂ L (X : L)).eigenspace ((k.toNat : ℕ) : ℂ) := by
      rw [Module.End.mem_eigenspace_iff, LieAlgebra.ad_apply, hw, hk, hkn]
    exact Submodule.mem_iSup_of_mem k.toNat (Submodule.mem_iSup_of_mem (by omega) hmem)

include hw in
/-- An element commutes with `X` exactly when its coordinates are supported on the indices of
weight zero at `X`. -/
theorem lie_eq_zero_iff (X : H) (x : L) :
    ⁅(X : L), x⁆ = 0 ↔ ∀ a ∈ (b.repr x).support, w a X = 0 := by
  constructor
  · intro hx a ha
    have h1 := repr_lie_basis b w hw X x a
    rw [hx, map_zero, Finsupp.zero_apply] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (Finsupp.mem_support_iff.mp ha)
  · intro h
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum, lie_sum]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [lie_smul, hw, h a ha, zero_smul, smul_zero]

end Eigen

section Commutator

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]

local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

/-- An element commuting with `X` preserves the positive eigenspaces of `ad X`. -/
theorem lie_mem_positiveEigenSubmodule {X y : L} (hy : ⁅X, y⁆ = 0) {x : L}
    (hx : x ∈ positiveEigenSubmodule X) : ⁅y, x⁆ ∈ positiveEigenSubmodule X := by
  induction hx using Submodule.iSup_induction' with
  | mem k x hx =>
    induction hx using Submodule.iSup_induction' with
    | mem hk x hx =>
      refine Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk ?_)
      rw [Module.End.mem_eigenspace_iff, LieAlgebra.ad_apply] at hx ⊢
      rw [leibniz_lie, hy, zero_lie, zero_add, hx, lie_smul]
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h₁ h₂ => rw [lie_add]; exact Submodule.add_mem _ h₁ h₂
  | zero => rw [lie_zero]; exact Submodule.zero_mem _
  | add x x' _ _ h₁ h₂ => rw [lie_add]; exact Submodule.add_mem _ h₁ h₂

/-- The commutator with a generator that normalizes `V` preserves the right ideal `V U(𝔤)`. -/
theorem commutatorMap_mem_generatorRightIdeal {V : Submodule ℂ L} {y : L}
    (hV : ∀ x ∈ V, ⁅y, x⁆ ∈ V) {u : U} (hu : u ∈ generatorRightIdeal V) :
    commutatorMap y u ∈ generatorRightIdeal V := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, v, rfl⟩ := hu
    rw [commutatorMap_mul, commutatorMap_ι]
    exact Submodule.add_mem _ (generator_mul_mem_generatorRightIdeal _ (hV x hx) _)
      (generator_mul_mem_generatorRightIdeal _ hx _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x x' _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul t x _ h => rw [map_smul]; exact Submodule.smul_mem _ t h

/-- An element commuting with all generators is central. -/
theorem mem_center_of_commute_ι {x : U} (hx : ∀ m : L, ι m * x = x * ι m) :
    x ∈ Subalgebra.center ℂ U := by
  rw [Subalgebra.mem_center_iff]
  intro g
  have hg : g ∈ Algebra.adjoin ℂ (Set.range (UniversalEnvelopingAlgebra.ι ℂ : L → U)) := by
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  induction hg using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨m, rfl⟩ := hg
    exact hx m
  | algebraMap r => exact Algebra.commutes r x
  | add g g' _ _ h₁ h₂ => rw [add_mul, mul_add, h₁, h₂]
  | mul g g' _ _ h₁ h₂ => rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc]

end Commutator

section LeviComponent

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L] {M : Type w} [LieRing M] [LieAlgebra ℂ M]

/-- **The Levi component of a central element is central** (Knapp–Vogan, Lemma 4.123 (c), in
mirror form). -/
theorem mem_center_of_sub_mem_generatorRightIdeal [FiniteDimensional ℂ L]
    [FiniteDimensional ℂ M] {H : LieSubalgebra ℂ L} (hC : IsSplitCartan H) (ι : M →ₗ⁅ℂ⁆ L)
    (hinj : Function.Injective ι) (X : H)
    (hint : ∀ χ : H → ℂ, weightSpace L χ ≠ ⊥ → ∃ k : ℤ, χ X = k)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X : L)))
    {z : UniversalEnvelopingAlgebra ℂ L} (hz : z ∈ Subalgebra.center ℂ _)
    {y : UniversalEnvelopingAlgebra ℂ M}
    (hy : z - UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp ι) y ∈
      generatorRightIdeal (positiveEigenSubmodule (X : L))) :
    y ∈ Subalgebra.center ℂ _ := by
  set j := UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp ι) with hj
  obtain ⟨r, b, χ, hb, -, hanti⟩ := hC.exists_ordered_weight_basis X
  have hw : ∀ a (h : H), ⁅(h : L), b a⁆ = χ a h • b a := fun a h => (mem_weightSpace _ _).mp (hb a) h
  have hint' : ∀ a, ∃ k : ℤ, χ a X = k := fun a =>
    hint _ (weightSpace_ne_bot_of_mem (hb a) (b.ne_zero a))
  have hpos : generatorRightIdeal (positiveEigenSubmodule (X : L)) =
      realPositiveGeneratorSpan b (realWeight χ X) := by
    rw [positiveEigenSubmodule_eq_span b χ hw X hint', generatorRightIdeal_span_image]
    rfl
  have hker : ∀ m : M, ⁅(X : L), ι m⁆ = 0 := fun m => by
    have : ι m ∈ LinearMap.ker (LieAlgebra.ad ℂ L (X : L)) := hrange ▸ ⟨m, rfl⟩
    simpa using this
  have hzero : ∀ u, j u ∈ (realZeroGeneratorSubalgebra b (realWeight χ X)).toSubmodule := by
    intro u
    have hu : u ∈ Algebra.adjoin ℂ (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        M → UniversalEnvelopingAlgebra ℂ M)) := by
      rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
      trivial
    have hmap : j u ∈ (Algebra.adjoin ℂ (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        M → UniversalEnvelopingAlgebra ℂ M))).map j := ⟨u, hu, rfl⟩
    rw [AlgHom.map_adjoin] at hmap
    refine (Algebra.adjoin_le ?_ : Algebra.adjoin ℂ _ ≤ realZeroGeneratorSubalgebra b
      (realWeight χ X)) hmap
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    rw [hj, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply]
    have hsupp := (lie_eq_zero_iff b χ hw X (ι m)).mp (hker m)
    rw [← b.linearCombination_repr (ι m), Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Subalgebra.sum_mem _ fun a ha => ?_
    rw [map_smul]
    refine Subalgebra.smul_mem _ (Algebra.subset_adjoin
      (show UniversalEnvelopingAlgebra.ι ℂ (b a) ∈ {u | ∃ a', realWeight χ X a' = 0 ∧
        u = UniversalEnvelopingAlgebra.ι ℂ (b a')} from ⟨a, ?_, rfl⟩)) _
    rw [realWeight, hsupp a ha, Complex.zero_re]
  apply mem_center_of_commute_ι
  intro m
  rw [← sub_eq_zero]
  apply lift_comp_injective ι hinj
  rw [map_zero]
  set u := UniversalEnvelopingAlgebra.ι ℂ m * y - y * UniversalEnvelopingAlgebra.ι ℂ m
  change j u = 0
  have hju : j u = -commutatorMap (ι m) (z - j y) := by
    rw [map_sub (commutatorMap (ι m)), commutatorMap_eq_zero_of_mem_center hz, zero_sub, neg_neg,
      commutatorMap_apply]
    simp only [u, map_sub, map_mul, hj, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply]
  have h1 : j u ∈ realPositiveGeneratorSpan b (realWeight χ X) := by
    rw [hju, ← hpos]
    exact Submodule.neg_mem _ (commutatorMap_mem_generatorRightIdeal
      (fun x hx => lie_mem_positiveEigenSubmodule (hker m) hx) hy)
  exact (Submodule.disjoint_def.mp (disjoint_real_of_antitone b χ hw X hanti)) _ h1 (hzero u)

end LeviComponent

section Shift

variable {M : Type w} [LieRing M] [LieAlgebra ℂ M]

local notation "U" => UniversalEnvelopingAlgebra ℂ M
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

theorem scalarShift_mem_center (lam : M →ₗ[ℂ] ℂ) (hlam : ∀ Y Y' : M, lam ⁅Y, Y'⁆ = 0) {y : U}
    (hy : y ∈ Subalgebra.center ℂ U) : scalarShift lam hlam y ∈ Subalgebra.center ℂ U := by
  apply mem_center_of_commute_ι
  intro m
  have hm : ι m = scalarShift lam hlam (ι m - algebraMap ℂ U (lam m)) := by
    rw [map_sub, scalarShift_ι, AlgHom.commutes, add_sub_cancel_right]
  rw [hm, ← map_mul, ← map_mul, (Subalgebra.mem_center_iff.mp hy _)]

/-- A character vanishing on brackets vanishes on nonzero weight spaces. -/
theorem eq_zero_of_mem_weightSpace (lam : M →ₗ[ℂ] ℂ) (hlam : ∀ Y Y' : M, lam ⁅Y, Y'⁆ = 0)
    {K : LieSubalgebra ℂ M} {χ : K → ℂ} (hχ : χ ≠ 0) {x : M} (hx : x ∈ weightSpace M χ) :
    lam x = 0 := by
  obtain ⟨h, hh⟩ : ∃ h, χ h ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hχ (funext hall)
  have h1 := hlam (h : M) x
  have h2 : ⁅(h : M), x⁆ = χ h • x := (mem_weightSpace _ _).mp hx h
  rw [h2, map_smul, smul_eq_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left hh

theorem eq_zero_of_mem_positiveRootSubmodule (lam : M →ₗ[ℂ] ℂ)
    (hlam : ∀ Y Y' : M, lam ⁅Y, Y'⁆ = 0) {K : LieSubalgebra ℂ M} (Y : K) {x : M}
    (hx : x ∈ positiveRootSubmodule K Y) : lam x = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem χ x hx =>
    induction hx using Submodule.iSup_induction' with
    | mem hχ x hx =>
      refine eq_zero_of_mem_weightSpace lam hlam ?_ hx
      rintro rfl
      rw [Pi.zero_apply, Complex.zero_re] at hχ
      exact lt_irrefl 0 hχ
    | zero => exact map_zero lam
    | add x x' _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
  | zero => exact map_zero lam
  | add x x' _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]

/-- An algebra map sending the generators of `R_X(λ)` into a right ideal `R` sends `R_X(λ)` into
`R`. -/
theorem map_mem_of_mem_vermaIdeal {A : Type*} [Ring A] [Algebra ℂ A] {K : LieSubalgebra ℂ M}
    (Y : K) (lam : K →ₗ[ℂ] ℂ) (ψ : U →ₐ[ℂ] A) (R : Submodule ℂ A)
    (hR : ∀ r ∈ R, ∀ a : A, r * a ∈ R)
    (hpos : ∀ x ∈ positiveRootSubmodule K Y, ψ (ι x) ∈ R)
    (hcart : ∀ h : K, ψ (ι (h : M) - algebraMap ℂ U (lam h)) ∈ R) {r : U}
    (hr : r ∈ vermaIdeal K Y lam) : ψ r ∈ R := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hr
  clear hr
  rw [map_add]
  refine R.add_mem ?_ ?_
  · induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, v, rfl⟩ := hx
      rw [map_mul]
      exact hR _ (hpos a ha) _
    | zero => rw [map_zero]; exact R.zero_mem
    | add x y _ _ h₁ h₂ => rw [map_add]; exact R.add_mem h₁ h₂
    | smul t x _ h => rw [map_smul]; exact R.smul_mem t h
  · induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, v, rfl⟩ := hx
      rw [map_mul]
      exact hR _ (hcart h) _
    | zero => rw [map_zero]; exact R.zero_mem
    | add x y _ _ h₁ h₂ => rw [map_add]; exact R.add_mem h₁ h₂
    | smul t x _ h => rw [map_smul]; exact R.smul_mem t h

/-- The shift `τ_λ` maps `R_Y(μ + λ)` into `R_Y(μ)`. -/
theorem scalarShift_mem_vermaIdeal (lam : M →ₗ[ℂ] ℂ) (hlam : ∀ Y Y' : M, lam ⁅Y, Y'⁆ = 0)
    {K : LieSubalgebra ℂ M} (Y : K) (μ : K →ₗ[ℂ] ℂ) {r : U}
    (hr : r ∈ vermaIdeal K Y (μ + lam.comp K.incl.toLinearMap)) :
    scalarShift lam hlam r ∈ vermaIdeal K Y μ := by
  refine map_mem_of_mem_vermaIdeal Y _ (scalarShift lam hlam) _
    (fun r hr a => vermaIdeal_mul_mem Y μ hr a) ?_ ?_ hr
  · intro x hx
    rw [scalarShift_ι, eq_zero_of_mem_positiveRootSubmodule lam hlam Y hx, map_zero, add_zero,
      ← mul_one (ι x)]
    exact positive_mul_mem_vermaIdeal Y μ hx 1
  · intro h
    have : scalarShift lam hlam (ι (h : M) - algebraMap ℂ U ((μ + lam.comp K.incl.toLinearMap) h)) =
        (ι (h : M) - algebraMap ℂ U (μ h)) * 1 := by
      rw [map_sub, scalarShift_ι, AlgHom.commutes, LinearMap.add_apply, LinearMap.comp_apply,
        map_add, mul_one]
      simp only [LieHom.coe_toLinearMap, LieSubalgebra.coe_incl]
      abel
    rw [this]
    exact cartan_mul_mem_vermaIdeal Y μ h 1

end Shift

end Langlands.Algebra.HarishChandra
