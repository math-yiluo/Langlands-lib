import Langlands.GroupScheme.Chevalley.RegularSubspace
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Invariant vectors in unipotent coordinate bialgebras

For a bialgebra `B` over a field in which every nonzero finite-dimensional right-translation
stable subspace contains `1`, this file proves:

* every nonzero finite-dimensional translation-stable subspace of a module mapped to `B` by a
  jointly injective family of intertwining maps contains a nonzero invariant vector;
* a bialgebra homomorphism from `B` to a bialgebra with a basis of grouplike elements factors
  through the counit.
-/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding Chevalley

/-- Vectors are separated by functionals. -/
theorem eq_of_forall_dual (K : Type*) [Field K] {B : Type*} [AddCommGroup B] [Module K B]
    {x y : B} (h : ∀ g : Module.Dual K B, g x = g y) : x = y := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro g
  rw [map_sub, h, sub_self]

/-- A bialgebra over a field is nonzero. -/
theorem one_ne_zero' (K B : Type*) [Field K] [Ring B] [Bialgebra K B] : (1 : B) ≠ 0 := by
  intro h
  have h1 := Bialgebra.counit_one (R := K) (A := B)
  rw [h, map_zero] at h1
  exact zero_ne_one h1

section Coalgebra

variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Module K B] [Coalgebra K B]

theorem counit_leftAct (θ : Module.Dual K B) (a : B) :
    counit (R := K) (leftAct θ a) = θ a := by
  rw [apply_leftAct, rightAct_counit]

/-- Coassociativity: left translations compose. -/
theorem leftAct_leftAct (ψ θ : Module.Dual K B) (a : B) :
    leftAct ψ (leftAct θ a) = leftAct (ψ ∘ₗ leftAct θ) a := by
  apply eq_of_forall_dual K
  intro g
  rw [apply_leftAct, rightAct_leftAct, apply_leftAct g (ψ ∘ₗ leftAct θ)]
  rfl

theorem leftAct_smul (c : K) (θ : Module.Dual K B) (a : B) :
    leftAct (c • θ) a = c • leftAct θ a := by
  rw [leftAct_apply, leftAct_apply, LinearMap.rTensor_smul, LinearMap.smul_apply, map_smul]

/-- Left translation along a functional pulled back by a coalgebra map. -/
theorem map_leftAct {C : Type*} [AddCommGroup C] [Module K C] [Coalgebra K C]
    (φ : B →ₗc[K] C) (χ : Module.Dual K C) (b : B) :
    φ (leftAct (χ ∘ₗ (φ : B →ₗ[K] C)) b) = leftAct χ (φ b) := by
  rw [leftAct_apply, leftAct_apply, ← CoalgHomClass.map_comp_comul_apply φ b]
  generalize comul (R := K) b = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- On a coalgebra with a basis of grouplike elements, left translation by a coordinate
functional is the coordinate projection. -/
theorem leftAct_coord_of_grouplike {ι : Type*} (g : Basis ι K B)
    (hg : ∀ i, comul (R := K) (g i) = g i ⊗ₜ[K] g i) (i : ι) (c : B) :
    leftAct (g.coord i) c = g.coord i c • g i := by
  have h : leftAct (g.coord i) = (g.coord i).smulRight (g i) := by
    apply g.ext
    intro l
    rw [LinearMap.smulRight_apply, leftAct_apply, hg l, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, Basis.coord_apply, Basis.repr_self]
    by_cases hil : i = l
    · subst hil
      rfl
    · rw [Finsupp.single_eq_of_ne hil, zero_smul, zero_smul]
  rw [h, LinearMap.smulRight_apply]

end Coalgebra

section Bialgebra

variable {K : Type*} [Field K] {B : Type*} [Ring B] [Bialgebra K B]

theorem rightAct_one (f : Module.Dual K B) : rightAct f (1 : B) = f 1 • (1 : B) := by
  rw [rightAct_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

theorem leftAct_one (f : Module.Dual K B) : leftAct f (1 : B) = f 1 • (1 : B) := by
  rw [leftAct_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

/-- An element fixed by every right translation is a constant. -/
theorem eq_counit_smul_one_of_invariant {b : B} (hb : ∀ g : Module.Dual K B, rightAct g b = g 1 • b) :
    b = counit (R := K) b • (1 : B) := by
  have h : ∀ ψ : Module.Dual K B, leftAct ψ b = ψ b • (1 : B) := by
    intro ψ
    apply eq_of_forall_dual K
    intro g
    rw [apply_leftAct, hb g, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  simpa using h counit

/-- Unipotence of a coordinate bialgebra over a field: every nonzero finite-dimensional
right-translation stable subspace contains the unit. -/
abbrev OneMemStable (K B : Type*) [Field K] [Ring B] [Bialgebra K B] : Prop :=
  ∀ V : Submodule K B, FiniteDimensional K V →
    (∀ (f : Module.Dual K B) (v : B), v ∈ V → rightAct f v ∈ V) → V ≠ ⊥ → (1 : B) ∈ V

/-- A nonzero finite-dimensional stable subspace of a module with a jointly injective family of
intertwining maps to a unipotent coordinate bialgebra contains a nonzero invariant vector. -/
theorem exists_invariant (hB : OneMemStable K B)
    {M : Type*} [AddCommGroup M] [Module K M] (T : Module.Dual K B → M →ₗ[K] M)
    {ι : Type*} (π : ι → M →ₗ[K] B)
    (hπ : ∀ i g m, π i (T g m) = rightAct g (π i m))
    (hsep : ∀ m, (∀ i, π i m = 0) → m = 0)
    (W : Submodule K M) [FiniteDimensional K W]
    (hW : ∀ g m, m ∈ W → T g m ∈ W) (hW0 : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ g, T g w = g 1 • w := by
  induction hd : finrank K W using Nat.strong_induction_on generalizing W with
  | _ d ih =>
    obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨i, hi⟩ : ∃ i, π i w₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw₀0 (hsep w₀ hc)
    by_cases hW' : W ⊓ LinearMap.ker (π i) = ⊥
    · have hV : (1 : B) ∈ W.map (π i) := by
        refine hB _ inferInstance ?_ ?_
        · rintro f _ ⟨m, hm, rfl⟩
          exact ⟨T f m, hW f m hm, hπ i f m⟩
        · intro h
          apply hi
          have : π i w₀ ∈ W.map (π i) := ⟨w₀, hw₀, rfl⟩
          rw [h] at this
          exact (Submodule.mem_bot K).1 this
      obtain ⟨w, hw, hw1⟩ := hV
      refine ⟨w, hw, ?_, fun g => ?_⟩
      · rintro rfl
        rw [map_zero] at hw1
        exact one_ne_zero' K B hw1.symm
      · have hmem : T g w - g 1 • w ∈ W ⊓ LinearMap.ker (π i) := by
          refine Submodule.mem_inf.2 ⟨W.sub_mem (hW g w hw) (W.smul_mem _ hw), ?_⟩
          rw [LinearMap.mem_ker, map_sub, map_smul, hπ, hw1, rightAct_one, sub_self]
        rw [hW'] at hmem
        exact sub_eq_zero.mp ((Submodule.mem_bot K).1 hmem)
    · have hle : W ⊓ LinearMap.ker (π i) ≤ W := inf_le_left
      have : FiniteDimensional K ↥(W ⊓ LinearMap.ker (π i)) :=
        Submodule.finiteDimensional_of_le hle
      have hlt : W ⊓ LinearMap.ker (π i) < W := by
        refine lt_of_le_of_ne hle fun h => hi ?_
        have : w₀ ∈ W ⊓ LinearMap.ker (π i) := by rw [h]; exact hw₀
        exact (Submodule.mem_inf.1 this).2
      obtain ⟨w, hw, hw0, hinv⟩ := ih _
        (by rw [← hd]; exact Submodule.finrank_lt_finrank_of_lt hlt) _
        (fun g m hm => Submodule.mem_inf.2 ⟨hW g m (Submodule.mem_inf.1 hm).1, by
          rw [LinearMap.mem_ker, hπ, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hm).2, map_zero]⟩)
        hW' rfl
      exact ⟨w, (Submodule.mem_inf.1 hw).1, hw0, hinv⟩

variable {C : Type*} [Ring C] [Bialgebra K C]

/-- A bialgebra homomorphism from a unipotent coordinate bialgebra to a bialgebra with a basis of
grouplike elements is trivial: it factors through the counit. -/
theorem bialgHom_eq_algebraMap_counit (hB : OneMemStable K B) (φ : B →ₐc[K] C)
    {ι : Type*} (g : Basis ι K C) (hg : ∀ i, comul (R := K) (g i) = g i ⊗ₜ[K] g i) (f : B) :
    φ f = algebraMap K C (counit (R := K) f) := by
  classical
  let φc : B →ₗc[K] C := φ
  let φl : B →ₗ[K] C := φ
  have hφl : ∀ b, φl b = φ b := fun _ => rfl
  -- The `g i`-weight space of the left action of `C`-functionals.
  let W (i : ι) : Submodule K B :=
    ⨅ χ : Module.Dual K C, LinearMap.ker (leftAct (χ ∘ₗ φl) - χ (g i) • LinearMap.id)
  have mem_W : ∀ i x, x ∈ W i ↔ ∀ χ : Module.Dual K C, leftAct (χ ∘ₗ φl) x = χ (g i) • x := by
    intro i x
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  -- The `i`-th weight component of `f`.
  let x (i : ι) : B := leftAct (g.coord i ∘ₗ φl) f
  have hx : ∀ i, x i ∈ W i := by
    intro i
    rw [mem_W]
    intro χ
    rw [leftAct_leftAct]
    have hfun : (χ ∘ₗ φl) ∘ₗ leftAct (g.coord i ∘ₗ φl) = χ (g i) • (g.coord i ∘ₗ φl) := by
      apply LinearMap.ext
      intro b
      have h1 := map_leftAct φc (g.coord i) b
      change χ (φl (leftAct (g.coord i ∘ₗ φl) b)) = χ (g i) * g.coord i (φl b)
      rw [show φl (leftAct (g.coord i ∘ₗ φl) b) = leftAct (g.coord i) (φl b) from h1,
        leftAct_coord_of_grouplike g hg, map_smul, smul_eq_mul, mul_comm]
    rw [hfun, leftAct_smul]
  have hstable : ∀ i (r : Module.Dual K B) (v : B), v ∈ W i → rightAct r v ∈ W i := by
    intro i r v hv
    rw [mem_W] at hv ⊢
    intro χ
    rw [← rightAct_leftAct, hv χ, map_smul]
  have hzero : ∀ i, g i ≠ 1 → x i = 0 := by
    intro i hgi
    by_contra hxi
    have hle : regularSpan (K := K) ({x i} : Finset B) ≤ W i := by
      rw [regularSpan, Submodule.span_le]
      rintro _ ⟨⟨a, r⟩, rfl⟩
      have ha : (a : B) = x i := Finset.mem_singleton.1 a.2
      simp only
      rw [ha]
      exact hstable i r _ (hx i)
    have h1 : (1 : B) ∈ regularSpan (K := K) ({x i} : Finset B) := by
      refine hB _ inferInstance (fun r v hv => rightAct_mem_regularSpan _ r hv) ?_
      intro h
      apply hxi
      have : x i ∈ regularSpan (K := K) ({x i} : Finset B) :=
        subset_regularSpan _ (Finset.mem_coe.2 (Finset.mem_singleton_self _))
      rw [h] at this
      exact (Submodule.mem_bot K).1 this
    have h1W := (mem_W i 1).1 (hle h1)
    apply hgi
    apply eq_of_forall_dual K
    intro χ
    have h2 := h1W χ
    rw [leftAct_one, LinearMap.comp_apply, hφl, map_one] at h2
    exact (smul_left_injective K (one_ne_zero' K B) h2).symm
  have hcoord : ∀ i, g.repr (φ f) i ≠ 0 → g i = 1 := by
    intro i hi
    by_contra hgi
    apply hi
    have h := counit_leftAct (K := K) (g.coord i ∘ₗ φl) f
    rw [show leftAct (g.coord i ∘ₗ φl) f = x i from rfl, hzero i hgi, map_zero] at h
    rw [← Basis.coord_apply]
    exact h.symm
  have hconst : ∃ c : K, φ f = c • (1 : C) := by
    refine ⟨(g.repr (φ f)).sum fun _ c => c, ?_⟩
    conv_lhs => rw [← g.linearCombination_repr (φ f)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord i (Finsupp.mem_support_iff.1 hi)]
  obtain ⟨c, hc⟩ := hconst
  have hcounit : counit (R := K) f = c := by
    rw [← CoalgHomClass.counit_comp_apply φ f, hc, map_smul, Bialgebra.counit_one, smul_eq_mul,
      mul_one]
  rw [hc, hcounit, Algebra.algebraMap_eq_smul_one]

end Bialgebra

section Transfer

variable {K : Type*} [Field K] {B C : Type*} [Ring B] [Bialgebra K B] [Ring C] [Bialgebra K C]

/-- Right translation commutes with a linear map compatible with the comultiplications. -/
theorem map_rightAct (φ : B →ₗ[K] C)
    (hφ : ∀ x, comul (R := K) (φ x) = TensorProduct.map φ φ (comul (R := K) x))
    (f : Module.Dual K C) (b : B) :
    φ (rightAct (f ∘ₗ φ) b) = rightAct f (φ b) := by
  rw [rightAct_apply, rightAct_apply, hφ]
  generalize comul (R := K) b = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The property that every nonzero finite-dimensional right-translation stable subspace contains
`1` transfers along a linear equivalence preserving the unit and the comultiplication. -/
theorem OneMemStable.of_linearEquiv (φ : B ≃ₗ[K] C) (h1 : φ 1 = 1)
    (hφ : ∀ x, comul (R := K) (φ x) = TensorProduct.map (φ : B →ₗ[K] C) φ (comul (R := K) x))
    (hB : OneMemStable K B) : OneMemStable K C := by
  intro V hfin hV hV0
  have hfin' : FiniteDimensional K (V.comap (φ : B →ₗ[K] C)) := by
    rw [Submodule.comap_equiv_eq_map_symm]
    infer_instance
  have hmem := hB (V.comap (φ : B →ₗ[K] C)) hfin' ?_ ?_
  · rw [Submodule.mem_comap, LinearEquiv.coe_coe, h1] at hmem
    exact hmem
  · intro f v hv
    rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    have h := map_rightAct (φ : B →ₗ[K] C) hφ (f ∘ₗ (φ.symm : C →ₗ[K] B)) v
    have hf : (f ∘ₗ (φ.symm : C →ₗ[K] B)) ∘ₗ (φ : B →ₗ[K] C) = f := by
      ext x
      simp
    rw [hf] at h
    simp only [LinearEquiv.coe_coe] at h
    rw [h]
    exact hV _ _ hv
  · intro h
    apply hV0
    rw [eq_bot_iff]
    intro c hc
    have hc' : φ.symm c ∈ V.comap (φ : B →ₗ[K] C) := by
      rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hc
    rw [h, Submodule.mem_bot] at hc'
    rw [Submodule.mem_bot, ← φ.apply_symm_apply c, hc', map_zero]

end Transfer

end Langlands.GroupScheme.Unipotent
