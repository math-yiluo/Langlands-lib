import Langlands.GroupScheme.Unipotent.HopfFixed
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-! # Unipotent coordinate bialgebras under extension of scalars -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding Chevalley

/-- Tensors are separated by contracting the first factor with functionals. -/
theorem tensor_ext_left {k : Type*} [Field k] {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {t : M ⊗[k] N}
    (h : ∀ g : Module.Dual k M, TensorProduct.lid k N (g.rTensor N t) = 0) : t = 0 := by
  classical
  let b := Basis.ofVectorSpace k M
  have key : ∀ (u : M ⊗[k] N) (i : Basis.ofVectorSpaceIndex k M),
      TensorProduct.equivFinsuppOfBasisLeft b u i =
        TensorProduct.lid k N ((b.coord i).rTensor N u) := by
    intro u i
    induction u using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [key, h, map_zero, Finsupp.zero_apply]

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] {B : Type*} [Ring B]
  [Bialgebra k B]

/-- Right translation by the scalar extension of a functional is the scalar extension of the
right translation. -/
theorem rightAct_baseChange (g : Module.Dual k B) (x : K ⊗[k] B) :
    rightAct (g.baseChange K) x = (rightAct g).lTensor K x := by
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    rw [rightAct_apply, LinearMap.lTensor_tmul, rightAct_apply, TensorProduct.comul_tmul,
      CommSemiring.comul_apply]
    generalize comul (R := k) b = t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, LinearMap.lTensor_tmul,
        Module.Dual.baseChange_apply_tmul, TensorProduct.rid_tmul]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The property that every nonzero finite-dimensional right-translation stable subspace contains
`1` is preserved by extension of scalars of the coordinate bialgebra. -/
theorem OneMemStable.baseChange (hB : OneMemStable k B) : OneMemStable K (K ⊗[k] B) := by
  classical
  intro V hfin hV hV0
  -- The `k`-linear translation operators and the coordinate projections.
  let T : Module.Dual k B → (K ⊗[k] B) →ₗ[k] (K ⊗[k] B) := fun g => (rightAct g).lTensor K
  let π : Module.Dual k K → (K ⊗[k] B) →ₗ[k] B := fun l => TensorProduct.lid k B ∘ₗ l.rTensor B
  have hπ : ∀ l g m, π l (T g m) = rightAct g (π l m) := by
    intro l g m
    induction m using TensorProduct.inductionOn with
    | tmul c b => simp [π, T]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsep : ∀ m, (∀ l, π l m = 0) → m = 0 := fun m hm => tensor_ext_left hm
  have hTV : ∀ g m, m ∈ V → T g m ∈ V := by
    intro g m hm
    change (rightAct g).lTensor K m ∈ V
    rw [← rightAct_baseChange]
    exact hV _ _ hm
  -- A nonzero vector of `V` and a finite-dimensional stable `k`-subspace containing it.
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset v₀
  let L : Submodule k K := Submodule.span k (S.image Prod.fst : Set K)
  let U : Submodule k B := regularSpan (K := k) (S.image Prod.snd)
  let ι : L ⊗[k] U →ₗ[k] K ⊗[k] B := TensorProduct.map L.subtype U.subtype
  have hι : ∀ g, T g ∘ₗ ι =
      ι ∘ₗ ((rightAct g).restrict fun _ hb => rightAct_mem_regularSpan _ g hb).lTensor L := by
    intro g
    apply TensorProduct.ext'
    intro c b
    rfl
  let W : Submodule k (K ⊗[k] B) := LinearMap.range ι ⊓ V.restrictScalars k
  have hW : ∀ g m, m ∈ W → T g m ∈ W := by
    rintro g m ⟨⟨y, rfl⟩, hm⟩
    exact ⟨⟨_, (LinearMap.congr_fun (hι g) y).symm⟩, hTV g _ hm⟩
  have hv₀W : v₀ ∈ W := by
    refine ⟨?_, hv₀⟩
    rw [hS]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hc : p.1 ∈ L := Submodule.subset_span (Finset.mem_image_of_mem _ hp)
    have hb : p.2 ∈ U := subset_regularSpan _ (Finset.mem_image_of_mem _ hp)
    exact ⟨⟨p.1, hc⟩ ⊗ₜ ⟨p.2, hb⟩, rfl⟩
  have hW0 : W ≠ ⊥ := fun h => hv₀0 ((Submodule.mem_bot k).1 (h ▸ hv₀W))
  obtain ⟨w, hwW, hw0, hw⟩ := exists_invariant hB T π hπ hsep W hW hW0
  -- The invariant vector is a constant tensor `c ⊗ 1`.
  have hcounit : ∀ (l : Module.Dual k K) (x : K ⊗[k] B), counit (R := k) (π l x) =
      l (TensorProduct.rid k K ((counit (R := k) (A := B)).lTensor K x)) := by
    intro l x
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [π, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  let c : K := TensorProduct.rid k K ((counit (R := k) (A := B)).lTensor K w)
  have hπw : ∀ l, π l w = l c • (1 : B) := by
    intro l
    have hinv : ∀ g : Module.Dual k B, rightAct g (π l w) = g 1 • π l w := by
      intro g
      rw [← hπ, hw, map_smul]
    rw [eq_counit_smul_one_of_invariant hinv, hcounit]
  have hwc : w = c ⊗ₜ[k] (1 : B) := by
    rw [← sub_eq_zero]
    apply hsep
    intro l
    rw [map_sub, hπw]
    simp [π]
  have hc0 : c ≠ 0 := by
    intro h
    apply hw0
    rw [hwc, h, TensorProduct.zero_tmul]
  have h1 : (1 : K ⊗[k] B) = c⁻¹ • w := by
    rw [hwc, TensorProduct.smul_tmul', smul_eq_mul, inv_mul_cancel₀ hc0,
      Algebra.TensorProduct.one_def]
  rw [h1]
  exact V.smul_mem _ ((Submodule.restrictScalars_mem k V w).1 hwW.2)

end Langlands.GroupScheme.Unipotent
