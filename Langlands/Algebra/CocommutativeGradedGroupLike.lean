import Langlands.Algebra.GroupAlgebraCoaction
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-! # Group-like elements of graded cocommutative bialgebras over algebraically closed fields

A bialgebra map `π : A → K[N]` grades `A` by `N` (`GroupAlgebraCoaction`). If `A` is
cocommutative and `K` is algebraically closed, every nonzero homogeneous component contains a
group-like element. With a Hopf algebra structure, group-like elements in every degree and a
degree-zero part spanned by group-like elements make `A` spanned by group-like elements. -/

noncomputable section

universe u v w

open TensorProduct Coalgebra

namespace Langlands

namespace CommonEigenvector

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- Over an algebraically closed field, a pairwise commuting family `S` of endomorphisms that
preserves a nonzero finite-dimensional subspace `W` has a common eigenvector in `W`. -/
theorem exists_mem_forall_eq_smul [IsAlgClosed K] (S : Set (Module.End K V))
    (hS : ∀ f ∈ S, ∀ g ∈ S, f ∘ₗ g = g ∘ₗ f) (W : Submodule K V) [FiniteDimensional K W]
    (hW : W ≠ ⊥) (hinv : ∀ f ∈ S, ∀ w ∈ W, f w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ f ∈ S, ∃ c : K, f w = c • w := by
  suffices H : ∀ d : ℕ, ∀ W : Submodule K V, Module.finrank K W = d → FiniteDimensional K W →
      W ≠ ⊥ → (∀ f ∈ S, ∀ w ∈ W, f w ∈ W) → ∃ w ∈ W, w ≠ 0 ∧ ∀ f ∈ S, ∃ c : K, f w = c • w from
    H _ W rfl inferInstance hW hinv
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hfin hW hinv
  by_cases hscal : ∀ f ∈ S, ∃ c : K, ∀ w ∈ W, f w = c • w
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨w, hw, hw0, fun f hf => let ⟨c, hc⟩ := hscal f hf; ⟨c, hc w hw⟩⟩
  push Not at hscal
  obtain ⟨f, hf, hfns⟩ := hscal
  have hmaps : Set.MapsTo f W W := fun w hw => hinv f hf w hw
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hmaps)
  obtain ⟨⟨w₀, hw₀W⟩, hw₀⟩ := hμ.exists_hasEigenvector
  have hfw₀ : f w₀ = μ • w₀ := by
    have := Module.End.mem_eigenspace_iff.mp hw₀.1
    exact congrArg Subtype.val this
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀.2 (Subtype.ext h)
  let W' : Submodule K V := W ⊓ (f.eigenspace μ)
  have hmem' : ∀ w, w ∈ W' ↔ w ∈ W ∧ f w = μ • w := fun w => by
    simp [W']
  have hW'le : W' ≤ W := inf_le_left
  have hW'ne : W' ≠ ⊥ := by
    intro h
    have : w₀ ∈ W' := (hmem' w₀).mpr ⟨hw₀W, hfw₀⟩
    rw [h, Submodule.mem_bot] at this
    exact hw₀0 this
  have hW'lt : W' < W := by
    refine lt_of_le_of_ne hW'le fun h => ?_
    obtain ⟨w, hw, hne⟩ := hfns μ
    exact hne ((hmem' w).mp (h ▸ hw)).2
  have : FiniteDimensional K W' := Submodule.finiteDimensional_of_le hW'le
  have hrank : Module.finrank K W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hW'lt
  have hinv' : ∀ g ∈ S, ∀ w ∈ W', g w ∈ W' := by
    intro g hg w hw
    rw [hmem'] at hw ⊢
    refine ⟨hinv g hg w hw.1, ?_⟩
    have hcomm := LinearMap.congr_fun (hS f hf g hg) w
    simp only [LinearMap.coe_comp, Function.comp_apply] at hcomm
    rw [hcomm, hw.2, map_smul]
  obtain ⟨w, hw, hw0, hc⟩ := ih _ hrank W' rfl inferInstance hW'ne hinv'
  exact ⟨w, hW'le hw, hw0, hc⟩

end CommonEigenvector

namespace GroupAlgebraCoaction

section TensorSeparation

variable {K : Type u} [Field K] {X : Type v} [AddCommGroup X] [Module K X]
  {A : Type w} [AddCommGroup A] [Module K A]

/-- Over a field, an element of `X ⊗ A` that is killed by `id ⊗ f` for every linear form `f` on
`A` is zero. -/
theorem eq_zero_of_forall_rid_lTensor (t : X ⊗[K] A)
    (h : ∀ f : A →ₗ[K] K, TensorProduct.rid K X (f.lTensor X t) = 0) : t = 0 := by
  let b := Module.Free.chooseBasis K A
  have key : ∀ (s : X ⊗[K] A) i, TensorProduct.equivFinsuppOfBasisRight b s i =
      TensorProduct.rid K X ((b.coord i).lTensor X s) := by
    intro s i
    induction s using TensorProduct.inductionOn with
    | tmul x a => simp
    | add s s' hs hs' => simp only [map_add, Finsupp.add_apply, hs, hs']
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, h, map_zero, Finsupp.zero_apply]

end TensorSeparation

section Coalgebra

variable {K : Type u} [Field K] {A : Type v} [AddCommGroup A] [Module K A] [Coalgebra K A]

theorem apply_ract (φ f : A →ₗ[K] K) (a : A) : φ (ract f a) = f (lact φ a) := by
  let 𝓡 := Repr.arbitrary K a
  rw [ract_apply 𝓡, lact_apply 𝓡, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul, smul_eq_mul, mul_comm]

/-- A nonzero element `v` of a coalgebra over a field that is an eigenvector of every right
translation `ract f` has a scalar multiple that is group-like. -/
theorem exists_isGroupLikeElem_smul_of_forall_ract {v : A} (hv : v ≠ 0)
    (h : ∀ f : A →ₗ[K] K, ∃ c : K, ract f v = c • v) :
    ∃ c : K, IsGroupLikeElem K (c • v) := by
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : A →ₗ[K] K, φ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv ((Module.forall_dual_apply_eq_zero_iff K v).mp hcon)
  let φ : A →ₗ[K] K := (φ₀ v)⁻¹ • φ₀
  have hφ : φ v = 1 := by
    simp [φ, inv_mul_cancel₀ hφ₀]
  set a := lact φ v with ha_def
  have hcomul : comul (R := K) v = v ⊗ₜ[K] a := by
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_rid_lTensor
    intro f
    obtain ⟨c, hc⟩ := h f
    have hfa : f a = c := by
      rw [ha_def, ← apply_ract, hc, map_smul, hφ, smul_eq_mul, mul_one]
    have hract : TensorProduct.rid K A (f.lTensor A (comul v)) = ract f v := rfl
    rw [map_sub, map_sub, hract, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hfa, hc,
      sub_self]
  have h1 : counit (R := K) v • a = v := by
    have := Coalgebra.rTensor_counit_comul (R := K) v
    rw [hcomul, LinearMap.rTensor_tmul] at this
    have := congrArg (TensorProduct.lid K A) this
    simpa using this
  have hε : counit (R := K) v ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h1
    exact hv h1.symm
  have hav : (counit (R := K) v)⁻¹ • v = a :=
    calc (counit (R := K) v)⁻¹ • v = (counit (R := K) v)⁻¹ • (counit (R := K) v • a) := by
          rw [h1]
      _ = a := by rw [smul_smul, inv_mul_cancel₀ hε, one_smul]
  refine ⟨(counit (R := K) v)⁻¹, ?_⟩
  rw [hav]
  constructor
  · rw [← hav, map_smul, smul_eq_mul, inv_mul_cancel₀ hε]
  · conv_lhs => rw [← hav]
    rw [map_smul, hcomul, TensorProduct.smul_tmul', hav]

end Coalgebra

section Cocommutative

variable {K : Type u} [Field K] {A : Type v} [AddCommGroup A] [Module K A] [Coalgebra K A]
  [Coalgebra.IsCocomm K A]

/-- In a cocommutative coalgebra, the convolution of linear forms is commutative. -/
theorem conv_comm (f g : A →ₗ[K] K) : conv f g = conv g f := by
  have key : ∀ t : A ⊗[K] A, TensorProduct.lid K K (TensorProduct.map f g
      (TensorProduct.comm K A A t)) = TensorProduct.lid K K (TensorProduct.map g f t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [mul_comm]
    | add s t hs ht => simp only [map_add, hs, ht]
  ext a
  change TensorProduct.lid K K (TensorProduct.map f g (comul a)) =
    TensorProduct.lid K K (TensorProduct.map g f (comul a))
  rw [← key, Coalgebra.comm_comul]

/-- In a cocommutative coalgebra, right translations commute. -/
theorem ract_comp_ract_comm (f g : A →ₗ[K] K) : ract f ∘ₗ ract g = ract g ∘ₗ ract f := by
  ext a
  simp only [LinearMap.coe_comp, Function.comp_apply, ract_ract, conv_comm f g]

end Cocommutative

section Graded

variable {K : Type u} [Field K] {N : Type w} [AddCommGroup N]
variable {A : Type v} [CommRing A] [Bialgebra K A] (π : A →ₐc[K] AddMonoidAlgebra K N)

/-- If `π` is surjective, every homogeneous component is nonzero. -/
theorem grade_ne_bot_of_surjective (hπ : Function.Surjective π) (n : N) : grade π n ≠ ⊥ := by
  obtain ⟨a, ha⟩ := hπ (AddMonoidAlgebra.single n 1)
  intro h
  have hmem := proj_mem π n a
  rw [h, Submodule.mem_bot] at hmem
  have := counit_proj π n a
  rw [hmem, map_zero, ha] at this
  simp at this

variable [Coalgebra.IsCocomm K A]

/-- In a cocommutative bialgebra, right translations preserve the homogeneous components. -/
theorem ract_mem_grade (f : A →ₗ[K] K) {n : N} {a : A} (ha : a ∈ grade π n) :
    ract f a ∈ grade π n := by
  have : proj π n (ract f a) = ract f a := by
    rw [proj, ract_ract, conv_comm, ← ract_ract, ← proj, proj_self_of_mem π ha]
  rw [← this]
  exact proj_mem π n _

/-- **Group-like elements in each degree.** Let `A` be a cocommutative bialgebra over an
algebraically closed field, graded by a bialgebra map `π : A → K[N]`. Every nonzero homogeneous
component of `A` contains a group-like element. -/
theorem exists_isGroupLikeElem_mem_grade [IsAlgClosed K] {n : N} (hn : grade π n ≠ ⊥) :
    ∃ g : A, IsGroupLikeElem K g ∧ g ∈ grade π n := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let W : Submodule K A := Submodule.span K (Set.range fun f : A →ₗ[K] K => ract f x)
  have hWle : W ≤ grade π n :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun f => ract_mem_grade π f hx)
  have hxW : x ∈ W := by
    have : ract (counit : A →ₗ[K] K) x ∈ W := Submodule.subset_span ⟨_, rfl⟩
    rwa [ract_counit] at this
  have hWne : W ≠ ⊥ := fun h => hx0 (by rw [h, Submodule.mem_bot] at hxW; exact hxW)
  have : FiniteDimensional K W := by
    let 𝓡 := Repr.arbitrary K x
    have hle : W ≤ Submodule.span K (𝓡.left '' (𝓡.index : Set _)) := by
      refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun f => ?_)
      rw [SetLike.mem_coe, ract_apply 𝓡]
      exact Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    have : FiniteDimensional K (Submodule.span K (𝓡.left '' (𝓡.index : Set _))) :=
      FiniteDimensional.span_of_finite K ((𝓡.index.finite_toSet).image _)
    exact Submodule.finiteDimensional_of_le hle
  let S : Set (Module.End K A) := Set.range fun f : A →ₗ[K] K => ract f
  have hS : ∀ f ∈ S, ∀ g ∈ S, f ∘ₗ g = g ∘ₗ f := by
    rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
    exact ract_comp_ract_comm f g
  have hinv : ∀ f ∈ S, ∀ w ∈ W, f w ∈ W := by
    rintro _ ⟨g, rfl⟩ w hw
    have hle : W ≤ W.comap (ract g) := by
      refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun f => ?_)
      change ract g (ract f x) ∈ W
      rw [ract_ract]
      exact Submodule.subset_span ⟨_, rfl⟩
    exact hle hw
  obtain ⟨w, hw, hw0, hc⟩ := CommonEigenvector.exists_mem_forall_eq_smul S hS W hWne hinv
  obtain ⟨c, hg⟩ := exists_isGroupLikeElem_smul_of_forall_ract hw0 fun f => hc _ ⟨f, rfl⟩
  exact ⟨c • w, hg, Submodule.smul_mem _ _ (hWle hw)⟩

end Graded

section Hopf

variable {K : Type u} [Field K] {N : Type w} [AddCommGroup N]
variable {A : Type v} [CommRing A] [HopfAlgebra K A] (π : A →ₐc[K] AddMonoidAlgebra K N)

/-- If a homogeneous component contains a group-like element `g` and the degree-zero component
lies in the span of the group-like elements, so does the whole component: `a = (a g⁻¹) g`. -/
theorem mem_span_isGroupLikeElem_of_mem_grade {n : N} {g : A} (hg : IsGroupLikeElem K g)
    (hgn : g ∈ grade π n) (h0 : grade π 0 ≤ Submodule.span K {x : A | IsGroupLikeElem K x})
    {a : A} (ha : a ∈ grade π n) : a ∈ Submodule.span K {x : A | IsGroupLikeElem K x} := by
  let u : Aˣ := hg.isUnit.unit
  have hu : (u : A) = g := rfl
  have hinv : ((u⁻¹ : Aˣ) : A) ∈ grade π (-n) := inv_mem_grade π u (hu ▸ hgn)
  have h0mem : a * ((u⁻¹ : Aˣ) : A) ∈ Submodule.span K {x : A | IsGroupLikeElem K x} := by
    apply h0
    have := mul_mem_grade π ha hinv
    rwa [add_neg_cancel] at this
  have hmap : (Submodule.span K {x : A | IsGroupLikeElem K x}).map (LinearMap.mulRight K g) ≤
      Submodule.span K {x : A | IsGroupLikeElem K x} := by
    rw [Submodule.map_span_le]
    intro x hx
    exact Submodule.subset_span (IsGroupLikeElem.mul hx hg)
  have heq : a = LinearMap.mulRight K g (a * ((u⁻¹ : Aˣ) : A)) := by
    rw [LinearMap.mulRight_apply, mul_assoc, ← hu, Units.inv_mul, mul_one]
  rw [heq]
  exact hmap (Submodule.mem_map_of_mem h0mem)

/-- A Hopf algebra graded by `π`, with a group-like element in every degree and degree-zero part
spanned by group-like elements, is spanned by its group-like elements. -/
theorem span_isGroupLikeElem_eq_top_of_forall_grade
    (hg : ∀ n, ∃ g : A, IsGroupLikeElem K g ∧ g ∈ grade π n)
    (h0 : grade π 0 ≤ Submodule.span K {x : A | IsGroupLikeElem K x}) :
    Submodule.span K {x : A | IsGroupLikeElem K x} = ⊤ := by
  rw [eq_top_iff]
  intro a _
  rw [← sum_proj π a]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨g, hg, hgn⟩ := hg n
  exact mem_span_isGroupLikeElem_of_mem_grade π hg hgn h0 (proj_mem π n a)

/-- **Cocommutative graded Hopf algebras are spanned by group-like elements.** Let `A` be a
cocommutative Hopf algebra over an algebraically closed field, and `π : A → K[N]` a surjective
bialgebra map. If the degree-zero component of the grading defined by `π` is spanned by
group-like elements, then `A` is spanned by group-like elements. -/
theorem span_isGroupLikeElem_eq_top [IsAlgClosed K] [Coalgebra.IsCocomm K A]
    (hπ : Function.Surjective π)
    (h0 : grade π 0 ≤ Submodule.span K {x : A | IsGroupLikeElem K x}) :
    Submodule.span K {x : A | IsGroupLikeElem K x} = ⊤ :=
  span_isGroupLikeElem_eq_top_of_forall_grade π
    (fun n => exists_isGroupLikeElem_mem_grade π (grade_ne_bot_of_surjective π hπ n)) h0

end Hopf

end GroupAlgebraCoaction

end Langlands
