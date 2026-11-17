import Langlands.Algebra.GroupAlgebraCoaction
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Langlands.Algebra.HopfPointConnected
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # Extensions with connected quotient in Hopf-algebra terms

Let `A` be a commutative Hopf algebra over a field `K`, with bialgebra maps `π : A → K[N]` (a
closed diagonalizable subgroup) and `φ : K[M] → A` (the quotient map onto a diagonalizable group),
such that the degree-zero part of the grading defined by `π` is the image of `φ`. If `K[M]` has no
nontrivial idempotents (the quotient is connected), then `π` is central and `A` is cocommutative.
The proofs use the convolution groups of points `A →ₐ[K] B` and a rigidity statement for
group-like elements over a connected coefficient ring. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

open TensorProduct Coalgebra WithConv Algebra.TensorProduct

namespace Langlands.ConnectedExtensionHopf

section Points

variable {K : Type u} [Field K]

theorem comp_productMap {C D B B' : Type*} [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    [CommSemiring B] [Algebra K B] [CommSemiring B'] [Algebra K B'] (f : B →ₐ[K] B') (ξ : C →ₐ[K] B)
    (η : D →ₐ[K] B) : f.comp (productMap ξ η) = productMap (f.comp ξ) (f.comp η) := by
  apply Algebra.TensorProduct.ext'
  intro c d
  simp

theorem productMap_map {C D C' D' B : Type*} [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    [CommRing C'] [Algebra K C'] [CommRing D'] [Algebra K D'] [CommSemiring B] [Algebra K B]
    (ξ : C →ₐ[K] B) (η : D →ₐ[K] B) (f : C' →ₐ[K] C) (g : D' →ₐ[K] D) (t : C' ⊗[K] D') :
    productMap ξ η (Algebra.TensorProduct.map f g t) = productMap (ξ.comp f) (η.comp g) t := by
  rw [← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro c d
  simp

/-- Convolution of two points of a bialgebra `C` with values in a commutative algebra `B`:
`(ξ ⋆ ξ') c = ∑ ξ(c₁) ξ'(c₂)`. -/
def conv {C B : Type*} [CommRing C] [Bialgebra K C] [CommSemiring B] [Algebra K B]
    (ξ ξ' : C →ₐ[K] B) : C →ₐ[K] B :=
  (productMap ξ ξ').comp (Bialgebra.comulAlgHom K C)

theorem conv_apply {C B : Type*} [CommRing C] [Bialgebra K C] [CommSemiring B] [Algebra K B]
    (ξ ξ' : C →ₐ[K] B) (c : C) : conv ξ ξ' c = productMap ξ ξ' (comul c) := rfl

theorem comp_conv {C B B' : Type*} [CommRing C] [Bialgebra K C] [CommSemiring B] [Algebra K B]
    [CommSemiring B'] [Algebra K B'] (f : B →ₐ[K] B') (ξ ξ' : C →ₐ[K] B) :
    f.comp (conv ξ ξ') = conv (f.comp ξ) (f.comp ξ') := by
  rw [conv, conv, ← AlgHom.comp_assoc, comp_productMap]

theorem conv_eq_ofConv {C B : Type*} [CommRing C] [Bialgebra K C] [CommSemiring B] [Algebra K B]
    (ξ ξ' : C →ₐ[K] B) : conv ξ ξ' = ofConv (toConv ξ * toConv ξ') := by
  ext c
  rw [conv_apply, AlgHom.convMul_apply]
  rfl

theorem conv_comp_bialgHom {C C' B : Type*} [CommRing C] [Bialgebra K C] [CommRing C']
    [Bialgebra K C'] [CommSemiring B] [Algebra K B] (ξ ξ' : C →ₐ[K] B) (h : C' →ₐc[K] C) :
    (conv ξ ξ').comp (h : C' →ₐ[K] C) = conv (ξ.comp h) (ξ'.comp h) := by
  rw [conv_eq_ofConv, conv_eq_ofConv, ← AlgHom.convMul_comp_bialgHom_distrib]

end Points

section Core

variable {K : Type u} [Field K] {N : Type w} [AddCommGroup N] {D : Type v} [CommRing D]
  [Algebra K D]

variable (K N D) in
/-- The triple tensor product `K[N] ⊗ (K[N] ⊗ D)`, as a type with its own ring structure. -/
def T₃ : Type _ := AddMonoidAlgebra K N ⊗[K] (AddMonoidAlgebra K N ⊗[K] D)

instance : CommRing (T₃ K N D) :=
  inferInstanceAs (CommRing (AddMonoidAlgebra K N ⊗[K] (AddMonoidAlgebra K N ⊗[K] D)))

instance : Algebra K (T₃ K N D) :=
  inferInstanceAs (Algebra K (AddMonoidAlgebra K N ⊗[K] (AddMonoidAlgebra K N ⊗[K] D)))

variable (K N D) in
/-- The first universal point on `T₃`. -/
def u₁ : AddMonoidAlgebra K N →ₐ[K] T₃ K N D := includeLeft

variable (K N D) in
/-- The second universal point on `T₃`. -/
def u₂ : AddMonoidAlgebra K N →ₐ[K] T₃ K N D :=
  (includeRight : AddMonoidAlgebra K N ⊗[K] D →ₐ[K] _).comp includeLeft

variable (K N D) in
/-- The third universal point on `T₃`. -/
def u₃ : D →ₐ[K] T₃ K N D :=
  (includeRight : AddMonoidAlgebra K N ⊗[K] D →ₐ[K] _).comp includeRight

/-- The algebra map out of `T₃` determined by three points. -/
def T₃.lift {B : Type*} [CommRing B] [Algebra K B] (ξ ξ' : AddMonoidAlgebra K N →ₐ[K] B)
    (η : D →ₐ[K] B) : T₃ K N D →ₐ[K] B :=
  productMap ξ (productMap ξ' η)

theorem T₃.lift_comp_u₁ {B : Type*} [CommRing B] [Algebra K B]
    (ξ ξ' : AddMonoidAlgebra K N →ₐ[K] B) (η : D →ₐ[K] B) :
    (T₃.lift ξ ξ' η).comp (u₁ K N D) = ξ := by
  refine AlgHom.ext fun x => ?_
  change productMap ξ (productMap ξ' η) (x ⊗ₜ[K] (1 : AddMonoidAlgebra K N ⊗[K] D)) = ξ x
  simp

theorem T₃.lift_comp_u₂ {B : Type*} [CommRing B] [Algebra K B]
    (ξ ξ' : AddMonoidAlgebra K N →ₐ[K] B) (η : D →ₐ[K] B) :
    (T₃.lift ξ ξ' η).comp (u₂ K N D) = ξ' := by
  refine AlgHom.ext fun x => ?_
  change productMap ξ (productMap ξ' η) ((1 : AddMonoidAlgebra K N) ⊗ₜ[K] (x ⊗ₜ[K] (1 : D))) =
    ξ' x
  simp

theorem T₃.lift_comp_u₃ {B : Type*} [CommRing B] [Algebra K B]
    (ξ ξ' : AddMonoidAlgebra K N →ₐ[K] B) (η : D →ₐ[K] B) :
    (T₃.lift ξ ξ' η).comp (u₃ K N D) = η := by
  refine AlgHom.ext fun x => ?_
  change productMap ξ (productMap ξ' η)
    ((1 : AddMonoidAlgebra K N) ⊗ₜ[K] ((1 : AddMonoidAlgebra K N) ⊗ₜ[K] x)) = η x
  simp

/-- The point `K[N] → D[N]`, `Xⁿ ↦ Xⁿ`. -/
abbrev ξ₀ : AddMonoidAlgebra K N →ₐ[K] AddMonoidAlgebra D N :=
  AddMonoidAlgebra.lift K (AddMonoidAlgebra D N) N (AddMonoidAlgebra.of D N)

/-- The point `D → D[N]`, `d ↦ d X⁰`. -/
abbrev η₀ : D →ₐ[K] AddMonoidAlgebra D N := IsScalarTower.toAlgHom K D (AddMonoidAlgebra D N)

theorem ξ₀_single (n : N) (c : K) :
    (ξ₀ : AddMonoidAlgebra K N →ₐ[K] AddMonoidAlgebra D N) (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single n (algebraMap K D c) := by
  simp [ξ₀, AddMonoidAlgebra.lift_single, Algebra.smul_def]

theorem productMap_ξ₀_η₀ (t : AddMonoidAlgebra K N ⊗[K] D) :
    productMap ξ₀ η₀ t = AddMonoidAlgebra.scalarTensorEquiv K D (Algebra.TensorProduct.comm K _ D t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x d =>
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | single n c =>
      simp [AddMonoidAlgebra.single_mul_single, Algebra.smul_def, mul_comm]
  | add s t hs ht => simp only [map_add, hs, ht]

open Langlands.Algebra.HopfPointExtension in
/-- **Rigidity over a connected coefficient ring.** Let `D` be a nonzero `K`-algebra whose only
idempotents are `0` and `1`, and `W ∈ K[N] ⊗ D`. Suppose `W` is group-like in the first variable:
evaluated at the universal points of `K[N] ⊗ (K[N] ⊗ D)`, `W(ξ₁ ξ₂, η) = W(ξ₁, η) W(ξ₂, η)`, and
`W(1, η) = 1`. Then `W = Xᵘ ⊗ 1` for some `μ`. -/
theorem exists_eq_single_tmul_one [Nontrivial D]
    (hD : ∀ e : D, IsIdempotentElem e → e = 0 ∨ e = 1) (W : AddMonoidAlgebra K N ⊗[K] D)
    (hmul : productMap (conv (u₁ K N D) (u₂ K N D)) (u₃ K N D) W =
      productMap (u₁ K N D) (u₃ K N D) W * productMap (u₂ K N D) (u₃ K N D) W)
    (hone : productMap (1 : WithConv (AddMonoidAlgebra K N →ₐ[K] D)).ofConv (AlgHom.id K D) W =
      1) :
    ∃ μ : N, W = AddMonoidAlgebra.single μ 1 ⊗ₜ 1 := by
  classical
  set y : AddMonoidAlgebra D N :=
    AddMonoidAlgebra.scalarTensorEquiv K D (Algebra.TensorProduct.comm K _ D W) with hy
  have hyW : y = productMap ξ₀ η₀ W := (productMap_ξ₀_η₀ W).symm
  let ι₁ : AddMonoidAlgebra K N →ₐ[K] AddMonoidAlgebra D (N × N) := (inlMap K D N).comp ξ₀
  let ι₂ : AddMonoidAlgebra K N →ₐ[K] AddMonoidAlgebra D (N × N) := (inrMap K D N).comp ξ₀
  let η' : D →ₐ[K] AddMonoidAlgebra D (N × N) := IsScalarTower.toAlgHom K D _
  have hη_diag : (diagMap K D N).comp η₀ = η' := by
    ext d
    simp [η', diagMap, η₀, AddMonoidAlgebra.mapDomain_single]
    rfl
  have hη_inl : (inlMap K D N).comp η₀ = η' := by
    ext d
    simp [η', inlMap, η₀, AddMonoidAlgebra.mapDomain_single]
    rfl
  have hη_inr : (inrMap K D N).comp η₀ = η' := by
    ext d
    simp [η', inrMap, η₀, AddMonoidAlgebra.mapDomain_single]
    rfl
  have hξ_diag : (diagMap K D N).comp ξ₀ = conv ι₁ ι₂ := by
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      rw [AlgHom.comp_apply, conv_apply,
        (AddMonoidAlgebra.isGroupLikeElem_single_one m).comul_eq_tmul_self]
      simp [ι₁, ι₂, diagMap, inlMap, inrMap, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single]
    · exact Subsingleton.elim _ _
  let F : T₃ K N D →ₐ[K] AddMonoidAlgebra D (N × N) := T₃.lift ι₁ ι₂ η'
  have hF₁ : F.comp (u₁ K N D) = ι₁ := T₃.lift_comp_u₁ _ _ _
  have hF₂ : F.comp (u₂ K N D) = ι₂ := T₃.lift_comp_u₂ _ _ _
  have hF₃ : F.comp (u₃ K N D) = η' := T₃.lift_comp_u₃ _ _ _
  have hdiag : diagMap K D N y = inlMap K D N y * inrMap K D N y := by
    have h := congrArg F hmul
    rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, comp_productMap,
      comp_productMap, comp_productMap, comp_conv, hF₁, hF₂, hF₃] at h
    rw [hyW, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, comp_productMap,
      comp_productMap, comp_productMap, hη_diag, hη_inl, hη_inr, hξ_diag]
    exact h
  have hcounit : groupCounit K D N y = 1 := by
    have h1 : (groupCounit K D N).comp ξ₀ = (1 : WithConv (AddMonoidAlgebra K N →ₐ[K] D)).ofConv := by
      apply AddMonoidAlgebra.algHom_ext
      · intro m
        simp [groupCounit, AddMonoidAlgebra.lift_single]
      · exact Subsingleton.elim _ _
    have h2 : (groupCounit K D N).comp η₀ = AlgHom.id K D := by
      ext d; simp [groupCounit, η₀, AddMonoidAlgebra.lift_single]
    rw [hyW, ← AlgHom.comp_apply, comp_productMap, h1, h2, hone]
  obtain ⟨μ, hμ⟩ := Langlands.Algebra.HopfPointConnected.exists_eq_single_of_grouplike
    (R := K) hD hdiag hcounit
  refine ⟨μ, ?_⟩
  have := congrArg (fun z => (Algebra.TensorProduct.comm K (AddMonoidAlgebra K N) D).symm
    ((AddMonoidAlgebra.scalarTensorEquiv K D (M := N)).symm z)) hy
  simp only [AlgEquiv.symm_apply_apply] at this
  rw [← this, hμ, AddMonoidAlgebra.scalarTensorEquiv_symm_single]
  rfl

end Core

section Conv

variable {K : Type u} [Field K]

theorem conv_assoc {C B : Type*} [CommRing C] [HopfAlgebra K C] [CommRing B] [Algebra K B]
    (ξ ξ' ξ'' : C →ₐ[K] B) : conv (conv ξ ξ') ξ'' = conv ξ (conv ξ' ξ'') := by
  simp only [conv_eq_ofConv, WithConv.toConv_ofConv, mul_assoc]

theorem one_conv {C B : Type*} [CommRing C] [HopfAlgebra K C] [CommRing B] [Algebra K B]
    (ξ : C →ₐ[K] B) : conv ((Algebra.ofId K B).comp (Bialgebra.counitAlgHom K C)) ξ = ξ := by
  rw [conv_eq_ofConv, ← AlgHom.convOne_def, one_mul]

theorem conv_one {C B : Type*} [CommRing C] [HopfAlgebra K C] [CommRing B] [Algebra K B]
    (ξ : C →ₐ[K] B) : conv ξ ((Algebra.ofId K B).comp (Bialgebra.counitAlgHom K C)) = ξ := by
  rw [conv_eq_ofConv, ← AlgHom.convOne_def, mul_one]

end Conv

section Extension

open GroupAlgebraCoaction

variable {K : Type u} [Field K] {N M : Type w} [AddCommGroup N] [AddCommGroup M]
  {A : Type v} [CommRing A] [HopfAlgebra K A]

/-- The Hopf-algebra data of an extension `1 → D(N) → G → D(M) → 1` with `G = Spec A`: `φ` is
injective (the quotient map is faithfully flat), `π` is surjective (the subgroup is closed),
`π ∘ φ` is trivial, and the invariants of the coaction of `K[N]` through `π` are the image of `φ`.
-/
structure IsExtension (φ : AddMonoidAlgebra K M →ₐc[K] A) (π : A →ₐc[K] AddMonoidAlgebra K N) :
    Prop where
  injective : Function.Injective φ
  surjective : Function.Surjective π
  comp_eq : ∀ b, π (φ b) = algebraMap K _ (counit (R := K) b)
  invariants : ∀ a ∈ grade π 0, ∃ b, φ b = a

variable {φ : AddMonoidAlgebra K M →ₐc[K] A} {π : A →ₐc[K] AddMonoidAlgebra K N}

theorem exists_mem_grade_counit_eq_one' (hπ : Function.Surjective π) (n : N) :
    ∃ a ∈ grade π n, counit (R := K) a = 1 := by
  obtain ⟨a, ha⟩ := hπ (AddMonoidAlgebra.single n 1)
  refine ⟨proj π n a, proj_mem π n a, ?_⟩
  rw [counit_proj, ha]
  simp [AddMonoidAlgebra.coeff_single]

/-- A family `(aᵢ, bᵢ)` with `aᵢ` of degree `n`, `bᵢ` of degree `-n` and `∑ aᵢ bᵢ = 1`. -/
theorem exists_unitFamily (hπ : Function.Surjective π) (n : N) :
    ∃ s : Multiset (A × A), (∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n)) ∧
      (s.map fun p => p.1 * p.2).sum = 1 := by
  obtain ⟨a, ha, h1⟩ := exists_mem_grade_counit_eq_one' hπ (-n)
  have h := one_mem_grade_neg_mul_grade π ha h1
  rw [neg_neg] at h
  refine Submodule.mul_induction_on h (C := fun x => ∃ s : Multiset (A × A),
    (∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n)) ∧ (s.map fun p => p.1 * p.2).sum = x)
    (fun x hx y hy => ⟨{(x, y)}, by simpa using ⟨hx, hy⟩, by simp⟩) ?_
  rintro x y ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  refine ⟨s + t, fun p hp => ?_, by simp⟩
  rcases Multiset.mem_add.mp hp with hp | hp
  · exact hs p hp
  · exact ht p hp

/-- The image of `φ` has degree `0`. (The proof is that of
`CentralTorusExtensionHopf.map_mem_grade_zero`, for an arbitrary `M`.) -/
theorem map_mem_grade_zero' (h : IsExtension φ π) (b : AddMonoidAlgebra K M) :
    φ b ∈ grade π 0 := by
  have key : (π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A ∘ₗ
      TensorProduct.map (φ : AddMonoidAlgebra K M →ₗ[K] A) φ =
        TensorProduct.map (φ : AddMonoidAlgebra K M →ₗ[K] A)
          (Algebra.linearMap K (AddMonoidAlgebra K N)) ∘ₗ
          (counit : AddMonoidAlgebra K M →ₗ[K] K).lTensor _ := by
    apply TensorProduct.ext'
    intro x y
    simp [h.comp_eq]
  rw [mem_grade_iff, coaction_apply, ← CoalgHomClass.map_comp_comul_apply φ b,
    ← LinearMap.comp_apply, key, LinearMap.comp_apply, lTensor_counit_comul]
  simp [AddMonoidAlgebra.smul_single]

/-- The composite `π ∘ φ`, as algebra maps, is the trivial point. -/
theorem comp_eq_one (h : IsExtension φ π) :
    (π : A →ₐ[K] AddMonoidAlgebra K N).comp (φ : AddMonoidAlgebra K M →ₐ[K] A) =
      (Algebra.ofId K _).comp (Bialgebra.counitAlgHom K _) := by
  ext m
  simp [h.comp_eq]

/-- A point of `G` translated on the left by a point of the subgroup agrees with the original
point on the degree-zero part `φ(K[M])`. -/
theorem conv_apply_of_mem_grade_zero (h : IsExtension φ π) {B : Type*} [CommRing B]
    [Algebra K B] (ψ : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) {e : A}
    (he : e ∈ grade π 0) : conv (ψ.comp π) x e = x e := by
  obtain ⟨c, rfl⟩ := h.invariants e he
  have key : (conv (ψ.comp π) x).comp (φ : AddMonoidAlgebra K M →ₐ[K] A) =
      x.comp (φ : AddMonoidAlgebra K M →ₐ[K] A) := by
    rw [conv_comp_bialgHom, AlgHom.comp_assoc, comp_eq_one h, ← AlgHom.comp_assoc,
      show ψ.comp (Algebra.ofId K _) = Algebra.ofId K B from Subsingleton.elim _ _, one_conv]
  exact congrArg (fun f => f c) key

theorem conv_comp_φ (h : IsExtension φ π) {B : Type*} [CommRing B] [Algebra K B]
    (ψ : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) :
    (conv (ψ.comp π) x).comp (φ : AddMonoidAlgebra K M →ₐ[K] A) =
      x.comp (φ : AddMonoidAlgebra K M →ₐ[K] A) := by
  exact AlgHom.ext fun c => conv_apply_of_mem_grade_zero h ψ x (map_mem_grade_zero' h c)

/-- Cancellation of a common factor `x a` over all `a` of degree `n`, using a unit family. -/
theorem eq_of_forall_mul {B : Type*} [CommRing B] [Algebra K B] (x : A →ₐ[K] B) {n : N}
    {s : Multiset (A × A)} (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) {c d : B}
    (hcd : ∀ a ∈ grade π n, c * x a = d * x a) : c = d := by
  have h1 : x (s.map fun p => p.1 * p.2).sum = 1 := by rw [hsum, map_one]
  rw [map_multiset_sum, Multiset.map_map] at h1
  calc c = c * (s.map (x ∘ fun p => p.1 * p.2)).sum := by rw [h1, mul_one]
    _ = d * (s.map (x ∘ fun p => p.1 * p.2)).sum := by
      rw [← Multiset.sum_map_mul_left, ← Multiset.sum_map_mul_left]
      congr 1
      refine Multiset.map_congr rfl fun p hp => ?_
      simp only [Function.comp_apply, map_mul, ← mul_assoc, hcd p.1 (hs p hp).1]
    _ = d := by rw [h1, mul_one]

section Character

variable (π) in
/-- The conjugation character `E(ψ, x) = ∑ (ψπ ⋆ x)(aᵢ) x(bᵢ)` attached to a unit family. -/
def charE (s : Multiset (A × A)) {B : Type*} [CommRing B] [Algebra K B]
    (ψ : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) : B :=
  (s.map fun p => conv (ψ.comp π) x p.1 * x p.2).sum

variable {n : N} {s : Multiset (A × A)}

theorem conv_eq_charE_mul (h : IsExtension φ π)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B] [Algebra K B]
    (ψ : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) {a : A} (ha : a ∈ grade π n) :
    conv (ψ.comp π) x a = charE π s ψ x * x a := by
  have key : ∀ p ∈ s, conv (ψ.comp π) x (p.1 * p.2 * a) = conv (ψ.comp π) x p.1 * x p.2 * x a := by
    intro p hp
    have h0 : p.2 * a ∈ grade π 0 := by
      have := mul_mem_grade π (hs p hp).2 ha
      rwa [neg_add_cancel] at this
    rw [mul_assoc, map_mul, conv_apply_of_mem_grade_zero h ψ x h0, map_mul, mul_assoc]
  calc conv (ψ.comp π) x a = conv (ψ.comp π) x ((s.map fun p => p.1 * p.2).sum * a) := by
        rw [hsum, one_mul]
    _ = (s.map fun p => conv (ψ.comp π) x (p.1 * p.2 * a)).sum := by
        rw [← Multiset.sum_map_mul_right, map_multiset_sum, Multiset.map_map]
        rfl
    _ = (s.map fun p => conv (ψ.comp π) x p.1 * x p.2 * x a).sum :=
        congrArg Multiset.sum (Multiset.map_congr rfl key)
    _ = charE π s ψ x * x a := by rw [charE, Multiset.sum_map_mul_right]

theorem sum_map_mul_eq_one (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B]
    [Algebra K B] (x : A →ₐ[K] B) : (s.map fun p => x p.1 * x p.2).sum = 1 := by
  calc (s.map fun p => x p.1 * x p.2).sum = (s.map (x ∘ fun p => p.1 * p.2)).sum := by
        congr 1
        exact Multiset.map_congr rfl fun p _ => by simp
    _ = x (s.map fun p => p.1 * p.2).sum := by rw [map_multiset_sum, Multiset.map_map]
    _ = 1 := by rw [hsum, map_one]

theorem charE_one (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B]
    [Algebra K B] (x : A →ₐ[K] B) :
    charE π s ((Algebra.ofId K B).comp (Bialgebra.counitAlgHom K _)) x = 1 := by
  have h1 : ((Algebra.ofId K B).comp (Bialgebra.counitAlgHom K (AddMonoidAlgebra K N))).comp
      (π : A →ₐ[K] AddMonoidAlgebra K N) = (Algebra.ofId K B).comp (Bialgebra.counitAlgHom K A) := by
    ext a
    simp
  rw [charE, h1, one_conv]
  exact sum_map_mul_eq_one hsum x

/-- The universal point of `D(N)` on `K[N] ⊗ A`. -/
abbrev ιN : AddMonoidAlgebra K N →ₐ[K] AddMonoidAlgebra K N ⊗[K] A := includeLeft

/-- The universal point of `G` on `K[N] ⊗ A`. -/
abbrev ιA : A →ₐ[K] AddMonoidAlgebra K N ⊗[K] A := includeRight

theorem charE_eq_productMap {B : Type*} [CommRing B] [Algebra K B]
    (ψ : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) :
    charE π s ψ x = productMap ψ x (charE π s (ιN (K := K) (N := N) (A := A)) ιA) := by
  have h1 : (productMap ψ x).comp (ιN (K := K) (N := N) (A := A)) = ψ := by ext; simp
  have h2 : (productMap ψ x).comp (ιA (K := K) (N := N) (A := A)) = x := by ext; simp
  rw [charE, charE, map_multiset_sum, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp_apply, map_mul]
  rw [← AlgHom.comp_apply (productMap ψ x) (conv _ _), comp_conv, ← AlgHom.comp_assoc, h1, h2,
    ← AlgHom.comp_apply (productMap ψ x) ιA, h2]

theorem charE_univ_mem (h : IsExtension φ π) (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n)) :
    charE π s (ιN (K := K) (N := N) (A := A)) ιA ∈
      (Algebra.TensorProduct.map (AlgHom.id K (AddMonoidAlgebra K N))
        (φ : AddMonoidAlgebra K M →ₐ[K] A)).range := by
  refine Subalgebra.multiset_sum_mem _ fun z hz => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
  have hb := (hs p hp).2
  rw [conv_apply, comul_of_mem π (hs p hp).1]
  generalize comul (R := K) p.1 = t
  induction t using TensorProduct.inductionOn with
  | tmul c d =>
    have h0 : proj π n d * p.2 ∈ grade π 0 := by
      have := mul_mem_grade π (proj_mem π n d) hb
      rwa [add_neg_cancel] at this
    obtain ⟨e, he⟩ := h.invariants _ h0
    refine ⟨(π c) ⊗ₜ e, ?_⟩
    simp [he, Algebra.TensorProduct.tmul_mul_tmul]
  | add t t' ht ht' =>
    rw [map_add, map_add, add_mul]
    exact add_mem ht ht'

theorem charE_eq_W {W : AddMonoidAlgebra K N ⊗[K] AddMonoidAlgebra K M}
    (hW : Algebra.TensorProduct.map (AlgHom.id K (AddMonoidAlgebra K N))
        (φ : AddMonoidAlgebra K M →ₐ[K] A) W = charE π s (ιN (K := K) (N := N) (A := A)) ιA)
    {B : Type*} [CommRing B] [Algebra K B] (ψ : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) :
    charE π s ψ x = productMap ψ (x.comp (φ : AddMonoidAlgebra K M →ₐ[K] A)) W := by
  rw [charE_eq_productMap, ← hW, productMap_map, AlgHom.comp_id]

theorem charE_conv_right (h : IsExtension φ π)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n)) {B : Type*} [CommRing B] [Algebra K B]
    (ψ ψ' : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) :
    charE π s ψ (conv (ψ'.comp π) x) = charE π s ψ x := by
  obtain ⟨W, hW⟩ := charE_univ_mem h hs
  rw [charE_eq_W hW, charE_eq_W hW, conv_comp_φ h]

theorem charE_conv (h : IsExtension φ π)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B] [Algebra K B]
    (ψ ψ' : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) :
    charE π s (conv ψ ψ') x = charE π s ψ x * charE π s ψ' x := by
  refine eq_of_forall_mul x hs hsum fun a ha => ?_
  rw [← conv_eq_charE_mul h hs hsum _ x ha, conv_comp_bialgHom, conv_assoc,
    conv_eq_charE_mul h hs hsum ψ _ ha, charE_conv_right h hs, conv_eq_charE_mul h hs hsum ψ' x ha,
    mul_assoc]

/-- **Rigidity of the conjugation character.** If `K[M]` has no nontrivial idempotents, the
universal conjugation character of a unit family of degree `n` is a monomial `Xᵘ ⊗ 1`. -/
theorem exists_charE_univ_eq (h : IsExtension φ π)
    (hD : ∀ e : AddMonoidAlgebra K M, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) :
    ∃ μ : N, charE π s (ιN (K := K) (N := N) (A := A)) ιA =
      AddMonoidAlgebra.single μ 1 ⊗ₜ[K] (1 : A) := by
  obtain ⟨W, hW⟩ := charE_univ_mem h hs
  let Φ : T₃ K N (AddMonoidAlgebra K M) →ₐ[K] T₃ K N A :=
    T₃.lift (u₁ K N A) (u₂ K N A) ((u₃ K N A).comp (φ : AddMonoidAlgebra K M →ₐ[K] A))
  have hΦ : ∀ t : AddMonoidAlgebra K N ⊗[K] (AddMonoidAlgebra K N ⊗[K] AddMonoidAlgebra K M),
      Φ t = LinearMap.lTensor (AddMonoidAlgebra K N) (LinearMap.lTensor (AddMonoidAlgebra K N)
        (φ : AddMonoidAlgebra K M →ₗ[K] A)) t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a t' =>
      induction t' using TensorProduct.inductionOn with
      | tmul b c =>
        change productMap (u₁ K N A) (productMap (u₂ K N A) ((u₃ K N A).comp _)) (a ⊗ₜ (b ⊗ₜ c)) = _
        simp only [u₁, u₂, u₃, productMap_apply_tmul, AlgHom.comp_apply]
        change (a ⊗ₜ[K] (1 : AddMonoidAlgebra K N ⊗[K] A)) *
          (((1 : AddMonoidAlgebra K N) ⊗ₜ[K] (b ⊗ₜ[K] (1 : A))) *
            ((1 : AddMonoidAlgebra K N) ⊗ₜ[K] ((1 : AddMonoidAlgebra K N) ⊗ₜ[K] φ c))) =
          a ⊗ₜ[K] (b ⊗ₜ[K] φ c)
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add t₁ t₂ h₁ h₂ =>
        rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂]
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  have hΦinj : Function.Injective Φ := by
    intro t t' htt'
    rw [hΦ, hΦ] at htt'
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (Module.Flat.lTensor_preserves_injective_linearMap _ h.injective) htt'
  have hmul : productMap (conv (u₁ K N (AddMonoidAlgebra K M)) (u₂ K N (AddMonoidAlgebra K M)))
      (u₃ K N (AddMonoidAlgebra K M)) W =
      productMap (u₁ K N (AddMonoidAlgebra K M)) (u₃ K N (AddMonoidAlgebra K M)) W *
        productMap (u₂ K N (AddMonoidAlgebra K M)) (u₃ K N (AddMonoidAlgebra K M)) W := by
    apply hΦinj
    rw [map_mul, ← AlgHom.comp_apply Φ, ← AlgHom.comp_apply Φ, ← AlgHom.comp_apply Φ,
      comp_productMap, comp_productMap, comp_productMap, comp_conv, T₃.lift_comp_u₁,
      T₃.lift_comp_u₂, T₃.lift_comp_u₃, ← charE_eq_W hW, ← charE_eq_W hW, ← charE_eq_W hW,
      charE_conv h hs hsum]
  have hone : productMap (1 : WithConv (AddMonoidAlgebra K N →ₐ[K] AddMonoidAlgebra K M)).ofConv
      (AlgHom.id K _) W = 1 := by
    apply h.injective
    rw [map_one, AlgHom.convOne_def, WithConv.ofConv_toConv]
    change ((φ : AddMonoidAlgebra K M →ₐ[K] A).comp (productMap _ _)) W = 1
    rw [comp_productMap, ← AlgHom.comp_assoc,
      show (φ : AddMonoidAlgebra K M →ₐ[K] A).comp (Algebra.ofId K _) = Algebra.ofId K A from
        Subsingleton.elim _ _, AlgHom.comp_id,
      show (φ : AddMonoidAlgebra K M →ₐ[K] A) = (AlgHom.id K A).comp φ from rfl,
      ← charE_eq_W hW, charE_one hsum]
  obtain ⟨μ, hμ⟩ := exists_eq_single_tmul_one hD W hmul hone
  refine ⟨μ, ?_⟩
  rw [← hW, hμ]
  simp

theorem charE_eq_of_univ {μ : N}
    (hμ : charE π s (ιN (K := K) (N := N) (A := A)) ιA = AddMonoidAlgebra.single μ 1 ⊗ₜ[K] (1 : A))
    {B : Type*} [CommRing B] [Algebra K B] (ψ : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) :
    charE π s ψ x = ψ (AddMonoidAlgebra.single μ 1) := by
  rw [charE_eq_productMap, hμ]
  simp

end Character

theorem map_eq_single_of_mem_grade {a : A} {n : N} (ha : a ∈ grade π n) :
    π a = AddMonoidAlgebra.single n (counit (R := K) a) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  ext m
  rw [← counit_proj, proj_of_mem π ha, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hm : m = n
  · subst hm; simp
  · simp [hm, Ne.symm hm]

theorem conv_right_of_mem_grade {B : Type*} [CommRing B] [Algebra K B]
    (ψ : AddMonoidAlgebra K N →ₐ[K] B) (x : A →ₐ[K] B) {a : A} {n : N} (ha : a ∈ grade π n) :
    conv x (ψ.comp π) a = x a * ψ (AddMonoidAlgebra.single n 1) := by
  rw [conv_apply]
  have h1 : ∀ t : A ⊗[K] A, productMap x (ψ.comp π) t =
      productMap x ψ ((π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c d => simp
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']
  have h2 : (π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A (comul a) =
      a ⊗ₜ[K] AddMonoidAlgebra.single n 1 := by
    have := (mem_grade_iff π).mp ha
    rw [coaction_apply] at this
    rw [← (AddMonoidAlgebra.scalarTensorEquiv K A).symm_apply_apply
      ((π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A (comul a)), this,
      AddMonoidAlgebra.scalarTensorEquiv_symm_single]
  rw [h1, h2]
  simp

/-- **Centrality.** In an extension whose quotient `Spec K[M]` is connected (`K[M]` has no
nontrivial idempotents), the subgroup `Spec K[N]` is central. -/
theorem isCentral (h : IsExtension φ π)
    (hD : ∀ e : AddMonoidAlgebra K M, IsIdempotentElem e → e = 0 ∨ e = 1) : IsCentral π := by
  have key : ∀ n, ∀ a ∈ grade π n,
      conv ((ιN (K := K) (N := N) (A := A)).comp π) ιA a =
        conv ιA ((ιN (K := K) (N := N) (A := A)).comp π) a := by
    intro n a ha
    obtain ⟨s, hs, hsum⟩ := exists_unitFamily h.surjective n
    obtain ⟨μ, hμ⟩ := exists_charE_univ_eq h hD hs hsum
    have hμn : μ = n := by
      obtain ⟨a₀, ha₀, h1⟩ := exists_mem_grade_counit_eq_one' h.surjective n
      have e := conv_eq_charE_mul h hs hsum (AlgHom.id K (AddMonoidAlgebra K N))
        ((Algebra.ofId K _).comp (Bialgebra.counitAlgHom K A)) ha₀
      rw [AlgHom.id_comp, conv_one, charE_eq_of_univ hμ] at e
      simp only [AlgHom.id_apply, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, h1,
        map_one, mul_one] at e
      have e' : π a₀ = AddMonoidAlgebra.single μ 1 := e
      rw [map_eq_single_of_mem_grade ha₀, h1] at e'
      exact ((AddMonoidAlgebra.single_left_inj one_ne_zero).mp e').symm
    rw [conv_eq_charE_mul h hs hsum _ _ ha, charE_eq_of_univ hμ, hμn,
      conv_right_of_mem_grade _ _ ha, mul_comm]
  intro a
  have hL : (π : A →ₗ[K] AddMonoidAlgebra K N).rTensor A (comul a) =
      conv ((ιN (K := K) (N := N) (A := A)).comp π) ιA a := by
    rw [conv_apply]
    induction comul (R := K) a using TensorProduct.inductionOn with
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  have hR : TensorProduct.comm K A _ ((π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A (comul a)) =
      conv ιA ((ιN (K := K) (N := N) (A := A)).comp π) a := by
    rw [conv_apply]
    induction comul (R := K) a using TensorProduct.inductionOn with
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']
  rw [hL, hR, ← sum_proj π a, map_sum, map_sum]
  exact Finset.sum_congr rfl fun n _ => key n _ (proj_mem π n a)

/-! ### Commutativity -/

theorem conv_comm_groupAlgebra {B : Type*} [CommRing B] [Algebra K B]
    (ξ ξ' : AddMonoidAlgebra K M →ₐ[K] B) : conv ξ ξ' = conv ξ' ξ := by
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    rw [conv_apply, conv_apply, (AddMonoidAlgebra.isGroupLikeElem_single_one m).comul_eq_tmul_self]
    simp [mul_comm]
  · exact Subsingleton.elim _ _

/-- Points of `G` commute on the degree-zero part `φ(K[M])`: the quotient is commutative. -/
theorem conv_comm_of_mem_grade_zero (h : IsExtension φ π) {B : Type*} [CommRing B] [Algebra K B]
    (g k : A →ₐ[K] B) {e : A} (he : e ∈ grade π 0) : conv g k e = conv k g e := by
  obtain ⟨c, rfl⟩ := h.invariants e he
  have key : (conv g k).comp (φ : AddMonoidAlgebra K M →ₐ[K] A) =
      (conv k g).comp (φ : AddMonoidAlgebra K M →ₐ[K] A) := by
    rw [conv_comp_bialgHom, conv_comp_bialgHom, conv_comm_groupAlgebra]
  exact congrArg (fun f => f c) key

section Commutator

/-- The commutator pairing `U(g, k) = ∑ (g ⋆ k)(aᵢ) (k ⋆ g)(bᵢ)` attached to a unit family. -/
def commU (s : Multiset (A × A)) {B : Type*} [CommRing B] [Algebra K B] (g k : A →ₐ[K] B) : B :=
  (s.map fun p => conv g k p.1 * conv k g p.2).sum

variable {n : N} {s : Multiset (A × A)}

theorem conv_eq_commU_mul (h : IsExtension φ π)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B] [Algebra K B]
    (g k : A →ₐ[K] B) {a : A} (ha : a ∈ grade π n) :
    conv g k a = commU s g k * conv k g a := by
  have key : ∀ p ∈ s, conv g k (p.1 * p.2 * a) = conv g k p.1 * conv k g p.2 * conv k g a := by
    intro p hp
    have h0 : p.2 * a ∈ grade π 0 := by
      have := mul_mem_grade π (hs p hp).2 ha
      rwa [neg_add_cancel] at this
    rw [mul_assoc, map_mul, conv_comm_of_mem_grade_zero h g k h0, map_mul, mul_assoc]
  calc conv g k a = conv g k ((s.map fun p => p.1 * p.2).sum * a) := by rw [hsum, one_mul]
    _ = (s.map fun p => conv g k (p.1 * p.2 * a)).sum := by
        rw [← Multiset.sum_map_mul_right, map_multiset_sum, Multiset.map_map]
        rfl
    _ = (s.map fun p => conv g k p.1 * conv k g p.2 * conv k g a).sum :=
        congrArg Multiset.sum (Multiset.map_congr rfl key)
    _ = commU s g k * conv k g a := by rw [commU, Multiset.sum_map_mul_right]

theorem conv_left_eq_commU_mul (h : IsExtension φ π)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B] [Algebra K B]
    (z g k : A →ₐ[K] B) {a : A} (ha : a ∈ grade π n) :
    conv z (conv g k) a = commU s g k * conv z (conv k g) a := by
  rw [conv_apply, conv_apply, comul_of_mem π ha]
  induction comul (R := K) a using TensorProduct.inductionOn with
  | tmul c d =>
    simp only [LinearMap.lTensor_tmul, productMap_apply_tmul]
    rw [conv_eq_commU_mul h hs hsum g k (proj_mem π n d)]
    ring
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', mul_add]

theorem conv_right_eq_commU_mul (h : IsExtension φ π) (hc : IsCentral π)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B] [Algebra K B]
    (g k w : A →ₐ[K] B) {a : A} (ha : a ∈ grade π n) :
    conv (conv g k) w a = commU s g k * conv (conv k g) w a := by
  have hΔ : comul (R := K) a = (proj π n).rTensor A (comul a) := by
    rw [hc.rTensor_proj_comul, proj_self_of_mem π ha]
  rw [conv_apply, conv_apply, hΔ]
  induction comul (R := K) a using TensorProduct.inductionOn with
  | tmul c d =>
    simp only [LinearMap.rTensor_tmul, productMap_apply_tmul]
    rw [conv_eq_commU_mul h hs hsum g k (proj_mem π n c)]
    ring
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', mul_add]

theorem commU_conv (h : IsExtension φ π) (hc : IsCentral π)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B] [Algebra K B]
    (x x' y : A →ₐ[K] B) :
    commU s (conv x x') y = commU s x y * commU s x' y := by
  refine eq_of_forall_mul (conv (conv y x) x') hs hsum fun a ha => ?_
  have e1 := conv_eq_commU_mul h hs hsum (conv x x') y ha
  have e2 := conv_left_eq_commU_mul h hs hsum x x' y ha
  have e3 := conv_right_eq_commU_mul h hc hs hsum x y x' ha
  calc commU s (conv x x') y * conv (conv y x) x' a = conv (conv x x') y a := by
        rw [e1, conv_assoc]
    _ = conv x (conv x' y) a := by rw [conv_assoc]
    _ = commU s x' y * conv x (conv y x') a := e2
    _ = commU s x' y * (commU s x y * conv (conv y x) x' a) := by rw [← conv_assoc x y x', e3]
    _ = commU s x y * commU s x' y * conv (conv y x) x' a := by ring

theorem commU_one (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B]
    [Algebra K B] (g : A →ₐ[K] B) :
    commU s g ((Algebra.ofId K B).comp (Bialgebra.counitAlgHom K A)) = 1 := by
  rw [commU, conv_one, one_conv]
  exact sum_map_mul_eq_one hsum g

theorem one_commU (hsum : (s.map fun p => p.1 * p.2).sum = 1) {B : Type*} [CommRing B]
    [Algebra K B] (g : A →ₐ[K] B) :
    commU s ((Algebra.ofId K B).comp (Bialgebra.counitAlgHom K A)) g = 1 := by
  rw [commU, conv_one, one_conv]
  exact sum_map_mul_eq_one hsum g

/-- The universal pair of points of `G` on `A ⊗ A`. -/
abbrev κ₁ : A →ₐ[K] A ⊗[K] A := includeLeft

/-- The second universal point of `G` on `A ⊗ A`. -/
abbrev κ₂ : A →ₐ[K] A ⊗[K] A := includeRight

theorem commU_eq_productMap {B : Type*} [CommRing B] [Algebra K B] (g k : A →ₐ[K] B) :
    commU s g k = productMap g k (commU s (κ₁ (K := K) (A := A)) κ₂) := by
  have h1 : (productMap g k).comp (κ₁ (K := K) (A := A)) = g := by ext; simp
  have h2 : (productMap g k).comp (κ₂ (K := K) (A := A)) = k := by ext; simp
  rw [commU, commU, map_multiset_sum, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp_apply, map_mul]
  rw [← AlgHom.comp_apply (productMap g k) (conv κ₁ κ₂), comp_conv, h1, h2,
    ← AlgHom.comp_apply (productMap g k) (conv κ₂ κ₁), comp_conv, h1, h2]

theorem commU_univ_mem (h : IsExtension φ π) (hc : IsCentral π)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n)) :
    commU s (κ₁ (K := K) (A := A)) κ₂ ∈
      (Algebra.TensorProduct.map (φ : AddMonoidAlgebra K M →ₐ[K] A)
        (φ : AddMonoidAlgebra K M →ₐ[K] A)).range := by
  refine Subalgebra.multiset_sum_mem _ fun z hz => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
  have h0 : ∀ {c d : A}, c ∈ grade π n → d ∈ grade π (-n) → ∃ e, φ e = c * d := by
    intro c d hc' hd'
    have := mul_mem_grade π hc' hd'
    rw [add_neg_cancel] at this
    exact h.invariants _ this
  rw [conv_apply, conv_apply, hc.comul_of_mem (hs p hp).1, hc.comul_of_mem (hs p hp).2]
  induction comul (R := K) p.1 using TensorProduct.inductionOn with
  | tmul c d =>
    induction comul (R := K) p.2 using TensorProduct.inductionOn with
    | tmul c' d' =>
      obtain ⟨e₁, he₁⟩ := h0 (proj_mem π n c) (proj_mem π (-n) d')
      obtain ⟨e₂, he₂⟩ := h0 (proj_mem π n d) (proj_mem π (-n) c')
      refine ⟨e₁ ⊗ₜ e₂, ?_⟩
      simp [he₁, he₂, Algebra.TensorProduct.tmul_mul_tmul]
    | add t t' ht ht' => rw [map_add, map_add, mul_add]; exact add_mem ht ht'
  | add t t' ht ht' => rw [map_add, map_add, add_mul]; exact add_mem ht ht'

theorem commU_eq_V {V : AddMonoidAlgebra K M ⊗[K] AddMonoidAlgebra K M}
    (hV : Algebra.TensorProduct.map (φ : AddMonoidAlgebra K M →ₐ[K] A)
        (φ : AddMonoidAlgebra K M →ₐ[K] A) V = commU s (κ₁ (K := K) (A := A)) κ₂)
    {B : Type*} [CommRing B] [Algebra K B] (g k : A →ₐ[K] B) :
    commU s g k = productMap (g.comp (φ : AddMonoidAlgebra K M →ₐ[K] A))
      (k.comp (φ : AddMonoidAlgebra K M →ₐ[K] A)) V := by
  rw [commU_eq_productMap, ← hV, productMap_map]

variable (K A) in
/-- The triple tensor product `A ⊗ (A ⊗ A)`, as a type with its own ring structure. -/
def A₃ : Type _ := A ⊗[K] (A ⊗[K] A)

instance : CommRing (A₃ K A) := inferInstanceAs (CommRing (A ⊗[K] (A ⊗[K] A)))

instance : Algebra K (A₃ K A) := inferInstanceAs (Algebra K (A ⊗[K] (A ⊗[K] A)))

variable (K A) in
/-- The first universal point of `G` on `A₃`. -/
def j₁ : A →ₐ[K] A₃ K A := includeLeft

variable (K A) in
/-- The second universal point of `G` on `A₃`. -/
def j₂ : A →ₐ[K] A₃ K A := (includeRight : A ⊗[K] A →ₐ[K] _).comp includeLeft

variable (K A) in
/-- The third universal point of `G` on `A₃`. -/
def j₃ : A →ₐ[K] A₃ K A := (includeRight : A ⊗[K] A →ₐ[K] _).comp includeRight

/-- **Triviality of the commutator pairing.** If `K[M]` has no nontrivial idempotents and `π`
is central, the universal commutator pairing of a unit family is `1`. -/
theorem commU_univ_eq_one (h : IsExtension φ π) (hc : IsCentral π)
    (hD : ∀ e : AddMonoidAlgebra K M, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hs : ∀ p ∈ s, p.1 ∈ grade π n ∧ p.2 ∈ grade π (-n))
    (hsum : (s.map fun p => p.1 * p.2).sum = 1) :
    commU s (κ₁ (K := K) (A := A)) κ₂ = 1 := by
  obtain ⟨V, hV⟩ := commU_univ_mem h hc hs
  let φ' : AddMonoidAlgebra K M →ₐ[K] A := φ
  let Φ : T₃ K M (AddMonoidAlgebra K M) →ₐ[K] A₃ K A :=
    T₃.lift ((j₁ K A).comp φ') ((j₂ K A).comp φ') ((j₃ K A).comp φ')
  have hΦ : ∀ t : AddMonoidAlgebra K M ⊗[K] (AddMonoidAlgebra K M ⊗[K] AddMonoidAlgebra K M),
      Φ t = TensorProduct.map (φ : AddMonoidAlgebra K M →ₗ[K] A)
        (TensorProduct.map (φ : AddMonoidAlgebra K M →ₗ[K] A) (φ : AddMonoidAlgebra K M →ₗ[K] A))
        t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a t' =>
      induction t' using TensorProduct.inductionOn with
      | tmul b c =>
        change productMap ((j₁ K A).comp φ') (productMap ((j₂ K A).comp φ') ((j₃ K A).comp φ'))
          (a ⊗ₜ (b ⊗ₜ c)) = _
        simp only [j₁, j₂, j₃, productMap_apply_tmul, AlgHom.comp_apply]
        change (φ a ⊗ₜ[K] (1 : A ⊗[K] A)) * (((1 : A) ⊗ₜ[K] (φ b ⊗ₜ[K] (1 : A))) *
          ((1 : A) ⊗ₜ[K] ((1 : A) ⊗ₜ[K] φ c))) = φ a ⊗ₜ[K] (φ b ⊗ₜ[K] φ c)
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add t₁ t₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂]
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  have hΦinj : Function.Injective Φ := by
    intro t t' htt'
    rw [hΦ, hΦ] at htt'
    exact TensorProduct.map_injective_of_flat_flat _ _ h.injective
      (TensorProduct.map_injective_of_flat_flat _ _ h.injective h.injective) htt'
  have hmul : productMap (conv (u₁ K M (AddMonoidAlgebra K M)) (u₂ K M (AddMonoidAlgebra K M)))
      (u₃ K M (AddMonoidAlgebra K M)) V =
      productMap (u₁ K M (AddMonoidAlgebra K M)) (u₃ K M (AddMonoidAlgebra K M)) V *
        productMap (u₂ K M (AddMonoidAlgebra K M)) (u₃ K M (AddMonoidAlgebra K M)) V := by
    apply hΦinj
    rw [map_mul, ← AlgHom.comp_apply Φ, ← AlgHom.comp_apply Φ, ← AlgHom.comp_apply Φ,
      comp_productMap, comp_productMap, comp_productMap, comp_conv, T₃.lift_comp_u₁,
      T₃.lift_comp_u₂, T₃.lift_comp_u₃, ← conv_comp_bialgHom, ← commU_eq_V hV,
      ← commU_eq_V hV, ← commU_eq_V hV, commU_conv h hc hs hsum]
  have hcounit : (Bialgebra.counitAlgHom K A).comp φ' =
      Bialgebra.counitAlgHom K (AddMonoidAlgebra K M) := by
    ext m
    simp [φ']
  have hone : productMap (1 : WithConv (AddMonoidAlgebra K M →ₐ[K] AddMonoidAlgebra K M)).ofConv
      (AlgHom.id K _) V = 1 := by
    apply h.injective
    rw [map_one, AlgHom.convOne_def, WithConv.ofConv_toConv]
    change (φ'.comp (productMap _ _)) V = 1
    rw [comp_productMap, ← AlgHom.comp_assoc,
      show φ'.comp (Algebra.ofId K _) = Algebra.ofId K A from Subsingleton.elim _ _,
      AlgHom.comp_id, ← hcounit, ← AlgHom.comp_assoc]
    have e := commU_eq_V hV ((Algebra.ofId K A).comp (Bialgebra.counitAlgHom K A)) (AlgHom.id K A)
    rw [one_commU hsum, AlgHom.id_comp] at e
    exact e.symm
  obtain ⟨χ, hχ⟩ := exists_eq_single_tmul_one hD V hmul hone
  have hχ0 : φ (AddMonoidAlgebra.single χ 1) = 1 := by
    have e := commU_one hsum (AlgHom.id K A)
    rw [commU_eq_V hV, hχ] at e
    simpa using e
  have hχ1 : AddMonoidAlgebra.single χ (1 : K) = 1 := h.injective (by rw [hχ0, map_one])
  rw [← hV, hχ, hχ1, Algebra.TensorProduct.one_def.symm, map_one]

/-- **Commutativity.** In an extension with connected quotient (`K[M]` has no nontrivial
idempotents), the Hopf algebra `A` is cocommutative: the group `Spec A` is commutative. -/
theorem comm_comul (h : IsExtension φ π)
    (hD : ∀ e : AddMonoidAlgebra K M, IsIdempotentElem e → e = 0 ∨ e = 1) (a : A) :
    TensorProduct.comm K A A (comul a) = comul a := by
  have hc := isCentral h hD
  have key : ∀ n, ∀ a ∈ grade π n, conv (κ₁ (K := K) (A := A)) κ₂ a = conv κ₂ κ₁ a := by
    intro n a ha
    obtain ⟨s, hs, hsum⟩ := exists_unitFamily h.surjective n
    rw [conv_eq_commU_mul h hs hsum _ _ ha, commU_univ_eq_one h hc hD hs hsum, one_mul]
  have hL : comul (R := K) a = conv (κ₁ (K := K) (A := A)) κ₂ a := by
    rw [conv_apply]
    induction comul (R := K) a using TensorProduct.inductionOn with
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add t t' ht ht' => rw [map_add, ← ht, ← ht']
  have hR : TensorProduct.comm K A A (comul a) = conv (κ₂ (K := K) (A := A)) κ₁ a := by
    rw [conv_apply]
    induction comul (R := K) a using TensorProduct.inductionOn with
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  rw [hR, hL, ← sum_proj π a, map_sum, map_sum]
  exact (Finset.sum_congr rfl fun n _ => key n _ (proj_mem π n a)).symm

theorem isCocomm (h : IsExtension φ π)
    (hD : ∀ e : AddMonoidAlgebra K M, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Coalgebra.IsCocomm K A :=
  ⟨LinearMap.ext fun a => comm_comul h hD a⟩

end Commutator

end Extension

end Langlands.ConnectedExtensionHopf
