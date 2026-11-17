import Langlands.Algebra.CocommutativeGradedGroupLike
import Langlands.Algebra.GroupAlgebraCoaction
import Langlands.Algebra.IntLatticeAlgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Hopf algebras of central extensions of split tori by diagonalizable groups

Let `K` be a field and `A` a commutative Hopf algebra over `K`, with bialgebra maps
`φ : K[ℤ^I] → A` and `π : A → K[N]` for a commutative group `N`. Geometrically `φ` is a quotient
map `E → T` onto a split torus and `π` a central closed subgroup `D(N) → E` with `T = E / D(N)`.
Then `A` is spanned by its group-like elements, and these form a finitely generated group when
`N` is finitely generated. This generalizes `CentralTorusExtensionHopf`, where `N = ℤ^J`; the
arguments up to `exists_degree_eq` are copied from that module with `ℤ^J` replaced by `N`. -/

noncomputable section

universe u v w w'

open TensorProduct Coalgebra

namespace Langlands.CentralDiagonalizableExtensionHopf

open GroupAlgebraCoaction

variable {K : Type u} [Field K] {I : Type w} {N : Type w'} [AddCommGroup N]
variable {A : Type v} [CommRing A] [HopfAlgebra K A]

/-- The algebraic data of a central extension `1 → Z → E → T → 1` of the split torus with
character lattice `ℤ^I` by the diagonalizable group `Z = D(N)`, in terms of the coordinate Hopf
algebra `A` of `E`: `φ` is injective (`E → T` is faithfully flat), `π` is surjective (`Z → E` is
a closed immersion), `π ∘ φ` is trivial, the coaction of `K[N]` through `π` is central, and its
invariants are the image of `φ` (`T` is the quotient `E / Z`). -/
structure IsCentralExtension (φ : AddMonoidAlgebra K (I → ℤ) →ₐc[K] A)
    (π : A →ₐc[K] AddMonoidAlgebra K N) : Prop where
  injective : Function.Injective φ
  surjective : Function.Surjective π
  comp_eq : ∀ b, π (φ b) = algebraMap K _ (counit (R := K) b)
  isCentral : IsCentral π
  invariants : ∀ a ∈ grade π 0, ∃ b, φ b = a

variable {φ : AddMonoidAlgebra K (I → ℤ) →ₐc[K] A} {π : A →ₐc[K] AddMonoidAlgebra K N}

theorem map_mem_grade_zero (h : ∀ b, π (φ b) = algebraMap K _ (counit (R := K) b))
    (b : AddMonoidAlgebra K (I → ℤ)) : φ b ∈ grade π 0 := by
  have key : (π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A ∘ₗ
      TensorProduct.map (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A) φ =
        TensorProduct.map (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A)
          (Algebra.linearMap K (AddMonoidAlgebra K N)) ∘ₗ
          (counit : AddMonoidAlgebra K (I → ℤ) →ₗ[K] K).lTensor _ := by
    apply TensorProduct.ext'
    intro x y
    simp [h]
  rw [mem_grade_iff, coaction_apply, ← CoalgHomClass.map_comp_comul_apply φ b,
    ← LinearMap.comp_apply, key, LinearMap.comp_apply, lTensor_counit_comul]
  simp [AddMonoidAlgebra.smul_single]

theorem exists_mem_grade_counit_eq_one (hπ : Function.Surjective π) (n : N) :
    ∃ a ∈ grade π n, counit (R := K) a = 1 := by
  obtain ⟨a, ha⟩ := hπ (AddMonoidAlgebra.single n 1)
  refine ⟨proj π n a, proj_mem π n a, ?_⟩
  rw [counit_proj, ha]
  simp [AddMonoidAlgebra.coeff_single]

variable [Finite I]

/-- Every homogeneous component contains a unit: the components are invertible modules over
the group algebra `K[ℤ^I]`, whose Picard group is trivial. -/
theorem exists_unit_mem_grade (h : IsCentralExtension φ π) (n : N) :
    ∃ u : Aˣ, (u : A) ∈ grade π n := by
  let : Algebra (AddMonoidAlgebra K (I → ℤ)) A := (φ : _ →ₐ[K] A).toRingHom.toAlgebra
  have hsmul : ∀ (b : AddMonoidAlgebra K (I → ℤ)) (a : A), b • a = φ b * a :=
    fun b a => Algebra.smul_def b a
  have : FaithfulSMul (AddMonoidAlgebra K (I → ℤ)) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr h.injective
  have := IntLatticeAlgebra.subsingleton_pic K I
  let P : N → Submodule (AddMonoidAlgebra K (I → ℤ)) A := fun m =>
    { carrier := grade π m
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun b a ha => by
        rw [hsmul]
        simpa using mul_mem_grade π (map_mem_grade_zero h.comp_eq b) ha }
  have hP : ∀ m a, a ∈ P m ↔ a ∈ grade π m := fun _ _ => Iff.rfl
  have hmul : P n * P (-n) = 1 := by
    apply le_antisymm
    · rw [Submodule.mul_le]
      intro a ha a' ha'
      have : a * a' ∈ grade π 0 := by simpa using mul_mem_grade π ha ha'
      obtain ⟨b, hb⟩ := h.invariants _ this
      rw [Submodule.one_eq_range]
      exact ⟨b, hb⟩
    · rw [Submodule.one_le]
      obtain ⟨a, ha, h1⟩ := exists_mem_grade_counit_eq_one h.surjective (-n)
      have h2 := one_mem_grade_neg_mul_grade π ha h1
      rw [neg_neg] at h2
      refine Submodule.mul_induction_on h2 (fun x hx y hy => ?_) (fun _ _ => add_mem)
      exact Submodule.mul_mem_mul ((hP n x).mpr hx) ((hP (-n) y).mpr hy)
  have hU : IsUnit (P n) := IsUnit.of_mul_eq_one _ hmul
  have hker : hU.unit ∈ (Submodule.unitsToPic (AddMonoidAlgebra K (I → ℤ)) A).ker :=
    Subsingleton.elim _ _
  rw [Submodule.ker_unitsToPic] at hker
  obtain ⟨x, hx⟩ := hker
  have hx' : Submodule.span (AddMonoidAlgebra K (I → ℤ)) {(x : A)} = P n :=
    congrArg Units.val hx
  refine ⟨x, ?_⟩
  rw [← hP, ← hx']
  exact Submodule.mem_span_singleton_self _


section Divide

variable (h : IsCentralExtension φ π) {n : N} (u : Aˣ) (hu : (u : A) ∈ grade π n)

omit [Finite I] in
include h hu in
theorem mul_inv_mem_range (a : A) :
    proj π n a * ((u⁻¹ : Aˣ) : A) ∈ LinearMap.range (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A) := by
  have : proj π n a * ((u⁻¹ : Aˣ) : A) ∈ grade π 0 := by
    simpa using mul_mem_grade π (proj_mem π n a) (inv_mem_grade π u hu)
  obtain ⟨b, hb⟩ := h.invariants _ this
  exact ⟨b, hb⟩

/-- The map `a ↦ φ⁻¹ (aₙ u⁻¹)`, dividing the component of degree `n` by a unit of degree `n`. -/
def divide : A →ₗ[K] AddMonoidAlgebra K (I → ℤ) :=
  (LinearEquiv.ofInjective (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A)
    (fun _ _ hxy => h.injective hxy)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (LinearMap.mulRight K ((u⁻¹ : Aˣ) : A) ∘ₗ proj π n)
      (mul_inv_mem_range h u hu)

omit [Finite I] in
theorem map_divide (a : A) : φ (divide h u hu a) = proj π n a * ((u⁻¹ : Aˣ) : A) :=
  LinearEquiv.ofInjective_symm_apply (f := (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A))
    (h := fun _ _ hxy => h.injective hxy) _

omit [Finite I] in
theorem map_divide_mul (a : A) : φ (divide h u hu a) * u = proj π n a := by
  rw [map_divide, mul_assoc, u.inv_mul, mul_one]

omit [Finite I] in
theorem map_proj_proj (t : A ⊗[K] A) :
    TensorProduct.map (proj π n) (proj π n) t =
      Algebra.TensorProduct.map (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A)
        (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A)
        (TensorProduct.map (divide h u hu) (divide h u hu) t) * ((u : A) ⊗ₜ[K] (u : A)) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [BialgHom.coe_toAlgHom, map_divide_mul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_mul]

omit [Finite I] in
/-- The comultiplication of a unit of degree `n` is `(φ ⊗ φ) f · (u ⊗ u)` for some `f`. -/
theorem comul_eq_map_mul :
    comul (R := K) (u : A) =
      Algebra.TensorProduct.map (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A)
        (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A)
        (TensorProduct.map (divide h u hu) (divide h u hu) (comul (u : A))) *
          ((u : A) ⊗ₜ[K] (u : A)) := by
  rw [← map_proj_proj h u hu, ← h.isCentral.comul_of_mem hu]

end Divide

omit [Finite I] in
theorem map_map_injective (h : IsCentralExtension φ π) :
    Function.Injective (Algebra.TensorProduct.map (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A)
        (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A)) :=
  TensorProduct.map_injective_of_flat_flat (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A)
    (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A) h.injective h.injective

/-- A unit of degree `n` becomes group-like after rescaling. -/
theorem exists_isGroupLikeElem_smul (h : IsCentralExtension φ π) {n : N} (u : Aˣ)
    (hu : (u : A) ∈ grade π n) : ∃ d : K, IsGroupLikeElem K (d • (u : A)) := by
  obtain ⟨f, h1⟩ : ∃ f, comul (R := K) (u : A) =
      Algebra.TensorProduct.map (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A)
        (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A) f * ((u : A) ⊗ₜ[K] (u : A)) :=
    ⟨_, comul_eq_map_mul h u hu⟩
  obtain ⟨f', h2⟩ : ∃ f', comul (R := K) ((u⁻¹ : Aˣ) : A) =
      Algebra.TensorProduct.map (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A)
        (φ : AddMonoidAlgebra K (I → ℤ) →ₐ[K] A) f' *
          (((u⁻¹ : Aˣ) : A) ⊗ₜ[K] ((u⁻¹ : Aˣ) : A)) :=
    ⟨_, comul_eq_map_mul h u⁻¹ (inv_mem_grade π u hu)⟩
  have hff' : f * f' = 1 := by
    apply map_map_injective h
    rw [map_mul, map_one, ← Bialgebra.comul_one (R := K) (A := A), ← u.mul_inv,
      Bialgebra.comul_mul, h1, h2, mul_mul_mul_comm, Algebra.TensorProduct.tmul_mul_tmul,
      u.mul_inv, ← Algebra.TensorProduct.one_def, mul_one]
  have hf : IsUnit (AddMonoidAlgebra.scalarTensorEquiv K (AddMonoidAlgebra K (I → ℤ)) f) :=
    (IsUnit.of_mul_eq_one f' hff').map _
  obtain ⟨m₂, c, hc⟩ := IntLatticeAlgebra.exists_eq_single_of_isUnit _ I hf
  obtain ⟨m₁, d, hd⟩ := IntLatticeAlgebra.exists_eq_single_of_isUnit K I c.isUnit
  have hf' : f = AddMonoidAlgebra.single m₁ (d : K) ⊗ₜ AddMonoidAlgebra.single m₂ 1 := by
    rw [← (AddMonoidAlgebra.scalarTensorEquiv K _).symm_apply_apply f, hc, hd,
      AddMonoidAlgebra.scalarTensorEquiv_symm_single]
  have hcomul : comul (R := K) (u : A) =
      (φ (AddMonoidAlgebra.single m₁ (d : K)) * u) ⊗ₜ (φ (AddMonoidAlgebra.single m₂ 1) * u) := by
    rw [h1, hf', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  -- the two counit identities force `m₁ = m₂ = 0` and `d ε(u) = 1`
  have hl := Coalgebra.rTensor_counit_comul (R := K) (u : A)
  have hr := Coalgebra.lTensor_counit_comul (R := K) (u : A)
  rw [hcomul] at hl hr
  apply_fun TensorProduct.lid K A at hl
  apply_fun TensorProduct.rid K A at hr
  simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.lid_tmul,
    TensorProduct.rid_tmul, Bialgebra.counit_mul, CoalgHomClass.counit_comp_apply,
    AddMonoidAlgebra.counit_single, one_smul, CommSemiring.counit_apply, one_mul] at hl hr
  have key : ∀ (m : I → ℤ) (c : K), c • (φ (AddMonoidAlgebra.single m 1) * u) = u →
      m = 0 ∧ c = 1 := by
    intro m c hmc
    have h3 : φ (AddMonoidAlgebra.single m c) = φ (AddMonoidAlgebra.single 0 1) := by
      rw [← AddMonoidAlgebra.one_def, map_one]
      apply (Units.mul_left_inj u).mp
      rw [one_mul]
      conv_rhs => rw [← hmc]
      rw [← smul_mul_assoc, ← map_smul, AddMonoidAlgebra.smul_single', mul_one]
    simpa using AddMonoidAlgebra.single_inj.mp (h.injective h3)
  have hsingle : AddMonoidAlgebra.single m₁ (d : K) = (d : K) • AddMonoidAlgebra.single m₁ 1 := by
    rw [AddMonoidAlgebra.smul_single', mul_one]
  rw [hsingle, map_smul, smul_mul_assoc, smul_smul] at hr
  obtain ⟨rfl, -⟩ := key m₁ _ hr
  obtain ⟨rfl, hde⟩ := key m₂ _ hl
  refine ⟨d, ⟨?_, ?_⟩⟩
  · rw [map_smul, smul_eq_mul, hde]
  · rw [map_smul, hcomul, hsingle, map_smul, ← AddMonoidAlgebra.one_def, map_one, one_mul,
      smul_mul_assoc, one_mul, ← TensorProduct.tmul_smul]

/-! ### Group-like elements and their degrees -/

omit [Finite I] in
theorem mem_grade_of_isGroupLikeElem {g : A} (hg : IsGroupLikeElem K g) {n : N}
    (hn : π g = AddMonoidAlgebra.single n 1) : g ∈ grade π n := by
  have hn' : (π : A →ₗ[K] AddMonoidAlgebra K N) g = AddMonoidAlgebra.single n 1 := hn
  rw [mem_grade_iff, coaction_apply, hg.comul_eq_tmul_self, LinearMap.lTensor_tmul, hn',
    ← AddMonoidAlgebra.scalarTensorEquiv_symm_single, AlgEquiv.apply_symm_apply]

omit [Finite I] in
theorem eq_of_mem_grade {a : A} (ha : a ≠ 0) {m n : N} (hm : a ∈ grade π m)
    (hn : a ∈ grade π n) : m = n := by
  rw [mem_grade_iff] at hm hn
  exact (AddMonoidAlgebra.single_left_inj ha).mp (hm.symm.trans hn)

omit [Finite I] in
theorem exists_map_eq_single (g : GroupLike K A) : ∃ n, π g = AddMonoidAlgebra.single n 1 := by
  obtain ⟨n, hn⟩ := AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one.mp
    (g.isGroupLikeElem_val.map π)
  exact ⟨n, hn.symm⟩

variable (π) in
/-- The degree of a group-like element `g`: the character `n` with `π g = Xⁿ`. -/
def degree : Additive (GroupLike K A) →+ N :=
  AddMonoidHom.mk' (fun g => Classical.choose (exists_map_eq_single (π := π) g.toMul))
    fun g g' => by
      have hg := Classical.choose_spec (exists_map_eq_single (π := π) g.toMul)
      have hg' := Classical.choose_spec (exists_map_eq_single (π := π) g'.toMul)
      have hgg' := Classical.choose_spec (exists_map_eq_single (π := π) (g + g').toMul)
      have e : π ((g + g').toMul : A) = π (g.toMul : A) * π (g'.toMul : A) := by
        rw [toMul_add, GroupLike.val_mul, map_mul]
      have e2 := (e.symm.trans hgg').symm.trans (congrArg₂ (· * ·) hg hg')
      rw [AddMonoidAlgebra.single_mul_single, one_mul] at e2
      exact (AddMonoidAlgebra.single_left_inj one_ne_zero).mp e2

omit [Finite I] in
theorem map_eq_single_degree (g : Additive (GroupLike K A)) :
    π (g.toMul : A) = AddMonoidAlgebra.single (degree π g) 1 :=
  Classical.choose_spec (exists_map_eq_single (π := π) g.toMul)

omit [Finite I] in
theorem mem_grade_degree (g : Additive (GroupLike K A)) :
    (g.toMul : A) ∈ grade π (degree π g) :=
  mem_grade_of_isGroupLikeElem g.toMul.isGroupLikeElem_val (map_eq_single_degree g)

omit [Finite I] in
theorem degree_eq_of_mem_grade {g : Additive (GroupLike K A)} {n : N}
    (hg : (g.toMul : A) ∈ grade π n) : degree π g = n :=
  eq_of_mem_grade g.toMul.isGroupLikeElem_val.ne_zero (mem_grade_degree g) hg

variable (φ) in
/-- The group-like elements `φ(Xᵐ)` coming from the quotient torus. -/
def iota : (I → ℤ) →+ Additive (GroupLike K A) :=
  AddMonoidHom.mk' (fun m => Additive.ofMul ⟨φ (AddMonoidAlgebra.single m 1),
      (AddMonoidAlgebra.isGroupLikeElem_single_one m).map φ⟩) fun m m' => by
    apply Additive.toMul.injective
    ext
    simp only [toMul_ofMul, toMul_add, GroupLike.val_mul, ← map_mul,
      AddMonoidAlgebra.single_mul_single, mul_one]

omit [Finite I] in
theorem iota_val (m : I → ℤ) :
    (((iota φ m).toMul : GroupLike K A) : A) = φ (AddMonoidAlgebra.single m 1) :=
  rfl

omit [Finite I] in
theorem degree_iota (h : IsCentralExtension φ π) (m : I → ℤ) : degree π (iota φ m) = 0 :=
  degree_eq_of_mem_grade (map_mem_grade_zero h.comp_eq _)

omit [Finite I] in
theorem isGroupLikeElem_of_map (h : IsCentralExtension φ π) {b : AddMonoidAlgebra K (I → ℤ)}
    (hb : IsGroupLikeElem K (φ b)) : IsGroupLikeElem K b where
  counit_eq_one := by rw [← CoalgHomClass.counit_comp_apply φ b]; exact hb.counit_eq_one
  comul_eq_tmul_self := by
    apply TensorProduct.map_injective_of_flat_flat (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A)
      (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A) h.injective h.injective
    rw [CoalgHomClass.map_comp_comul_apply, hb.comul_eq_tmul_self, TensorProduct.map_tmul]
    rfl

theorem exists_degree_eq (h : IsCentralExtension φ π) (n : N) :
    ∃ g : Additive (GroupLike K A), degree π g = n := by
  obtain ⟨u, hu⟩ := exists_unit_mem_grade h n
  obtain ⟨d, hd⟩ := exists_isGroupLikeElem_smul h u hu
  exact ⟨Additive.ofMul ⟨_, hd⟩, degree_eq_of_mem_grade (Submodule.smul_mem _ d hu)⟩

theorem exists_isGroupLikeElem_mem_grade (h : IsCentralExtension φ π) (n : N) :
    ∃ g : A, IsGroupLikeElem K g ∧ g ∈ grade π n := by
  obtain ⟨u, hu⟩ := exists_unit_mem_grade h n
  obtain ⟨d, hd⟩ := exists_isGroupLikeElem_smul h u hu
  exact ⟨_, hd, Submodule.smul_mem _ d hu⟩

omit [Finite I] in
/-- The degree-zero component `φ(K[ℤ^I])` is spanned by the group-like elements `φ(Xᵐ)`. -/
theorem grade_zero_le_span (h : IsCentralExtension φ π) :
    grade π 0 ≤ Submodule.span K {x : A | IsGroupLikeElem K x} := by
  intro a ha
  obtain ⟨b, rfl⟩ := h.invariants a ha
  have hle : (Submodule.span K {x : AddMonoidAlgebra K (I → ℤ) | IsGroupLikeElem K x}).map
      (φ : AddMonoidAlgebra K (I → ℤ) →ₗ[K] A) ≤ Submodule.span K {x : A | IsGroupLikeElem K x} := by
    rw [Submodule.map_span_le]
    intro x hx
    exact Submodule.subset_span (hx.map φ)
  apply hle
  refine Submodule.mem_map_of_mem ?_
  rw [AddMonoidAlgebra.span_isGroupLikeElem]
  exact Submodule.mem_top

/-- **Group-like elements span.** The Hopf algebra of a central extension of a split torus by a
diagonalizable group is spanned by its group-like elements. -/
theorem span_isGroupLikeElem (h : IsCentralExtension φ π) :
    Submodule.span K {x : A | IsGroupLikeElem K x} = ⊤ :=
  GroupAlgebraCoaction.span_isGroupLikeElem_eq_top_of_forall_grade π
    (exists_isGroupLikeElem_mem_grade h) (grade_zero_le_span h)

omit [Finite I] in
/-- The group-like elements of degree zero are exactly the `φ(Xᵐ)`. -/
theorem ker_degree_le_range_iota (h : IsCentralExtension φ π) {g : Additive (GroupLike K A)}
    (hg : degree π g = 0) : ∃ m, iota φ m = g := by
  have hg0 : (g.toMul : A) ∈ grade π 0 := hg ▸ mem_grade_degree g
  obtain ⟨b, hb⟩ := h.invariants _ hg0
  have hbG : IsGroupLikeElem K b :=
    isGroupLikeElem_of_map h (hb ▸ g.toMul.isGroupLikeElem_val)
  obtain ⟨m, hm⟩ := AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one.mp hbG
  refine ⟨m, Additive.toMul.injective (GroupLike.val_injective ?_)⟩
  change φ (AddMonoidAlgebra.single m 1) = (g.toMul : A)
  rw [← hb, ← hm]

/-- **Finite generation.** If `N` is finitely generated, so is the group of group-like elements:
it is an extension of `N` (through `degree`, which is surjective) by a quotient of `ℤ^I` (the
image of `iota`). -/
theorem addGroupFG [AddGroup.FG N] (h : IsCentralExtension φ π) :
    AddGroup.FG (Additive (GroupLike K A)) := by
  have : Module.Finite ℤ N := Module.Finite.iff_addGroup_fg.mpr inferInstance
  rw [← Module.Finite.iff_addGroup_fg]
  let f := (degree π).toIntLinearMap
  let ι := (iota φ).toIntLinearMap
  have hker : LinearMap.ker f = LinearMap.range ι := by
    apply le_antisymm
    · intro g hg
      exact ker_degree_le_range_iota h hg
    · rintro _ ⟨m, rfl⟩
      exact degree_iota h m
  have hsurj : Function.Surjective f := fun n => exists_degree_eq h n
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_⟩
  · rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    exact Module.Finite.fg_top
  · rw [top_inf_eq, hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _

end Langlands.CentralDiagonalizableExtensionHopf
