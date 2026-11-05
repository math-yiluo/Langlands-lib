import Langlands.Algebra.CentralTorusExtensionHopf
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Central split-torus extensions of polynomial Hopf algebras

Homogeneous invertible modules and scalar units give a Hopf section of the
restriction map to a central split torus when the quotient has polynomial coordinates.
-/

noncomputable section

universe u v w z

open TensorProduct Coalgebra

namespace Langlands.CentralTorusVectorExtensionHopf

open GroupAlgebraCoaction

variable {K : Type u} [Field K] {J : Type w}
variable {A : Type v} [CommRing A] [HopfAlgebra K A]
variable {B : Type z} [CommRing B] [Bialgebra K B]

/-- Central extension data with an arbitrary commutative quotient Hopf algebra. -/
structure IsCentralExtension (φ : B →ₐc[K] A)
    (π : A →ₐc[K] AddMonoidAlgebra K (J → ℤ)) : Prop where
  injective : Function.Injective φ
  surjective : Function.Surjective π
  comp_eq : ∀ b, π (φ b) = algebraMap K _ (counit (R := K) b)
  isCentral : IsCentral π
  invariants : ∀ a ∈ grade π 0, ∃ b, φ b = a

variable {φ : B →ₐc[K] A} {π : A →ₐc[K] AddMonoidAlgebra K (J → ℤ)}

theorem map_mem_grade_zero (h : ∀ b, π (φ b) = algebraMap K _ (counit (R := K) b))
    (b : B) : φ b ∈ grade π 0 := by
  have key : (π : A →ₗ[K] AddMonoidAlgebra K (J → ℤ)).lTensor A ∘ₗ
      TensorProduct.map (φ : B →ₗ[K] A) φ =
        TensorProduct.map (φ : B →ₗ[K] A)
          (Algebra.linearMap K (AddMonoidAlgebra K (J → ℤ))) ∘ₗ
          (counit : B →ₗ[K] K).lTensor _ := by
    apply TensorProduct.ext'
    intro x y
    simp [h]
  rw [mem_grade_iff, coaction_apply, ← CoalgHomClass.map_comp_comul_apply φ b,
    ← LinearMap.comp_apply, key, LinearMap.comp_apply, lTensor_counit_comul]
  simp [AddMonoidAlgebra.smul_single]

variable [Subsingleton (CommRing.Pic B)]

/-- Triviality of the quotient Picard group supplies a homogeneous unit in every degree. -/
theorem exists_unit_mem_grade (h : IsCentralExtension φ π) (n : J → ℤ) :
    ∃ u : Aˣ, (u : A) ∈ grade π n := by
  let : Algebra (B) A := (φ : _ →ₐ[K] A).toRingHom.toAlgebra
  have hsmul : ∀ (b : B) (a : A), b • a = φ b * a :=
    fun b a => Algebra.smul_def b a
  have : FaithfulSMul (B) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr h.injective
  let P : (J → ℤ) → Submodule (B) A := fun m =>
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
      obtain ⟨a, ha, h1⟩ := CentralTorusExtensionHopf.exists_mem_grade_counit_eq_one h.surjective (-n)
      have h2 := one_mem_grade_neg_mul_grade π ha h1
      rw [neg_neg] at h2
      refine Submodule.mul_induction_on h2 (fun x hx y hy => ?_) (fun _ _ => add_mem)
      exact Submodule.mul_mem_mul ((hP n x).mpr hx) ((hP (-n) y).mpr hy)
  have hU : IsUnit (P n) := IsUnit.of_mul_eq_one _ hmul
  have hker : hU.unit ∈ (Submodule.unitsToPic (B) A).ker :=
    Subsingleton.elim _ _
  rw [Submodule.ker_unitsToPic] at hker
  obtain ⟨x, hx⟩ := hker
  have hx' : Submodule.span (B) {(x : A)} = P n :=
    congrArg Units.val hx
  refine ⟨x, ?_⟩
  rw [← hP, ← hx']
  exact Submodule.mem_span_singleton_self _


section Divide

variable (h : IsCentralExtension φ π) {n : J → ℤ} (u : Aˣ) (hu : (u : A) ∈ grade π n)

omit [Subsingleton (CommRing.Pic B)] in
include h hu in
theorem mul_inv_mem_range (a : A) :
    proj π n a * ((u⁻¹ : Aˣ) : A) ∈ LinearMap.range (φ : B →ₗ[K] A) := by
  have : proj π n a * ((u⁻¹ : Aˣ) : A) ∈ grade π 0 := by
    simpa using mul_mem_grade π (proj_mem π n a) (inv_mem_grade π u hu)
  obtain ⟨b, hb⟩ := h.invariants _ this
  exact ⟨b, hb⟩

/-- The map `a ↦ φ⁻¹ (aₙ u⁻¹)`, dividing the component of degree `n` by a unit of degree `n`. -/
def divide : A →ₗ[K] B :=
  (LinearEquiv.ofInjective (φ : B →ₗ[K] A)
    (fun _ _ hxy => h.injective hxy)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (LinearMap.mulRight K ((u⁻¹ : Aˣ) : A) ∘ₗ proj π n)
      (mul_inv_mem_range h u hu)

omit [Subsingleton (CommRing.Pic B)] in
theorem map_divide (a : A) : φ (divide h u hu a) = proj π n a * ((u⁻¹ : Aˣ) : A) :=
  LinearEquiv.ofInjective_symm_apply (f := (φ : B →ₗ[K] A))
    (h := fun _ _ hxy => h.injective hxy) _

omit [Subsingleton (CommRing.Pic B)] in
theorem map_divide_mul (a : A) : φ (divide h u hu a) * u = proj π n a := by
  rw [map_divide, mul_assoc, u.inv_mul, mul_one]

omit [Subsingleton (CommRing.Pic B)] in
theorem map_proj_proj (t : A ⊗[K] A) :
    TensorProduct.map (proj π n) (proj π n) t =
      Algebra.TensorProduct.map (φ : B →ₐ[K] A)
        (φ : B →ₐ[K] A)
        (TensorProduct.map (divide h u hu) (divide h u hu) t) * ((u : A) ⊗ₜ[K] (u : A)) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [BialgHom.coe_toAlgHom, map_divide_mul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_mul]

omit [Subsingleton (CommRing.Pic B)] in
/-- The comultiplication of a unit of degree `n` is `(φ ⊗ φ) f · (u ⊗ u)` for some `f`. -/
theorem comul_eq_map_mul :
    comul (R := K) (u : A) =
      Algebra.TensorProduct.map (φ : B →ₐ[K] A)
        (φ : B →ₐ[K] A)
        (TensorProduct.map (divide h u hu) (divide h u hu) (comul (u : A))) *
          ((u : A) ⊗ₜ[K] (u : A)) := by
  rw [← map_proj_proj h u hu, ← h.isCentral.comul_of_mem hu]

end Divide

omit [Subsingleton (CommRing.Pic B)] in
theorem map_map_injective (h : IsCentralExtension φ π) :
    Function.Injective (Algebra.TensorProduct.map (φ : B →ₐ[K] A)
        (φ : B →ₐ[K] A)) :=
  TensorProduct.map_injective_of_flat_flat (φ : B →ₗ[K] A)
    (φ : B →ₗ[K] A) h.injective h.injective

omit [Subsingleton (CommRing.Pic B)] in
/-- If tensor-square units of the quotient are scalars, a homogeneous unit
becomes group-like after scalar normalization. -/
theorem exists_isGroupLikeElem_smul (h : IsCentralExtension φ π)
    (hscalar : ∀ f : B ⊗[K] B, IsUnit f → ∃ d : K, f = d • 1)
    {n : J → ℤ} (u : Aˣ) (hu : (u : A) ∈ grade π n) :
    ∃ d : K, IsGroupLikeElem K (d • (u : A)) := by
  obtain ⟨f, h1⟩ : ∃ f, comul (R := K) (u : A) =
      Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A) f *
        ((u : A) ⊗ₜ[K] (u : A)) := ⟨_, comul_eq_map_mul h u hu⟩
  obtain ⟨f', h2⟩ : ∃ f', comul (R := K) ((u⁻¹ : Aˣ) : A) =
      Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A) f' *
        (((u⁻¹ : Aˣ) : A) ⊗ₜ[K] ((u⁻¹ : Aˣ) : A)) :=
    ⟨_, comul_eq_map_mul h u⁻¹ (inv_mem_grade π u hu)⟩
  have hff' : f * f' = 1 := by
    apply map_map_injective h
    rw [map_mul, map_one, ← Bialgebra.comul_one (R := K) (A := A), ← u.mul_inv,
      Bialgebra.comul_mul, h1, h2, mul_mul_mul_comm, Algebra.TensorProduct.tmul_mul_tmul,
      u.mul_inv, ← Algebra.TensorProduct.one_def, mul_one]
  obtain ⟨d, rfl⟩ := hscalar f (IsUnit.of_mul_eq_one f' hff')
  have hcomul : comul (R := K) (u : A) = d • ((u : A) ⊗ₜ[K] (u : A)) := by
    simpa using h1
  have hl := Coalgebra.rTensor_counit_comul (R := K) (u : A)
  rw [hcomul] at hl
  apply_fun TensorProduct.lid K A at hl
  simp only [map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    smul_smul] at hl
  have he : counit (R := K) (u : A) ≠ 0 :=
    (u.isUnit.map (Bialgebra.counitAlgHom K A)).ne_zero
  have hde : d * counit (R := K) (u : A) = 1 := by
    have hh := congrArg (counit (R := K)) hl
    simp only [map_smul, smul_eq_mul] at hh
    exact mul_right_cancel₀ he hh
  refine ⟨d, ⟨?_, ?_⟩⟩
  · rw [map_smul, smul_eq_mul, hde]
  · rw [map_smul, hcomul, smul_smul, TensorProduct.smul_tmul_smul]

/-- Every weight of the central torus lifts to a group-like element. -/
theorem exists_groupLike (h : IsCentralExtension φ π)
    (hscalar : ∀ f : B ⊗[K] B, IsUnit f → ∃ d : K, f = d • 1) (n : J → ℤ) :
    ∃ g : Additive (GroupLike K A), CentralTorusExtensionHopf.degree π g = n := by
  obtain ⟨u, hu⟩ := exists_unit_mem_grade h n
  obtain ⟨d, hd⟩ := exists_isGroupLikeElem_smul h hscalar u hu
  exact ⟨Additive.ofMul ⟨_, hd⟩,
    CentralTorusExtensionHopf.degree_eq_of_mem_grade (Submodule.smul_mem _ d hu)⟩

variable [Finite J]

open Classical in
/-- Choose lifts on a lattice basis, then extend additively. -/
def weightSection (h : IsCentralExtension φ π)
    (hscalar : ∀ f : B ⊗[K] B, IsUnit f → ∃ d : K, f = d • 1) :
    (J → ℤ) →+ Additive (GroupLike K A) :=
  ((Pi.basisFun ℤ J).constr ℤ fun j =>
    Classical.choose (exists_groupLike h hscalar (Pi.single j 1))).toAddMonoidHom

open Classical in
/-- The chosen lift has its prescribed degree. -/
theorem degree_weightSection (h : IsCentralExtension φ π)
    (hscalar : ∀ f : B ⊗[K] B, IsUnit f → ∃ d : K, f = d • 1) (n : J → ℤ) :
    CentralTorusExtensionHopf.degree π (weightSection h hscalar n) = n := by
  have : (CentralTorusExtensionHopf.degree π).toIntLinearMap ∘ₗ
      (Pi.basisFun ℤ J).constr ℤ (fun j =>
        Classical.choose (exists_groupLike h hscalar (Pi.single j 1))) = LinearMap.id :=
    (Pi.basisFun ℤ J).ext fun j => by
      rw [LinearMap.comp_apply, Module.Basis.constr_basis, LinearMap.id_apply, Pi.basisFun_apply]
      exact Classical.choose_spec (exists_groupLike h hscalar (Pi.single j 1))
  exact LinearMap.congr_fun this n

/-- Extend the lifted character lattice to a bialgebra map. -/
def sectionMap (h : IsCentralExtension φ π)
    (hscalar : ∀ f : B ⊗[K] B, IsUnit f → ∃ d : K, f = d • 1) :
    AddMonoidAlgebra K (J → ℤ) →ₐc[K] A :=
  .ofAlgHom
    (AddMonoidAlgebra.lift K A (J → ℤ)
      { toFun n := ((weightSection h hscalar n.toAdd).toMul : A)
        map_one' := by simp
        map_mul' := by intro n m; simp })
    (by ext; simp) (by ext; simp)

/-- Restriction to the torus is the identity. -/
theorem comp_sectionMap (h : IsCentralExtension φ π)
    (hscalar : ∀ f : B ⊗[K] B, IsUnit f → ∃ d : K, f = d • 1) :
    π.comp (sectionMap h hscalar) = BialgHom.id K _ := by
  apply BialgHom.coe_toAlgHom_injective
  apply AddMonoidAlgebra.algHom_ext (fun n => ?_) (by ext)
  change π ((AddMonoidAlgebra.lift K A (J → ℤ) _) (AddMonoidAlgebra.single n 1)) =
    AddMonoidAlgebra.single n 1
  rw [AddMonoidAlgebra.lift_single, one_smul]
  change π ((weightSection h hscalar n).toMul : A) = AddMonoidAlgebra.single n 1
  rw [CentralTorusExtensionHopf.map_eq_single_degree, degree_weightSection]

end Langlands.CentralTorusVectorExtensionHopf

namespace Langlands.PolynomialTensorUnits

variable (K : Type u) [Field K] (I : Type w)

/-- Units of the tensor square of a polynomial algebra over a field are scalar. -/
theorem exists_eq_smul_one (f : MvPolynomial I K ⊗[K] MvPolynomial I K) (hf : IsUnit f) :
    ∃ d : K, f = d • 1 := by
  let e := MvPolynomial.tensorEquivSum K I I K
  have he : IsUnit (e f) := hf.map e.toRingHom
  obtain ⟨d, _, hd⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp he
  refine ⟨d, e.injective ?_⟩
  rw [map_smul, map_one]
  simpa [Algebra.smul_def, MvPolynomial.algebraMap_eq] using hd

end Langlands.PolynomialTensorUnits
