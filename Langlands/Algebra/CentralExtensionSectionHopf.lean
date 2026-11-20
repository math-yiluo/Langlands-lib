import Langlands.Algebra.CentralDiagonalizableExtensionHopf
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # Sections of central extensions by diagonalizable groups, in terms of Hopf algebras

Let `K` be a field and let `φ : B → A` and `π : A → K[N]` be maps of commutative Hopf algebras
over `K`. Geometrically `Spec A = E` is a group, `Spec φ : E → Spec B` is a quotient map and
`Spec π : D(N) → E` is a central closed subgroup with `Spec B = E / D(N)`.

Assume that the Picard group of `B` is trivial and that every unit of `B ⊗ B` is a scalar (for
example `B` a polynomial ring over `K`). Then every homogeneous component of the grading of `A`
defined by `π` contains exactly one group-like element, and dividing each component by its
group-like element gives a bialgebra map `σ : A → B` with `σ ∘ φ = id`. Geometrically, `σ` is a
homomorphic section of the quotient map `E → E / D(N)`. -/

noncomputable section

universe u v v' w

open TensorProduct Coalgebra

namespace Langlands.CentralExtensionSectionHopf

open GroupAlgebraCoaction

variable {K : Type u} [Field K] {N : Type w} [AddCommGroup N]
variable {A : Type v} [CommRing A] [HopfAlgebra K A] {B : Type v'} [CommRing B] [HopfAlgebra K B]

/-- The algebraic data of a central extension `1 → D(N) → E → Spec B → 1`, in terms of the
coordinate Hopf algebra `A` of `E`: `φ` is injective (`E → Spec B` is faithfully flat), `π` is
surjective (`D(N) → E` is a closed immersion), `π ∘ φ` is trivial, the coaction of `K[N]`
through `π` is central, and its invariants are the image of `φ` (`Spec B` is `E / D(N)`). -/
structure IsCentralExtension (φ : B →ₐc[K] A) (π : A →ₐc[K] AddMonoidAlgebra K N) : Prop where
  injective : Function.Injective φ
  surjective : Function.Surjective π
  comp_eq : ∀ b, π (φ b) = algebraMap K _ (counit (R := K) b)
  isCentral : IsCentral π
  invariants : ∀ a ∈ grade π 0, ∃ b, φ b = a

variable {φ : B →ₐc[K] A} {π : A →ₐc[K] AddMonoidAlgebra K N}

theorem map_mem_grade_zero (h : ∀ b, π (φ b) = algebraMap K _ (counit (R := K) b)) (b : B) :
    φ b ∈ grade π 0 := by
  have key : (π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A ∘ₗ
      TensorProduct.map (φ : B →ₗ[K] A) φ =
        TensorProduct.map (φ : B →ₗ[K] A)
          (Algebra.linearMap K (AddMonoidAlgebra K N)) ∘ₗ
          (counit : B →ₗ[K] K).lTensor _ := by
    apply TensorProduct.ext'
    intro x y
    simp [h]
  rw [mem_grade_iff, coaction_apply, ← CoalgHomClass.map_comp_comul_apply φ b,
    ← LinearMap.comp_apply, key, LinearMap.comp_apply, lTensor_counit_comul]
  simp [AddMonoidAlgebra.smul_single]

/-- Every homogeneous component contains a unit: the components are invertible `B`-submodules
of `A`, and the Picard group of `B` is trivial. -/
theorem exists_unit_mem_grade [Subsingleton (CommRing.Pic B)] (h : IsCentralExtension φ π)
    (n : N) : ∃ u : Aˣ, (u : A) ∈ grade π n := by
  let : Algebra B A := (φ : B →ₐ[K] A).toRingHom.toAlgebra
  have hsmul : ∀ (b : B) (a : A), b • a = φ b * a :=
    fun b a => Algebra.smul_def b a
  have : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr h.injective
  let P : N → Submodule B A := fun m =>
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
      obtain ⟨a, ha, h1⟩ :=
        CentralDiagonalizableExtensionHopf.exists_mem_grade_counit_eq_one h.surjective (-n)
      have h2 := one_mem_grade_neg_mul_grade π ha h1
      rw [neg_neg] at h2
      refine Submodule.mul_induction_on h2 (fun x hx y hy => ?_) (fun _ _ => add_mem)
      exact Submodule.mul_mem_mul ((hP n x).mpr hx) ((hP (-n) y).mpr hy)
  have hU : IsUnit (P n) := IsUnit.of_mul_eq_one _ hmul
  have hker : hU.unit ∈ (Submodule.unitsToPic B A).ker :=
    Subsingleton.elim _ _
  rw [Submodule.ker_unitsToPic] at hker
  obtain ⟨x, hx⟩ := hker
  have hx' : Submodule.span B {(x : A)} = P n :=
    congrArg Units.val hx
  refine ⟨x, ?_⟩
  rw [← hP, ← hx']
  exact Submodule.mem_span_singleton_self _

section Divide

variable (h : IsCentralExtension φ π) {n : N} (u : Aˣ) (hu : (u : A) ∈ grade π n)

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

theorem map_divide (a : A) : φ (divide h u hu a) = proj π n a * ((u⁻¹ : Aˣ) : A) :=
  LinearEquiv.ofInjective_symm_apply (f := (φ : B →ₗ[K] A))
    (h := fun _ _ hxy => h.injective hxy) _

theorem map_divide_mul (a : A) : φ (divide h u hu a) * u = proj π n a := by
  rw [map_divide, mul_assoc, u.inv_mul, mul_one]

theorem map_proj_proj (t : A ⊗[K] A) :
    TensorProduct.map (proj π n) (proj π n) t =
      Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A)
        (TensorProduct.map (divide h u hu) (divide h u hu) t) * ((u : A) ⊗ₜ[K] (u : A)) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [BialgHom.coe_toAlgHom, map_divide_mul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_mul]

/-- The comultiplication of a unit of degree `n` is `(φ ⊗ φ) f · (u ⊗ u)` for some `f`. -/
theorem comul_eq_map_mul :
    comul (R := K) (u : A) =
      Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A)
        (TensorProduct.map (divide h u hu) (divide h u hu) (comul (u : A))) *
          ((u : A) ⊗ₜ[K] (u : A)) := by
  rw [← map_proj_proj h u hu, ← h.isCentral.comul_of_mem hu]

end Divide

theorem map_map_injective (h : IsCentralExtension φ π) :
    Function.Injective (Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A)) :=
  TensorProduct.map_injective_of_flat_flat (φ : B →ₗ[K] A) (φ : B →ₗ[K] A)
    h.injective h.injective

omit [HopfAlgebra K A] in
theorem nontrivial_of_bialgebra [Bialgebra K A] : Nontrivial A :=
  ⟨⟨0, 1, fun h01 => by
    have := congrArg (counit (R := K)) h01
    rw [map_zero, Bialgebra.counit_one] at this
    exact zero_ne_one this⟩⟩

/-- A unit of degree `n` becomes group-like after rescaling, when the units of `B ⊗ B` are
scalars. -/
theorem exists_isGroupLikeElem_smul (h : IsCentralExtension φ π)
    (hB : ∀ f : B ⊗[K] B, IsUnit f → ∃ c : K, f = algebraMap K _ c) {n : N} (u : Aˣ)
    (hu : (u : A) ∈ grade π n) : ∃ d : K, IsGroupLikeElem K (d • (u : A)) := by
  have : Nontrivial A := nontrivial_of_bialgebra (K := K)
  obtain ⟨f, h1⟩ : ∃ f, comul (R := K) (u : A) =
      Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A) f *
        ((u : A) ⊗ₜ[K] (u : A)) :=
    ⟨_, comul_eq_map_mul h u hu⟩
  obtain ⟨f', h2⟩ : ∃ f', comul (R := K) ((u⁻¹ : Aˣ) : A) =
      Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A) f' *
          (((u⁻¹ : Aˣ) : A) ⊗ₜ[K] ((u⁻¹ : Aˣ) : A)) :=
    ⟨_, comul_eq_map_mul h u⁻¹ (inv_mem_grade π u hu)⟩
  have hff' : f * f' = 1 := by
    apply map_map_injective h
    rw [map_mul, map_one, ← Bialgebra.comul_one (R := K) (A := A), ← u.mul_inv,
      Bialgebra.comul_mul, h1, h2, mul_mul_mul_comm, Algebra.TensorProduct.tmul_mul_tmul,
      u.mul_inv, ← Algebra.TensorProduct.one_def, mul_one]
  obtain ⟨c, hc⟩ := hB f (IsUnit.of_mul_eq_one f' hff')
  have hcomul : comul (R := K) (u : A) = c • ((u : A) ⊗ₜ[K] (u : A)) := by
    rw [h1, hc, AlgHom.commutes, Algebra.smul_def]
  have hl := Coalgebra.rTensor_counit_comul (R := K) (u : A)
  rw [hcomul, map_smul, LinearMap.rTensor_tmul] at hl
  apply_fun TensorProduct.lid K A at hl
  rw [map_smul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, one_smul, smul_smul] at hl
  have hce : c * counit (R := K) (u : A) = 1 := by
    have h3 : (c * counit (R := K) (u : A)) • (1 : A) = 1 := by
      have := congrArg (· * ((u⁻¹ : Aˣ) : A)) hl
      simpa only [smul_mul_assoc, u.mul_inv] using this
    rw [← Algebra.algebraMap_eq_smul_one, ← map_one (algebraMap K A)] at h3
    exact (algebraMap K A).injective h3
  refine ⟨c, ⟨?_, ?_⟩⟩
  · rw [map_smul, smul_eq_mul, hce]
  · rw [map_smul, hcomul, smul_smul, TensorProduct.smul_tmul_smul]

/-! ### Group-like elements and their degrees -/

theorem isGroupLikeElem_of_map (h : IsCentralExtension φ π) {b : B}
    (hb : IsGroupLikeElem K (φ b)) : IsGroupLikeElem K b where
  counit_eq_one := by rw [← CoalgHomClass.counit_comp_apply φ b]; exact hb.counit_eq_one
  comul_eq_tmul_self := by
    apply TensorProduct.map_injective_of_flat_flat (φ : B →ₗ[K] A) (φ : B →ₗ[K] A)
      h.injective h.injective
    rw [CoalgHomClass.map_comp_comul_apply, hb.comul_eq_tmul_self, TensorProduct.map_tmul]
    rfl

omit [HopfAlgebra K B] in
/-- If the units of `B ⊗ B` are scalars, so are the units of `B`. -/
theorem exists_eq_algebraMap_of_isUnit [Algebra K B]
    (hB : ∀ f : B ⊗[K] B, IsUnit f → ∃ c : K, f = algebraMap K _ c) {b : B} (hb : IsUnit b) :
    ∃ c : K, b = algebraMap K B c := by
  have hb' : IsUnit (b ⊗ₜ[K] (1 : B)) :=
    hb.map (Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B)
  obtain ⟨c, hc⟩ := hB _ hb'
  refine ⟨c, ?_⟩
  have := congrArg (Algebra.TensorProduct.lmul' K (S := B)) hc
  simpa using this

/-- The only group-like element of degree `0` is `1`. -/
theorem eq_one_of_isGroupLikeElem_mem_grade_zero (h : IsCentralExtension φ π)
    (hB : ∀ f : B ⊗[K] B, IsUnit f → ∃ c : K, f = algebraMap K _ c) {g : A}
    (hg : IsGroupLikeElem K g) (h0 : g ∈ grade π 0) : g = 1 := by
  obtain ⟨b, rfl⟩ := h.invariants g h0
  have hbG := isGroupLikeElem_of_map h hg
  obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_isUnit hB hbG.isUnit
  have hc : c = 1 := by
    have := hbG.counit_eq_one
    rwa [Bialgebra.counit_algebraMap] at this
  rw [hc, map_one, map_one]

theorem degree_injective (h : IsCentralExtension φ π)
    (hB : ∀ f : B ⊗[K] B, IsUnit f → ∃ c : K, f = algebraMap K _ c) :
    Function.Injective
      (CentralDiagonalizableExtensionHopf.degree π : Additive (GroupLike K A) →+ N) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  have h0 : (g.toMul : A) ∈ grade π 0 :=
    hg ▸ CentralDiagonalizableExtensionHopf.mem_grade_degree g
  have h1 := eq_one_of_isGroupLikeElem_mem_grade_zero h hB g.toMul.isGroupLikeElem_val h0
  apply Additive.toMul.injective
  apply GroupLike.val_injective
  rw [toMul_zero]
  exact h1

theorem exists_degree_eq [Subsingleton (CommRing.Pic B)] (h : IsCentralExtension φ π)
    (hB : ∀ f : B ⊗[K] B, IsUnit f → ∃ c : K, f = algebraMap K _ c) (n : N) :
    ∃ g : Additive (GroupLike K A), CentralDiagonalizableExtensionHopf.degree π g = n := by
  obtain ⟨u, hu⟩ := exists_unit_mem_grade h n
  obtain ⟨d, hd⟩ := exists_isGroupLikeElem_smul h hB u hu
  exact ⟨Additive.ofMul ⟨_, hd⟩,
    CentralDiagonalizableExtensionHopf.degree_eq_of_mem_grade (Submodule.smul_mem _ d hu)⟩

section Section

variable [Subsingleton (CommRing.Pic B)] (h : IsCentralExtension φ π)
  (hB : ∀ f : B ⊗[K] B, IsUnit f → ∃ c : K, f = algebraMap K _ c)

/-- The degree is an isomorphism from the group of group-like elements of `A` onto `N`. -/
def degreeEquiv : Additive (GroupLike K A) ≃+ N :=
  AddEquiv.ofBijective (CentralDiagonalizableExtensionHopf.degree π)
    ⟨degree_injective h hB, exists_degree_eq h hB⟩

/-- The group-like element of degree `n`. -/
def groupLikeOf (n : N) : A :=
  (((degreeEquiv h hB).symm n).toMul : A)

theorem groupLikeOf_isGroupLikeElem (n : N) : IsGroupLikeElem K (groupLikeOf h hB n) :=
  ((degreeEquiv h hB).symm n).toMul.isGroupLikeElem_val

theorem groupLikeOf_mem_grade (n : N) : groupLikeOf h hB n ∈ grade π n := by
  have hm :=
    CentralDiagonalizableExtensionHopf.mem_grade_degree (π := π) ((degreeEquiv h hB).symm n)
  have e : CentralDiagonalizableExtensionHopf.degree π ((degreeEquiv h hB).symm n) = n :=
    (degreeEquiv h hB).apply_symm_apply n
  rwa [e] at hm

theorem groupLikeOf_add (m n : N) :
    groupLikeOf h hB (m + n) = groupLikeOf h hB m * groupLikeOf h hB n := by
  simp only [groupLikeOf, map_add, toMul_add, GroupLike.val_mul]

theorem groupLikeOf_zero : groupLikeOf h hB 0 = 1 := by
  simp only [groupLikeOf, map_zero, toMul_zero]
  rfl

/-- The character `n ↦ g₋ₙ` of `N` with values in `A`. -/
def sectionCharacter : Multiplicative N →* A where
  toFun n := groupLikeOf h hB (-n.toAdd)
  map_one' := by simp only [toAdd_one, neg_zero, groupLikeOf_zero]
  map_mul' m n := by simp only [toAdd_mul, neg_add, groupLikeOf_add]

/-- The algebra map `a ↦ ∑ₙ aₙ g₋ₙ`. -/
def sectionAux : A →ₐ[K] A :=
  ((AddMonoidAlgebra.lift A A N (sectionCharacter h hB)).restrictScalars K).comp (coaction π)

theorem sectionAux_of_mem {n : N} {a : A} (ha : a ∈ grade π n) :
    sectionAux h hB a = a * groupLikeOf h hB (-n) := by
  simp only [sectionAux, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    (mem_grade_iff π).mp ha, AddMonoidAlgebra.lift_single, smul_eq_mul]
  rfl

theorem sectionAux_proj (n : N) (a : A) :
    sectionAux h hB (proj π n a) = proj π n a * groupLikeOf h hB (-n) :=
  sectionAux_of_mem h hB (proj_mem π n a)

theorem sectionAux_mem_grade_zero (a : A) : sectionAux h hB a ∈ grade π 0 := by
  rw [← sum_proj π a, map_sum]
  refine Submodule.sum_mem _ fun n _ => ?_
  rw [sectionAux_proj]
  simpa using mul_mem_grade π (proj_mem π n a) (groupLikeOf_mem_grade h hB (-n))

/-- Two linear maps agreeing on all homogeneous components agree. -/
theorem eq_of_forall_proj {M : Type*} [AddCommMonoid M] [Module K M]
    (f g : A →ₗ[K] M) (hfg : ∀ n a, f (proj π n a) = g (proj π n a)) (a : A) : f a = g a := by
  rw [← sum_proj π a, map_sum, map_sum]
  exact Finset.sum_congr rfl fun n _ => hfg n a

theorem counit_sectionAux (a : A) : counit (R := K) (sectionAux h hB a) = counit (R := K) a := by
  refine eq_of_forall_proj (π := π) ((counit : A →ₗ[K] K) ∘ₗ (sectionAux h hB).toLinearMap)
    counit (fun n x => ?_) a
  change counit (R := K) (sectionAux h hB (proj π n x)) = counit (R := K) (proj π n x)
  rw [sectionAux_proj, Bialgebra.counit_mul, (groupLikeOf_isGroupLikeElem h hB (-n)).counit_eq_one,
    mul_one]

theorem comul_sectionAux (a : A) :
    comul (R := K) (sectionAux h hB a) =
      TensorProduct.map (sectionAux h hB).toLinearMap (sectionAux h hB).toLinearMap
        (comul (R := K) a) := by
  refine eq_of_forall_proj (π := π) ((comul : A →ₗ[K] A ⊗[K] A) ∘ₗ (sectionAux h hB).toLinearMap)
    (TensorProduct.map (sectionAux h hB).toLinearMap (sectionAux h hB).toLinearMap ∘ₗ comul)
    (fun n x => ?_) a
  change comul (R := K) (sectionAux h hB (proj π n x)) =
    TensorProduct.map (sectionAux h hB).toLinearMap (sectionAux h hB).toLinearMap
      (comul (R := K) (proj π n x))
  set g := groupLikeOf h hB (-n)
  have hg := groupLikeOf_isGroupLikeElem h hB (-n)
  have hcomp : (sectionAux h hB).toLinearMap ∘ₗ proj π n =
      LinearMap.mulRight K g ∘ₗ proj π n := by
    ext y
    exact sectionAux_proj h hB n y
  have key : ∀ t : A ⊗[K] A,
      TensorProduct.map (sectionAux h hB).toLinearMap (sectionAux h hB).toLinearMap
          (TensorProduct.map (proj π n) (proj π n) t) =
        TensorProduct.map (proj π n) (proj π n) t * (g ⊗ₜ[K] g) := by
    intro t
    rw [← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp, hcomp]
    induction t using TensorProduct.inductionOn with
    | tmul y z =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mulRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => rw [map_add, map_add, hy, hz, add_mul]
  have hmem := proj_mem π n x
  rw [sectionAux_proj, Bialgebra.comul_mul, hg.comul_eq_tmul_self,
    h.isCentral.comul_of_mem hmem, key]

/-- The section `σ : A → B` as an algebra map: `σ a = φ⁻¹ (∑ₙ aₙ g₋ₙ)`. -/
def sectionAlgHom : A →ₐ[K] B :=
  (AlgEquiv.ofInjective (φ : B →ₐ[K] A) h.injective).symm.toAlgHom.comp
    ((sectionAux h hB).codRestrict (φ : B →ₐ[K] A).range fun a => by
      obtain ⟨b, hb⟩ := h.invariants _ (sectionAux_mem_grade_zero h hB a)
      exact ⟨b, hb⟩)

theorem map_sectionAlgHom (a : A) : φ (sectionAlgHom h hB a) = sectionAux h hB a := by
  let e := AlgEquiv.ofInjective (φ : B →ₐ[K] A) h.injective
  have he : ∀ x : (φ : B →ₐ[K] A).range, φ (e.symm x) = (x : A) := fun x =>
    congrArg Subtype.val (e.apply_symm_apply x)
  exact he _

/-- **The section.** Dividing each homogeneous component by its group-like element is a
bialgebra map `σ : A → B` with `σ ∘ φ = id`. -/
def sectionBialgHom : A →ₐc[K] B :=
  BialgHom.ofAlgHom (sectionAlgHom h hB)
    (by
      ext a
      change counit (R := K) (sectionAlgHom h hB a) = counit (R := K) a
      rw [← CoalgHomClass.counit_comp_apply φ, map_sectionAlgHom, counit_sectionAux])
    (by
      ext a
      apply map_map_injective h
      change Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A)
          (Algebra.TensorProduct.map (sectionAlgHom h hB) (sectionAlgHom h hB) (comul a)) =
        Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A)
          (comul (R := K) (sectionAlgHom h hB a))
      have e1 : ∀ t : A ⊗[K] A,
          Algebra.TensorProduct.map (φ : B →ₐ[K] A) (φ : B →ₐ[K] A)
            (Algebra.TensorProduct.map (sectionAlgHom h hB) (sectionAlgHom h hB) t) =
          TensorProduct.map (sectionAux h hB).toLinearMap (sectionAux h hB).toLinearMap t := by
        intro t
        induction t using TensorProduct.inductionOn with
        | tmul x y =>
          simp only [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul,
            BialgHom.coe_toAlgHom, map_sectionAlgHom, AlgHom.toLinearMap_apply]
        | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
      rw [e1, ← comul_sectionAux, ← map_sectionAlgHom h hB a]
      exact (CoalgHomClass.map_comp_comul_apply φ (sectionAlgHom h hB a)).symm)

theorem sectionBialgHom_apply (a : A) : sectionBialgHom h hB a = sectionAlgHom h hB a :=
  rfl

theorem sectionBialgHom_map (b : B) : sectionBialgHom h hB (φ b) = b := by
  apply h.injective
  rw [sectionBialgHom_apply, map_sectionAlgHom,
    sectionAux_of_mem h hB (map_mem_grade_zero h.comp_eq b), neg_zero, groupLikeOf_zero, mul_one]

end Section

/-- **Sections of central extensions.** Let `φ : B → A` and `π : A → K[N]` be the Hopf algebra
data of a central extension `1 → D(N) → Spec A → Spec B → 1`. If the Picard group of `B` is
trivial and every unit of `B ⊗ B` is a scalar, then there is a bialgebra map `σ : A → B` with
`σ ∘ φ = id`. -/
theorem exists_section [Subsingleton (CommRing.Pic B)] (h : IsCentralExtension φ π)
    (hB : ∀ f : B ⊗[K] B, IsUnit f → ∃ c : K, f = algebraMap K _ c) :
    ∃ σ : A →ₐc[K] B, ∀ b, σ (φ b) = b :=
  ⟨sectionBialgHom h hB, sectionBialgHom_map h hB⟩

/-! ### Polynomial quotient algebras -/

section Polynomial

omit [HopfAlgebra K B] in
/-- A `K`-algebra isomorphic to a polynomial ring over `K` has trivial Picard group. -/
theorem subsingleton_pic_of_algEquiv [Algebra K B] {ι : Type*} (e : B ≃ₐ[K] MvPolynomial ι K) :
    Subsingleton (CommRing.Pic B) := by
  let f : B ≃+* MvPolynomial ι K := e.toRingEquiv
  have hinj : Function.Injective (CommRing.Pic.mapRingHom (f : B →+* MvPolynomial ι K)) := by
    intro x y hxy
    have hxy' := congrArg (CommRing.Pic.mapRingHom (f.symm : MvPolynomial ι K →+* B)) hxy
    have hid : (f.symm : MvPolynomial ι K →+* B).comp (f : B →+* MvPolynomial ι K) =
        RingHom.id B := by
      ext b
      simp
    rwa [CommRing.Pic.mapRingHom_mapRingHom, CommRing.Pic.mapRingHom_mapRingHom,
      hid, CommRing.Pic.mapRingHom_id_apply,
      CommRing.Pic.mapRingHom_id_apply] at hxy'
  exact hinj.subsingleton

omit [HopfAlgebra K B] in
/-- If `B` is a polynomial ring over `K`, every unit of `B ⊗ B` is a scalar. -/
theorem exists_eq_algebraMap_of_isUnit_tensor [Algebra K B] {ι : Type*}
    (e : B ≃ₐ[K] MvPolynomial ι K) (f : B ⊗[K] B) (hf : IsUnit f) :
    ∃ c : K, f = algebraMap K _ c := by
  let E : B ⊗[K] B ≃ₐ[K] MvPolynomial (ι ⊕ ι) K :=
    (Algebra.TensorProduct.congr e e).trans (MvPolynomial.tensorEquivSum K ι ι K)
  have h1 : IsUnit (E f) := hf.map E
  obtain ⟨r, -, hr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h1
  refine ⟨r, E.injective ?_⟩
  rw [hr, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]

/-- **Sections over a polynomial quotient.** If the quotient Hopf algebra `B` is isomorphic, as a
`K`-algebra, to a polynomial ring over `K`, then the central extension has a section: a
bialgebra map `σ : A → B` with `σ ∘ φ = id`. -/
theorem exists_section_of_algEquiv {ι : Type*} (e : B ≃ₐ[K] MvPolynomial ι K)
    (h : IsCentralExtension φ π) : ∃ σ : A →ₐc[K] B, ∀ b, σ (φ b) = b := by
  have := subsingleton_pic_of_algEquiv e
  exact exists_section h (exists_eq_algebraMap_of_isUnit_tensor e)

end Polynomial

end Langlands.CentralExtensionSectionHopf
