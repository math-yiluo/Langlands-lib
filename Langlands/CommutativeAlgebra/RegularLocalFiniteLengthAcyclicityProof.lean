import Langlands.CommutativeAlgebra.RegularLocalFiniteLengthAcyclicityStatement
import Langlands.CommutativeAlgebra.RegularLocalFactorialTools
import Langlands.Algebra.ExtendScalarsTensor
import Langlands.Cohomology.AdditiveAdjunction
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Finite-length acyclicity over a regular local ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology Langlands.Cohomology.ModuleComplex
open scoped TensorProduct ChangeOfRings

namespace Langlands.CommutativeAlgebra.FiniteLengthAcyclicity

variable {R : Type u} [CommRing R]

section Quotient

variable (x : R) (C : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The scalar extension of `C` to `R ⧸ (x)`. -/
abbrev quotientComplex : CochainComplex (ModuleCat.{u} (R ⧸ Ideal.span {x})) ℤ :=
  (baseChange (algebraMap R (R ⧸ Ideal.span {x}))).obj C

/-- The scalar extension of `C` to `R ⧸ (x)`, regarded again as a complex of `R`-modules. -/
abbrev restrictedQuotientComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {x}))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (quotientComplex x C)

/-- The degreewise map `m ↦ 1 ⊗ m` from `C` to its scalar extension. -/
def quotientUnit : C ⟶ restrictedQuotientComplex x C :=
  (complexAdjunctionUnit
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R (R ⧸ Ideal.span {x})))
    (ComplexShape.up ℤ)).app C

/-- The short complex `C ⟶ C ⟶ C ⊗ R ⧸ (x)`, multiplication by `x` followed by reduction. -/
def quotientSequence : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (x • 𝟙 C) (quotientUnit x C) (by
    apply HomologicalComplex.hom_ext
    intro i
    ext m
    change ((quotientUnit x C).f i).hom (x • m) = 0
    rw [map_smul, ModuleCat.restrictScalars.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x), zero_smul]
    rfl)

end Quotient

section Degreewise

variable (x : R) (M : ModuleCat.{u} R)

/-- The comparison of scalar extension to `R ⧸ (x)` with the algebra tensor product. -/
abbrev quotientTensorEquiv :
    (ModuleCat.extendScalars (algebraMap R (R ⧸ Ideal.span {x}))).obj M ≃ₗ[R ⧸ Ideal.span {x}]
      (R ⧸ Ideal.span {x}) ⊗[R] M :=
  Langlands.Scheme.Modules.extendScalarsAlgebraEquiv (CommRingCat.of R)
    (CommRingCat.of (R ⧸ Ideal.span {x})) M

lemma unit_surjective :
    Function.Surjective
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R (R ⧸ Ideal.span {x}))).unit.app M) := by
  intro t
  obtain ⟨m, hm⟩ := TensorProduct.mk_surjective R M (R ⧸ Ideal.span {x})
    Ideal.Quotient.mk_surjective (quotientTensorEquiv x M t)
  refine ⟨m, ?_⟩
  apply (quotientTensorEquiv x M).injective
  rw [← hm]
  rfl

lemma exists_smul_eq_of_unit_eq_zero (m : M)
    (hm : (ModuleCat.extendRestrictScalarsAdj (algebraMap R (R ⧸ Ideal.span {x}))).unit.app M m
      = 0) : ∃ m' : M, x • m' = m := by
  have h1 : ((1 : R ⧸ Ideal.span {x}) ⊗ₜ[R] m : (R ⧸ Ideal.span {x}) ⊗[R] M) = 0 := by
    exact (LinearEquiv.map_eq_zero_iff (quotientTensorEquiv x M)).mpr hm
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {x})) h1
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
    Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨m', -, hm'⟩ := h2
  exact ⟨m', hm'⟩

end Degreewise

section ShortExact

variable (x : R) (C : CochainComplex (ModuleCat.{u} R) ℤ)

lemma smul_f_apply (i : ℤ) (m : C.X i) : ((x • 𝟙 C).f i).hom m = x • m := rfl

/-- Over a domain, multiplication by a nonzero `x` followed by reduction modulo `x` is a short
exact sequence of complexes of free modules. -/
theorem quotientSequence_shortExact [IsDomain R] (hx : x ≠ 0)
    (hC : ∀ i, Module.Free R (C.X i)) : (quotientSequence x C).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro m hm
    obtain ⟨m', hm'⟩ := exists_smul_eq_of_unit_eq_zero x (C.X i) m hm
    exact ⟨m', hm'⟩
  · rw [ModuleCat.mono_iff_injective]
    intro a b hab
    have hab' : x • a = x • b := hab
    have := hC i
    have : Module.IsTorsionFree R (C.X i) := inferInstance
    exact smul_right_injective (C.X i) hx hab'
  · rw [ModuleCat.epi_iff_surjective]
    exact unit_surjective x (C.X i)

end ShortExact

section LongExact

variable (x : R) (C : CochainComplex (ModuleCat.{u} R) ℤ)

lemma homologyMap_smul_id (j : ℤ) :
    HomologicalComplex.homologyMap (x • 𝟙 C) j = x • 𝟙 (C.homology j) := by
  have h1 : (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) j).map
      (x • 𝟙 C) = x • 𝟙 (C.sc j) :=
    ShortComplex.hom_ext _ _ rfl rfl rfl
  change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) j).map
        (x • 𝟙 C)) = x • 𝟙 ((C.sc j).homology)
  rw [h1, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]

/-- If the homology of the reduction vanishes in degree `j - 1`, multiplication by `x` is
injective on `Hʲ(C)`. -/
theorem smul_injective_homology (hS : (quotientSequence x C).ShortExact) (j : ℤ)
    (hz : IsZero ((restrictedQuotientComplex x C).homology (j - 1))) :
    Function.Injective (fun y : C.homology j => x • y) := by
  have hex := hS.homology_exact₁ (j - 1) j (by simp)
  have hmono := hex.mono_g (hz.eq_of_src _ _)
  have h : HomologicalComplex.homologyMap (quotientSequence x C).f j = x • 𝟙 (C.homology j) :=
    homologyMap_smul_id x C j
  change Mono (HomologicalComplex.homologyMap (quotientSequence x C).f j) at hmono
  rw [h] at hmono
  exact (ModuleCat.mono_iff_injective _).mp hmono

/-- The homology of the reduction is killed by the product of ideals killing the neighbouring
homology modules of `C`. -/
theorem mul_le_annihilator_homology (hS : (quotientSequence x C).ShortExact) (i : ℤ)
    (I₁ I₂ : Ideal R) (h₁ : I₁ ≤ Module.annihilator R (C.homology i))
    (h₂ : I₂ ≤ Module.annihilator R (C.homology (i + 1))) :
    I₁ * I₂ ≤ Module.annihilator R ((quotientSequence x C).X₃.homology i) := by
  have hex := hS.homology_exact₃ i (i + 1) (by simp)
  rw [ShortComplex.moduleCat_exact_iff] at hex
  rw [Ideal.mul_le]
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro (y : (quotientSequence x C).X₃.homology i)
  have hδ : (hS.δ i (i + 1) (by simp)).hom (b • y) = 0 := by
    rw [LinearMap.map_smul]
    exact Module.mem_annihilator.mp (h₂ hb) _
  obtain ⟨z, hz⟩ := hex (b • y) hδ
  rw [mul_smul, ← hz]
  change a • (HomologicalComplex.homologyMap (quotientSequence x C).g i).hom z = 0
  rw [← LinearMap.map_smul]
  have hz0 : a • z = 0 := Module.mem_annihilator.mp (h₁ ha) z
  rw [hz0, map_zero]

end LongExact

section QuotientProperties

variable (x : R) (C : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The homology of the restricted reduction is the restriction of the homology. -/
def restrictedQuotientHomologyIso (i : ℤ) :
    (restrictedQuotientComplex x C).homology i ≅
      (ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {x}))).obj
        ((quotientComplex x C).homology i) :=
  ((quotientComplex x C).sc i).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {x})))

lemma isZero_homology_of_neg [C.IsStrictlyGE 0] {i : ℤ} (hi : i < 0) :
    IsZero (C.homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ (C.sc i) (C.isZero_of_isStrictlyGE 0 i hi)

lemma isStrictlyGE_quotientComplex (a : ℤ) [C.IsStrictlyGE a] :
    (quotientComplex x C).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (ModuleCat.extendScalars (algebraMap R (R ⧸ Ideal.span {x}))).map_isZero
    (C.isZero_of_isStrictlyGE a i hi)

lemma isStrictlyLE_quotientComplex (b : ℤ) [C.IsStrictlyLE b] :
    (quotientComplex x C).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (ModuleCat.extendScalars (algebraMap R (R ⧸ Ideal.span {x}))).map_isZero
    (C.isZero_of_isStrictlyLE b i hi)

lemma isFiniteFree_quotientComplex (hC : IsFiniteFree C) : IsFiniteFree (quotientComplex x C) := by
  obtain ⟨⟨a, b, hga, hlb⟩, hfin⟩ := hC
  refine ⟨⟨a, b, isStrictlyGE_quotientComplex x C a, isStrictlyLE_quotientComplex x C b⟩,
    fun i => ?_⟩
  obtain ⟨hf, hfr⟩ := hfin i
  let e := quotientTensorEquiv x (C.X i)
  exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩

/-- A power of the maximal ideal of `R` killing the restriction of a module over `R ⧸ (x)`
gives the same power of the maximal ideal of `R ⧸ (x)` killing it. -/
lemma pow_le_annihilator_of_restrict [IsLocalRing R] [IsLocalRing (R ⧸ Ideal.span {x})]
    (H : ModuleCat.{u} (R ⧸ Ideal.span {x})) {N : ℕ}
    (h : maximalIdeal R ^ N ≤ Module.annihilator R
      ((ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {x}))).obj H)) :
    maximalIdeal (R ⧸ Ideal.span {x}) ^ N ≤ Module.annihilator (R ⧸ Ideal.span {x}) H := by
  have hmax : maximalIdeal (R ⧸ Ideal.span {x}) ≤
      (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) := by
    intro s hs
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    refine Ideal.mem_map_of_mem _ ?_
    by_contra hr
    exact (mem_maximalIdeal _).mp hs ((notMem_maximalIdeal.mp hr).map _)
  calc maximalIdeal (R ⧸ Ideal.span {x}) ^ N
      ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x}))) ^ N :=
        Ideal.pow_right_mono hmax N
    _ = (maximalIdeal R ^ N).map (Ideal.Quotient.mk (Ideal.span {x})) := (Ideal.map_pow _ _ _).symm
    _ ≤ Module.annihilator (R ⧸ Ideal.span {x}) H := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        rw [Ideal.mem_comap, Module.mem_annihilator]
        intro y
        exact Module.mem_annihilator.mp (h hr) y

end QuotientProperties

section Main

/-- Finite-length acyclicity below the dimension, by induction on the dimension. -/
theorem isZero_homology_of_lt_dim (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], ringKrullDim R = n →
    ∀ (C : CochainComplex (ModuleCat.{u} R) ℤ), IsFiniteFree C → C.IsStrictlyGE 0 →
      (∀ i : ℤ, ∃ N : ℕ, maximalIdeal R ^ N ≤ Module.annihilator R (C.homology i)) →
      ∀ i : ℤ, i < (n : ℤ) → IsZero (C.homology i) := by
  induction n with
  | zero =>
    intro R _ _ _ C _ hGE _ i hi
    exact isZero_homology_of_neg C (by exact_mod_cast hi)
  | succ n ih =>
    intro R _ _ hdim C hC hGE htor i hi
    have : IsDomain R := regularLocalDomain R inferInstance
    have hsf : (maximalIdeal R).spanFinrank = n + 1 := by
      have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
      rw [hdim] at h
      exact_mod_cast h
    obtain ⟨x, hxm, hx2, hxp⟩ :=
      RegularLocalFactorial.exists_prime_parameter (R := R) (by omega)
    have hx0 : x ≠ 0 := hxp.ne_zero
    have : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
      RegularLocalFactorial.isRegularLocalRing_quotient_span_singleton hxm hx2
    have hdimS : ringKrullDim (R ⧸ Ideal.span {x}) = n := by
      have h1 := RegularLocalFactorial.spanFinrank_quotient_add_one hxm hx2
      have h2 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = n := by omega
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, h2]
    have hS := quotientSequence_shortExact x C hx0 (fun i => (hC.2 i).2)
    have htorS : ∀ i : ℤ, ∃ N : ℕ, maximalIdeal (R ⧸ Ideal.span {x}) ^ N ≤
        Module.annihilator (R ⧸ Ideal.span {x}) ((quotientComplex x C).homology i) := by
      intro i
      obtain ⟨N₁, h₁⟩ := htor i
      obtain ⟨N₂, h₂⟩ := htor (i + 1)
      refine ⟨N₁ + N₂, pow_le_annihilator_of_restrict x _ ?_⟩
      have h := mul_le_annihilator_homology x C hS i _ _ h₁ h₂
      have heq : Module.annihilator R ((quotientSequence x C).X₃.homology i) =
          Module.annihilator R ((ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {x}))).obj
            ((quotientComplex x C).homology i)) :=
        (restrictedQuotientHomologyIso x C i).toLinearEquiv.annihilator_eq
      rw [heq] at h
      rw [pow_add]
      exact h
    have hGES := isStrictlyGE_quotientComplex x C 0
    have hvanS := ih (R ⧸ Ideal.span {x}) hdimS (quotientComplex x C)
      (isFiniteFree_quotientComplex x C hC) hGES htorS
    have hinj := smul_injective_homology x C hS i
      (IsZero.of_iso ((ModuleCat.restrictScalars _).map_isZero
        (hvanS (i - 1) (by push_cast at hi; omega))) (restrictedQuotientHomologyIso x C (i - 1)))
    obtain ⟨N, hN⟩ := htor i
    have hk : ∀ k : ℕ, ∀ y : C.homology i, x ^ k • y = 0 → y = 0 := by
      intro k
      induction k with
      | zero => intro y h; simpa using h
      | succ k ihk =>
        intro y h
        apply ihk
        apply hinj
        change x • (x ^ k • y) = x • 0
        rw [smul_zero, ← mul_smul, ← pow_succ']
        exact h
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun y z => ?_⟩
    rw [hk N y (Module.mem_annihilator.mp (hN (Ideal.pow_mem_pow hxm N)) y),
      hk N z (Module.mem_annihilator.mp (hN (Ideal.pow_mem_pow hxm N)) z)]

end Main

end Langlands.CommutativeAlgebra.FiniteLengthAcyclicity

namespace Langlands.CommutativeAlgebra

/-- A bounded finite free complex in nonnegative degrees over a regular local ring of
dimension `g`, whose homology modules are killed by powers of the maximal ideal, has vanishing
homology below degree `g`. -/
theorem regularLocalFiniteLengthAcyclicity : RegularLocalFiniteLengthAcyclicityStatement.{u} := by
  intro R _ _ g hg C hC hGE htor i hi
  exact FiniteLengthAcyclicity.isZero_homology_of_lt_dim g R hg C hC hGE htor i hi

end Langlands.CommutativeAlgebra
