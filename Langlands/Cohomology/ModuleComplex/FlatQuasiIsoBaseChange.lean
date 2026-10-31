import Langlands.Cohomology.PerfectModuleComplexHomotopy
import Langlands.AnthropicFLT.P2M.Sol.S_Module_quasiIso_baseChange_of_quasiIso_of_flat
import Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_ker_of_surjective_of_flat
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Scalar extension preserves bounded-above flat quasi-isomorphisms

For a ring map `φ : R →+* S` and a quasi-isomorphism `u : K ⟶ L` of `ℤ`-indexed
cochain complexes of `R`-modules whose terms are flat and which vanish above a
common degree, the degreewise scalar extension `(baseChange φ).map u` is again a
quasi-isomorphism.

The proof passes through the mapping cone. Its terms are flat, it vanishes above
the same degree, and it is acyclic exactly when `u` is a quasi-isomorphism. For a
bounded-above acyclic complex of flat modules, descending induction shows that
all modules of cocycles are flat, and then tensoring with any module keeps the
complex acyclic. Scalar extension commutes with mapping cones.
-/

universe u

open CategoryTheory TensorProduct

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

variable {R : Type u} [CommRing R]

/-- A morphism of `ℤ`-indexed cochain complexes in an abelian category is a
quasi-isomorphism exactly when its mapping cone is acyclic. -/
lemma quasiIso_iff_exactAt_mappingCone {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (u : K ⟶ L) :
    QuasiIso u ↔ ∀ n, (CochainComplex.mappingCone u).ExactAt n := by
  have h := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished u)
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact h.trans (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt _)

section Acyclic

variable (E : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Element form of exactness of a complex of modules at degree `n + 1`. -/
lemma exists_d_eq_of_exactAt {n : ℤ} (h : E.ExactAt (n + 1)) (x : E.X (n + 1))
    (hx : (E.d (n + 1) (n + 1 + 1)).hom x = 0) : ∃ y, (E.d n (n + 1)).hom y = x := by
  rw [HomologicalComplex.exactAt_iff' E n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at h
  exact h x hx

/-- The submodule of cocycles of degree `n`, the kernel of the differential
leaving degree `n`. -/
def cocycleSubmodule (n : ℤ) : Submodule R (E.X n) :=
  LinearMap.ker (E.d n (n + 1)).hom

lemma d_d_apply (n : ℤ) (x : E.X n) :
    (E.d (n + 1) (n + 1 + 1)).hom ((E.d n (n + 1)).hom x) = 0 := by
  have h := congrArg (fun f => f.hom x) (E.d_comp_d n (n + 1) (n + 1 + 1))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at h
  exact h

/-- The differential leaving degree `n`, with codomain restricted to the cocycles
of degree `n + 1`. -/
def toCocycleSubmodule (n : ℤ) : E.X n →ₗ[R] cocycleSubmodule E (n + 1) :=
  LinearMap.codRestrict (cocycleSubmodule E (n + 1)) (E.d n (n + 1)).hom (d_d_apply E n)

lemma cocycleSubmodule_subtype_comp_toCocycleSubmodule (n : ℤ) :
    (cocycleSubmodule E (n + 1)).subtype ∘ₗ toCocycleSubmodule E n = (E.d n (n + 1)).hom :=
  LinearMap.subtype_comp_codRestrict _ _ _

lemma exact_cocycleSubmodule_subtype (n : ℤ) :
    Function.Exact (cocycleSubmodule E n).subtype (toCocycleSubmodule E n) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact Subtype.ext z.2

variable {E}

lemma toCocycleSubmodule_surjective (hE : ∀ n, E.ExactAt n) (n : ℤ) :
    Function.Surjective (toCocycleSubmodule E n) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, hy⟩ := exists_d_eq_of_exactAt E (hE (n + 1)) z hz
  exact ⟨y, Subtype.ext hy⟩

/-- In a bounded-above acyclic complex of flat modules, every module of cocycles
is flat. -/
lemma flat_cocycleSubmodule (b : ℤ) [E.IsStrictlyLE b] (hE : ∀ n, E.ExactAt n)
    (hflat : ∀ n, Module.Flat R (E.X n)) (n : ℤ) :
    Module.Flat R (cocycleSubmodule E n) := by
  have base : ∀ m, b < m → Module.Flat R (cocycleSubmodule E m) := by
    intro m hm
    have : Subsingleton (E.X m) :=
      ModuleCat.subsingleton_of_isZero (CochainComplex.isZero_of_isStrictlyLE E b m hm)
    infer_instance
  have step : ∀ m, Module.Flat R (cocycleSubmodule E (m + 1)) →
      Module.Flat R (cocycleSubmodule E m) := by
    intro m hm
    have := hflat m
    have : Module.Flat R (LinearMap.ker (toCocycleSubmodule E m)) :=
      Module.Flat.ker_of_surjective_of_flat (toCocycleSubmodule E m)
        (toCocycleSubmodule_surjective hE m)
    exact Module.Flat.of_linearEquiv
      (LinearEquiv.ofEq _ _ (LinearMap.ker_codRestrict _ _ _).symm :
        cocycleSubmodule E m ≃ₗ[R] LinearMap.ker (toCocycleSubmodule E m))
  have key : ∀ k : ℕ, Module.Flat R (cocycleSubmodule E (b + 1 - k)) := by
    intro k
    induction k with
    | zero => exact base _ (by simp)
    | succ k ih =>
      have e : b + 1 - ((k + 1 : ℕ) : ℤ) + 1 = b + 1 - k := by push_cast; ring
      have h := step (b + 1 - ((k + 1 : ℕ) : ℤ))
      rw [e] at h
      exact h ih
  by_cases hn : b < n
  · exact base n hn
  · have h := key (b + 1 - n).toNat
    rwa [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at h

/-- Tensoring a bounded-above acyclic complex of flat modules with any module
gives an acyclic complex, in element form at degree `n + 1`. -/
lemma exists_lTensor_d_eq (b : ℤ) [E.IsStrictlyLE b] (hE : ∀ n, E.ExactAt n)
    (hflat : ∀ n, Module.Flat R (E.X n)) (A : Type*) [AddCommGroup A] [Module R A] (n : ℤ)
    (x : A ⊗[R] E.X (n + 1)) (hx : (E.d (n + 1) (n + 1 + 1)).hom.lTensor A x = 0) :
    ∃ y, (E.d n (n + 1)).hom.lTensor A y = x := by
  have := flat_cocycleSubmodule b hE hflat (n + 1 + 1 + 1)
  have hinj : Function.Injective ((cocycleSubmodule E (n + 1 + 1)).subtype.lTensor A) :=
    LinearMap.lTensor_injective_of_exact_of_flat (toCocycleSubmodule E (n + 1 + 1))
      (toCocycleSubmodule_surjective hE _) _ Subtype.val_injective
      (exact_cocycleSubmodule_subtype E _) A
  have hx' : (toCocycleSubmodule E (n + 1)).lTensor A x = 0 := by
    apply hinj
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      cocycleSubmodule_subtype_comp_toCocycleSubmodule, hx, map_zero]
  obtain ⟨z, rfl⟩ := (lTensor_exact A (exact_cocycleSubmodule_subtype E (n + 1))
    (toCocycleSubmodule_surjective hE (n + 1)) x).1 hx'
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective A (toCocycleSubmodule_surjective hE n) z
  refine ⟨y, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    cocycleSubmodule_subtype_comp_toCocycleSubmodule]

end Acyclic

section BaseChange

variable {S : Type u} [CommRing S] (φ : R →+* S)

/-- Scalar extension of a bounded-above acyclic complex of flat modules is
acyclic. -/
lemma exactAt_baseChange_of_flat (E : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [E.IsStrictlyLE b] (hE : ∀ n, E.ExactAt n) (hflat : ∀ n, Module.Flat R (E.X n))
    (m : ℤ) : ((baseChange φ).obj E).ExactAt m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by ring⟩
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, hy⟩ := exists_lTensor_d_eq b hE hflat
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) n x hx
  exact ⟨y, hy⟩

/-- The mapping cone of a morphism between complexes with flat terms has flat
terms. -/
lemma flat_mappingCone_X {K L : CochainComplex (ModuleCat.{u} R) ℤ} (u : K ⟶ L)
    (hK : ∀ n, Module.Flat R (K.X n)) (hL : ∀ n, Module.Flat R (L.X n)) (n : ℤ) :
    Module.Flat R ((CochainComplex.mappingCone u).X n) := by
  have := hK (n + 1)
  have := hL n
  have : Module.Flat R (K.X (n + 1) × L.X n) :=
    P2MW.S_Module_quasiIso_baseChange_of_quasiIso_of_flat.QisoBC.flat_prod _ _
  exact Module.Flat.of_linearEquiv
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod u n (n + 1) rfl ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv)

/-- The mapping cone of a morphism between complexes vanishing above `b` vanishes
above `b`. -/
lemma mappingCone_isStrictlyLE {K L : CochainComplex (ModuleCat.{u} R) ℤ} (u : K ⟶ L)
    (b : ℤ) [K.IsStrictlyLE b] [L.IsStrictlyLE b] :
    (CochainComplex.mappingCone u).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨CochainComplex.isZero_of_isStrictlyLE K b (i + 1) (by omega),
    CochainComplex.isZero_of_isStrictlyLE L b i hi⟩

/-- Degreewise scalar extension along any ring map preserves quasi-isomorphisms
between `ℤ`-indexed complexes of flat modules vanishing above a common degree. -/
theorem quasiIso_baseChange_map_of_flat {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (u : K ⟶ L) [QuasiIso u] (b : ℤ) [K.IsStrictlyLE b] [L.IsStrictlyLE b]
    (hK : ∀ n, Module.Flat R (K.X n)) (hL : ∀ n, Module.Flat R (L.X n)) :
    QuasiIso ((baseChange φ).map u) := by
  have hE := (quasiIso_iff_exactAt_mappingCone u).1 inferInstance
  have := mappingCone_isStrictlyLE u b
  have h := exactAt_baseChange_of_flat φ (CochainComplex.mappingCone u) b hE
    (flat_mappingCone_X u hK hL)
  change QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map u)
  rw [quasiIso_iff_exactAt_mappingCone]
  intro n
  exact (h n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso u (ModuleCat.extendScalars φ))

end BaseChange

end Langlands.Cohomology.ModuleComplex
