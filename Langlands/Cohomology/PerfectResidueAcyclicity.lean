import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Acyclicity of a strictly perfect complex from its reductions at maximal ideals

A strictly perfect complex (a bounded complex of finite projective modules) over a
commutative ring is acyclic as soon as its ordinary degreewise scalar extension to `R ⧸ m`
is acyclic for every maximal ideal `m`. This is a special case of Stacks, Tag 068V
(`lemma-check-perfect-pointwise`). The proof is a descending induction from the top degree
with the global Nakayama lemma, and it uses only the upper bound of the complex.
-/

universe u

open CategoryTheory
open scoped ChangeOfRings

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

variable {R : Type u} [CommRing R]

/-- Global Nakayama lemma: a finite module whose reduction modulo every maximal ideal
vanishes is zero. -/
lemma subsingleton_of_forall_maximal_mkQ_eq_zero {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ x : M, (m • (⊤ : Submodule R M)).mkQ x = 0) :
    Subsingleton M := by
  have hann : (⊤ : Submodule R M).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
      Module.Finite.fg_top (fun x _ ↦ by
        have hx := h m hm x
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx)
    have hrm : r ∈ m := hle (Submodule.mem_annihilator.2 hr)
    have h1 : (1 : R) ∈ m := by simpa using m.sub_mem hrm hr1
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  have h1 : (1 : R) ∈ (⊤ : Submodule R M).annihilator := hann ▸ Submodule.mem_top
  refine ⟨fun x y ↦ ?_⟩
  have hx := Submodule.mem_annihilator.1 h1 x Submodule.mem_top
  have hy := Submodule.mem_annihilator.1 h1 y Submodule.mem_top
  rw [one_smul] at hx hy
  rw [hx, hy]

/-- In `R ⧸ m`, multiplication by the class of `r` is the scalar action of `r`. -/
lemma mk_mul_eq_smul (m : Ideal R) (r : R) (x : R ⧸ m) : Ideal.Quotient.mk m r * x = r • x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, ← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk,
    ← Submodule.Quotient.mk_smul, smul_eq_mul]

/-- The identity of `R ⧸ m`, from the restricted-scalars module used by
`ModuleCat.extendScalars` to the standard quotient module. -/
def residueRestrictId (m : Ideal R) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk m)).obj (ModuleCat.of (R ⧸ m) (R ⧸ m)) →ₗ[R]
      R ⧸ m where
  toFun s := s
  map_add' _ _ := rfl
  map_smul' r s := mk_mul_eq_smul m r s

/-- If the image of `d : K^i ⟶ K^j` is projective, the cycles at `i` are a direct summand
of `K^i`. -/
lemma exists_retraction_ker (K : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ)
    [Module.Projective R (LinearMap.range (K.d i j).hom)] :
    ∃ π : K.X i →ₗ[R] LinearMap.ker (K.d i j).hom,
      ∀ z : LinearMap.ker (K.d i j).hom, π z = z := by
  set d := (K.d i j).hom
  obtain ⟨s, hs⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    d.surjective_rangeRestrict
  have hds : ∀ y : LinearMap.range d, d (s y) = y := fun y ↦
    congrArg Subtype.val (LinearMap.congr_fun hs y)
  refine ⟨LinearMap.codRestrict (LinearMap.ker d) (LinearMap.id - s ∘ₗ d.rangeRestrict)
    (fun x ↦ ?_), fun z ↦ ?_⟩
  · simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub, hds]
    exact sub_eq_zero.2 rfl
  · have hz : d.rangeRestrict (z : K.X i) = 0 := Subtype.ext z.2
    ext
    simp [hz]

/-- One step of the descending induction: the cycles at `k + 1` are boundaries, provided
they form a direct summand of the finite module `K^{k+1}` and every reduction of `K` at a
maximal ideal is exact at `k + 1`. -/
lemma ker_le_range_of_residue_exactAt (K : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℤ)
    [Module.Finite R (K.X (k + 1))]
    (π : K.X (k + 1) →ₗ[R] LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom)
    (hπ : ∀ z : LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom, π z = z)
    (hres : ∀ m : Ideal R, m.IsMaximal →
      ((baseChange (Ideal.Quotient.mk m)).obj K).ExactAt (k + 1)) :
    LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom ≤ LinearMap.range (K.d k (k + 1)).hom := by
  let Z := LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom
  let B : Submodule R Z := (LinearMap.range (K.d k (k + 1)).hom).comap Z.subtype
  have : Module.Finite R Z := Module.Finite.of_surjective π (fun z ↦ ⟨z, hπ z⟩)
  have : Module.Finite R (Z ⧸ B) := Module.Finite.of_surjective B.mkQ B.mkQ_surjective
  have hsub : Subsingleton (Z ⧸ B) := by
    refine subsingleton_of_forall_maximal_mkQ_eq_zero (R := R) fun m hm x ↦ ?_
    obtain ⟨z, rfl⟩ := B.mkQ_surjective x
    have hex := hres m hm
    rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 1 + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at hex
    obtain ⟨t, ht⟩ := hex ((1 : R ⧸ m) ⊗ₜ[R, Ideal.Quotient.mk m] (z : K.X (k + 1))) (by
      change (1 : R ⧸ m) ⊗ₜ[R, Ideal.Quotient.mk m] ((K.d (k + 1) (k + 1 + 1)).hom z) = 0
      rw [show (K.d (k + 1) (k + 1 + 1)).hom z = 0 from z.2, TensorProduct.tmul_zero])
    let q : K.X (k + 1) →ₗ[R] Z ⧸ B := B.mkQ ∘ₗ π
    let Φ := (TensorProduct.quotTensorEquivQuotSMul (Z ⧸ B) m).toLinearMap ∘ₗ
      TensorProduct.map (residueRestrictId m) q
    have h1 : Φ ((1 : R ⧸ m) ⊗ₜ[R, Ideal.Quotient.mk m] (z : K.X (k + 1))) =
        (m • (⊤ : Submodule R (Z ⧸ B))).mkQ (B.mkQ z) := by
      change TensorProduct.quotTensorEquivQuotSMul (Z ⧸ B) m ((1 : R ⧸ m) ⊗ₜ[R] q z) = _
      rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
      simp [q, hπ]
    have h2 : ∀ t : TensorProduct R
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk m)).obj (ModuleCat.of (R ⧸ m) (R ⧸ m)))
        (K.X k), Φ (((ModuleCat.extendScalars (Ideal.Quotient.mk m)).map (K.d k (k + 1))).hom t)
          = 0 := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul s y =>
        have hy : (K.d k (k + 1)).hom y ∈ Z := by
          change (K.d (k + 1) (k + 1 + 1)).hom ((K.d k (k + 1)).hom y) = 0
          rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
          rfl
        have hq : q ((K.d k (k + 1)).hom y) = 0 := by
          change B.mkQ (π ((K.d k (k + 1)).hom y)) = 0
          rw [show π ((K.d k (k + 1)).hom y) = ⟨_, hy⟩ from hπ ⟨_, hy⟩,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨y, rfl⟩
        change TensorProduct.quotTensorEquivQuotSMul (Z ⧸ B) m
          (residueRestrictId m s ⊗ₜ[R] q ((K.d k (k + 1)).hom y)) = 0
        rw [hq, TensorProduct.tmul_zero, map_zero]
      | add a b ha hb =>
        refine (congrArg Φ (map_add _ a b)).trans ((map_add Φ _ _).trans ?_)
        exact (congrArg₂ (· + ·) ha hb).trans (add_zero 0)
    rw [← h1]
    exact (congrArg Φ ht).symm.trans (h2 t)
  intro y hy
  have : B.mkQ ⟨y, hy⟩ = 0 := Subsingleton.elim _ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact this

/-- A strictly perfect complex over a commutative ring is acyclic once its ordinary
degreewise scalar extension to `R ⧸ m` is acyclic for every maximal ideal `m`. -/
theorem acyclic_of_isStrictlyPerfect_of_residue_acyclic
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (hres : ∀ m : Ideal R, m.IsMaximal →
      ((baseChange (Ideal.Quotient.mk m)).obj K).Acyclic) :
    K.Acyclic := by
  obtain ⟨⟨-, b, -, hb⟩, hfin⟩ := hK
  let P : ℤ → Prop := fun i ↦
    Module.Projective R (LinearMap.range (K.d i (i + 1)).hom) ∧ ∀ j, i < j → K.ExactAt j
  have base : P b := by
    refine ⟨?_, fun j hj ↦ HomologicalComplex.ExactAt.of_isZero (K.isZero_of_isStrictlyLE b j hj)⟩
    have : Subsingleton (K.X (b + 1)) :=
      ModuleCat.isZero_iff_subsingleton.1 (K.isZero_of_isStrictlyLE b (b + 1))
    infer_instance
  have step : ∀ k, P (k + 1) → P k := by
    rintro k ⟨hproj, hex⟩
    have := hproj
    have := (hfin (k + 1)).1
    have := (hfin (k + 1)).2
    obtain ⟨π, hπ⟩ := exists_retraction_ker K (k + 1) (k + 1 + 1)
    have hle := ker_le_range_of_residue_exactAt K k π hπ (fun m hm ↦ hres m hm (k + 1))
    have hrange : LinearMap.range (K.d k (k + 1)).hom =
        LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom := by
      refine le_antisymm ?_ hle
      rintro _ ⟨y, rfl⟩
      change (K.d (k + 1) (k + 1 + 1)).hom ((K.d k (k + 1)).hom y) = 0
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
      rfl
    have : Module.Projective R (LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom) :=
      Module.Projective.of_split (LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom).subtype π
        (LinearMap.ext hπ)
    refine ⟨Module.Projective.of_equiv' (LinearEquiv.ofEq _ _ hrange.symm), fun j hj ↦ ?_⟩
    rcases lt_or_eq_of_le (show k + 1 ≤ j by omega) with h | rfl
    · exact hex j h
    · rw [HomologicalComplex.exactAt_iff' K k (k + 1) (k + 1 + 1) (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_ker_sub_range]
      exact hle
  have hP : ∀ n, n ≤ b → P n := fun n hn ↦
    Int.leInductionDown (motive := fun n _ ↦ P n) base
      (fun n _ h ↦ step (n - 1) (by rwa [sub_add_cancel])) n hn
  intro j
  exact (hP (min (j - 1) b) (min_le_right _ _)).2 j (by omega)

end Langlands.Cohomology.ModuleComplex
