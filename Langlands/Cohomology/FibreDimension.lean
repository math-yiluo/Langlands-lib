import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Langlands.Cohomology.PerfectModuleComplex

/-! # Fibre dimensions of modules and of base-changed complexes

Fibre dimensions `dim_{κ(p)} κ(p) ⊗_R M`, their upper semicontinuity and invariance under field
extension, and the resulting formulas for the dimensions of the homology of `K ⊗_R k` for a
complex `K` of finite (projective) modules: upper semicontinuity and local constancy of the Euler
characteristic. -/

universe u v

open TensorProduct

namespace Langlands.Cohomology.FibreDimension

variable {R : Type u} [CommRing R]

/-- The fibre dimension `dim_{κ(p)} κ(p) ⊗_R M` of a module at a prime. -/
noncomputable def fibreDim (M : Type v) [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    ℕ :=
  Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- For a finite module the fibre dimension is upper semicontinuous. -/
theorem isOpen_setOf_fibreDim_le [Module.Finite R M] (d : ℕ) :
    IsOpen {p : PrimeSpectrum R | fibreDim M p ≤ d} := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  let κ := p.asIdeal.ResidueField
  let S : Set (κ ⊗[R] M) := Set.range fun m : M ↦ (1 : κ) ⊗ₜ[R] m
  have hS : Submodule.span κ S = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    induction z with
    | tmul a m =>
      have : a ⊗ₜ[R] m = a • ((1 : κ) ⊗ₜ[R] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    | add x y hx hy => exact add_mem hx hy
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent κ S
  have hTfin : T.Finite := hTli.setFinite
  have : Fintype T := hTfin.fintype
  choose x hx using fun t : T ↦ hTS t.2
  let N : Submodule R M := Submodule.span R (Set.range x)
  -- the images of the `x t` span every fibre outside the support of `M ⧸ N`
  have key : ∀ q : PrimeSpectrum R, Subsingleton (q.asIdeal.ResidueField ⊗[R] (M ⧸ N)) →
      fibreDim M q ≤ Fintype.card T := by
    intro q hq
    let κ' := q.asIdeal.ResidueField
    have hW : Submodule.span κ' (Set.range fun t : T ↦ (1 : κ') ⊗ₜ[R] x t) = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      have hex := lTensor_exact κ' (LinearMap.exact_subtype_mkQ N)
        (Submodule.mkQ_surjective N)
      obtain ⟨w, rfl⟩ := (hex z).mp (Subsingleton.elim _ _)
      induction w with
      | tmul a n =>
        simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
        obtain ⟨n, hn⟩ := n
        induction hn using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨t, rfl⟩ := hy
          have : a ⊗ₜ[R] x t = a • ((1 : κ') ⊗ₜ[R] x t) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
        | zero => simp
        | add y y' _ _ hy hy' => rw [TensorProduct.tmul_add]; exact add_mem hy hy'
        | smul r y _ hy =>
          rw [← TensorProduct.smul_tmul, ← algebraMap_smul κ' r]
          exact Submodule.smul_mem _ _ hy
      | add w w' hw hw' => rw [map_add]; exact add_mem hw hw'
    have := finrank_range_le_card (R := κ') (fun t : T ↦ (1 : κ') ⊗ₜ[R] x t)
    rw [Set.finrank, hW, finrank_top] at this
    exact this
  have hcard : Fintype.card T = fibreDim M p := by
    have h1 := finrank_span_set_eq_card hTli
    rw [hTspan, hS, finrank_top, Set.toFinset_card] at h1
    exact h1.symm
  have hQp : Subsingleton (κ ⊗[R] (M ⧸ N)) := by
    have hker : ∀ z : κ ⊗[R] M, LinearMap.baseChange κ N.mkQ z = 0 := by
      intro z
      have hz : z ∈ Submodule.span κ T := by rw [hTspan, hS]; trivial
      induction hz using Submodule.span_induction with
      | mem y hy =>
        have hy' : (1 : κ) ⊗ₜ[R] x ⟨y, hy⟩ = y := hx ⟨y, hy⟩
        rw [← hy']
        simp only [LinearMap.baseChange_tmul, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩),
          TensorProduct.tmul_zero]
      | zero => simp
      | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
      | smul a y _ hy => rw [map_smul, hy, smul_zero]
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨a', rfl⟩ := LinearMap.lTensor_surjective κ (Submodule.mkQ_surjective N) a
    obtain ⟨b', rfl⟩ := LinearMap.lTensor_surjective κ (Submodule.mkQ_surjective N) b
    have ha := hker a'
    have hb := hker b'
    rw [LinearMap.baseChange_eq_ltensor] at ha hb
    rw [ha, hb]
  refine ⟨(Module.support R (M ⧸ N))ᶜ, fun q hq ↦ ?_, (Module.isClosed_support (M := M ⧸ N)).isOpen_compl, ?_⟩
  · have hq' : Subsingleton (q.asIdeal.ResidueField ⊗[R] (M ⧸ N)) := by
      rw [← not_nontrivial_iff_subsingleton,
        ← Module.mem_support_iff_nontrivial_residueField_tensorProduct]
      exact hq
    have := key q hq'
    rw [hcard] at this
    exact this.trans hp
  · rw [Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
    exact hQp

/-- The prime of `R` given by the kernel of a ring map to a field. -/
def kerPrime {k : Type*} [Field k] (φ : R →+* k) : PrimeSpectrum R :=
  ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩

/-- The dimension of the base change of a module along any ring map to a field only depends on
the kernel: it is the fibre dimension at that prime. -/
theorem finrank_tensor_eq_fibreDim {k : Type v} [Field k] (φ : R →+* k) :
    letI := φ.toAlgebra
    Module.finrank k (k ⊗[R] M) = fibreDim M (kerPrime φ) := by
  let := φ.toAlgebra
  let p := (kerPrime φ).asIdeal
  let ψ : p.ResidueField →+* k := Ideal.ResidueField.lift p φ le_rfl (fun x hx ↦ by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact hx)
  let := ψ.toAlgebra
  have : IsScalarTower R p.ResidueField k := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change φ r = ψ (algebraMap R p.ResidueField r)
    exact (Ideal.ResidueField.lift_algebraMap p φ le_rfl _ r).symm
  rw [← (AlgebraTensorModule.cancelBaseChange R p.ResidueField k k M).finrank_eq,
    Module.finrank_baseChange]
  rfl

/-- The fibre dimension of a finite projective module is locally constant. -/
theorem isLocallyConstant_fibreDim [Module.Finite R M] [Module.Projective R M] :
    IsLocallyConstant (fibreDim (R := R) M) := by
  have := Module.finitePresentation_of_projective R M
  convert Module.isLocallyConstant_rankAtStalk (R := R) (M := M) using 1
  funext p
  rw [Module.rankAtStalk_eq]
  rfl

/-- Dimension count for a short complex of vector spaces: `dim H + rk f + rk g = dim X₂`. -/
theorem finrank_homology_add {k : Type v} [Field k] (S : CategoryTheory.ShortComplex (ModuleCat.{v} k))
    [FiniteDimensional k S.X₂] :
    Module.finrank k S.homology + Module.finrank k (LinearMap.range S.f.hom) +
      Module.finrank k (LinearMap.range S.g.hom) = Module.finrank k S.X₂ := by
  rw [(S.moduleCatHomologyIso).toLinearEquiv.finrank_eq]
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have h2 := LinearMap.finrank_range_add_finrank_ker S.g.hom
  have h3 : Module.finrank k (LinearMap.range S.moduleCatToCycles) =
      Module.finrank k (LinearMap.range S.f.hom) := by
    have : LinearMap.range S.f.hom =
        (LinearMap.range S.moduleCatToCycles).map (LinearMap.ker S.g.hom).subtype := by
      rw [← LinearMap.range_comp]
      rfl
    rw [this, Submodule.finrank_map_subtype_eq]
  change Module.finrank k (↥(LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles) + _ + _ = _
  omega

section BaseChange

variable {k : Type v} [Field k] [Algebra R k]

lemma finrank_tensor_eq_fibreDim' (N : Type v) [AddCommGroup N] [Module R N] :
    Module.finrank k (k ⊗[R] N) = fibreDim N (kerPrime (algebraMap R k)) := by
  let p := (kerPrime (algebraMap R k)).asIdeal
  let ψ : p.ResidueField →+* k := Ideal.ResidueField.lift p (algebraMap R k) le_rfl (fun x hx ↦ by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact hx)
  let := ψ.toAlgebra
  have : IsScalarTower R p.ResidueField k := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R k r = ψ (algebraMap R p.ResidueField r)
    exact (Ideal.ResidueField.lift_algebraMap p (algebraMap R k) le_rfl _ r).symm
  rw [← (AlgebraTensorModule.cancelBaseChange R p.ResidueField k k N).finrank_eq,
    Module.finrank_baseChange]
  rfl

/-- The rank of a base-changed map, in terms of the fibre dimension of its cokernel. -/
theorem finrank_range_baseChange_add {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (d : M →ₗ[R] N) :
    Module.finrank k (LinearMap.range (d.baseChange k)) +
        fibreDim (N ⧸ LinearMap.range d) (kerPrime (algebraMap R k)) =
      Module.finrank k (k ⊗[R] N) := by
  let π := (LinearMap.range d).mkQ
  have hex := lTensor_exact k (LinearMap.exact_map_mkQ_range d) (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker (π.baseChange k) = LinearMap.range (d.baseChange k) := by
    ext z
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    exact hex z
  have hrange : LinearMap.range (π.baseChange k) = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact LinearMap.lTensor_surjective k (Submodule.mkQ_surjective _)
  have h := LinearMap.finrank_range_add_finrank_ker (π.baseChange k)
  rw [hker, hrange, finrank_top, finrank_tensor_eq_fibreDim' (k := k) (N ⧸ LinearMap.range d)] at h
  omega

end BaseChange

section Complex

open CategoryTheory CategoryTheory.Limits

/-- Telescoping of an alternating sum of consecutive pairs. -/
lemma sum_range_negOnePow_mul_add (x : ℕ → ℤ) (N : ℕ) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (x i + x (i + 1)) = x 0 - (-1) ^ N * x N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

variable {k : Type u} [Field k]

/-- The rank of a differential of a cochain complex of vector spaces. -/
noncomputable abbrev rankD (C : CochainComplex (ModuleCat.{u} k) ℤ) (i j : ℤ) : ℕ :=
  Module.finrank k (LinearMap.range (C.d i j).hom)

lemma rankD_congr (C : CochainComplex (ModuleCat.{u} k) ℤ) {i j i' j' : ℤ} (hi : i = i')
    (hj : j = j') : rankD C i j = rankD C i' j' := by
  subst hi hj
  rfl

lemma rankD_eq_zero_of_isZero_src (C : CochainComplex (ModuleCat.{u} k) ℤ) {i j : ℤ}
    (h : IsZero (C.X i)) : rankD C i j = 0 := by
  rw [rankD, h.eq_of_src (C.d i j) 0, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]

lemma rankD_eq_zero_of_isZero_tgt (C : CochainComplex (ModuleCat.{u} k) ℤ) {i j : ℤ}
    (h : IsZero (C.X j)) : rankD C i j = 0 := by
  rw [rankD, h.eq_of_tgt (C.d i j) 0, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]

/-- `dim Hⁿ + rk d^{n-1} + rk dⁿ = dim Cⁿ` for a complex of vector spaces. -/
theorem finrank_homology_add_rankD (C : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ)
    [FiniteDimensional k (C.X n)] :
    Module.finrank k (C.homology n) + rankD C (n - 1) n + rankD C n (n + 1) =
      Module.finrank k (C.X n) := by
  rw [(C.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)).toLinearEquiv.finrank_eq]
  have : FiniteDimensional k (C.sc' (n - 1) n (n + 1)).X₂ := ‹_›
  exact finrank_homology_add (C.sc' (n - 1) n (n + 1))

/-- For a complex of finite-dimensional vector spaces vanishing in degrees `a - 1` and `a + N`,
the alternating sums of the dimensions of the homology and of the terms over `[a, a + N)`
agree. -/
theorem sum_negOnePow_finrank_homology (C : CochainComplex (ModuleCat.{u} k) ℤ) (a : ℤ) (N : ℕ)
    [∀ n, FiniteDimensional k (C.X n)] (ha : IsZero (C.X (a - 1))) (hb : IsZero (C.X (a + N))) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (Module.finrank k (C.homology (a + i)) : ℤ) =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (Module.finrank k (C.X (a + i)) : ℤ) := by
  let ρ : ℕ → ℤ := fun i => rankD C (a + i - 1) (a + i)
  have key : ∀ i : ℕ, (Module.finrank k (C.homology (a + i)) : ℤ) =
      Module.finrank k (C.X (a + i)) - (ρ i + ρ (i + 1)) := by
    intro i
    have h := finrank_homology_add_rankD C (a + i)
    have h' : rankD C (a + i) (a + i + 1) =
        rankD C (a + ((i + 1 : ℕ) : ℤ) - 1) (a + ((i + 1 : ℕ) : ℤ)) :=
      rankD_congr C (by push_cast; ring) (by push_cast; ring)
    simp only [ρ]
    rw [← h']
    omega
  have h0 : ρ 0 = 0 := by
    simp only [ρ, Nat.cast_zero, add_zero]
    exact_mod_cast rankD_eq_zero_of_isZero_src C ha
  have hN : ρ N = 0 := by
    simp only [ρ]
    exact_mod_cast rankD_eq_zero_of_isZero_tgt C hb
  have ht := sum_range_negOnePow_mul_add ρ N
  rw [h0, hN, mul_zero, sub_zero] at ht
  simp_rw [key, mul_sub, Finset.sum_sub_distrib, ht, sub_zero]

end Complex

section BaseChangeComplex

open CategoryTheory CategoryTheory.Limits Langlands.Cohomology.ModuleComplex

variable {k : Type u} [Field k] (K : CochainComplex (ModuleCat.{u} R) ℤ) (φ : R →+* k)

/-- The terms of the base change of a complex along `φ : R → k` have the fibre dimensions of the
terms at the kernel of `φ`. -/
lemma finrank_baseChange_X (n : ℤ) :
    Module.finrank k (((baseChange φ).obj K).X n) = fibreDim (K.X n) (kerPrime φ) :=
  finrank_tensor_eq_fibreDim (K.X n) φ

/-- The rank of a base-changed differential. -/
lemma rankD_baseChange_add (i j : ℤ) [Module.Finite R (K.X j)] :
    rankD ((baseChange φ).obj K) i j +
        fibreDim (K.X j ⧸ LinearMap.range (K.d i j).hom) (kerPrime φ) =
      fibreDim (K.X j) (kerPrime φ) := by
  let := φ.toAlgebra
  rw [← finrank_tensor_eq_fibreDim (K.X j) φ]
  exact finrank_range_baseChange_add (k := k) (K.d i j).hom

instance finiteDimensional_baseChange_X [∀ i, Module.Finite R (K.X i)] (n : ℤ) :
    FiniteDimensional k (((baseChange φ).obj K).X n) := by
  let := φ.toAlgebra
  exact Module.Finite.base_change R k (K.X n)

/-- **Dimension formula.** The dimension of `Hⁿ(K ⊗_R k)` in terms of fibre dimensions over `R`
at the kernel `P` of `φ`: `dim Hⁿ = c_{n-1}(P) + c_n(P) - e_{n+1}(P)`, where `c_m` is the fibre
dimension of the cokernel of `dᵐ` and `e_m` that of `Kᵐ`. -/
theorem finrank_homology_baseChange [∀ i, Module.Finite R (K.X i)] (n : ℤ) :
    (Module.finrank k (((baseChange φ).obj K).homology n) : ℤ) =
      fibreDim (K.X n ⧸ LinearMap.range (K.d (n - 1) n).hom) (kerPrime φ) +
        fibreDim (K.X (n + 1) ⧸ LinearMap.range (K.d n (n + 1)).hom) (kerPrime φ) -
        fibreDim (K.X (n + 1)) (kerPrime φ) := by
  have h := finrank_homology_add_rankD ((baseChange φ).obj K) n
  have h1 := rankD_baseChange_add K φ (n - 1) n
  have h2 := rankD_baseChange_add K φ n (n + 1)
  rw [finrank_baseChange_X] at h
  omega

/-- The integer `c_{n-1}(p) + c_n(p) - e_{n+1}(p)` of the dimension formula, as a function of
the prime `p`. -/
noncomputable def homologyDim (n : ℤ) (p : PrimeSpectrum R) : ℤ :=
  fibreDim (K.X n ⧸ LinearMap.range (K.d (n - 1) n).hom) p +
    fibreDim (K.X (n + 1) ⧸ LinearMap.range (K.d n (n + 1)).hom) p - fibreDim (K.X (n + 1)) p

/-- `dim_k Hⁿ(K ⊗_R k) = homologyDim K n (ker φ)`. -/
theorem finrank_homology_baseChange_eq [∀ i, Module.Finite R (K.X i)] (n : ℤ) :
    (Module.finrank k (((baseChange φ).obj K).homology n) : ℤ) =
      homologyDim K n (kerPrime φ) :=
  finrank_homology_baseChange K φ n

/-- **Upper semicontinuity.** If the terms of `K` are finite and `K^{n+1}` is projective, then
`{p | homologyDim K n p < r}` is open. -/
theorem isOpen_setOf_homologyDim_lt [∀ i, Module.Finite R (K.X i)]
    [Module.Projective R (K.X (n + 1))] (r : ℤ) :
    IsOpen {p : PrimeSpectrum R | homologyDim K n p < r} := by
  rw [isOpen_iff_forall_mem_open]
  intro p₀ hp₀
  refine ⟨{p | fibreDim (K.X n ⧸ LinearMap.range (K.d (n - 1) n).hom) p ≤
      fibreDim (K.X n ⧸ LinearMap.range (K.d (n - 1) n).hom) p₀} ∩
    {p | fibreDim (K.X (n + 1) ⧸ LinearMap.range (K.d n (n + 1)).hom) p ≤
      fibreDim (K.X (n + 1) ⧸ LinearMap.range (K.d n (n + 1)).hom) p₀} ∩
    {p | fibreDim (K.X (n + 1)) p = fibreDim (K.X (n + 1)) p₀}, ?_, ?_, ?_⟩
  · rintro p ⟨⟨h1, h2⟩, h3⟩
    simp only [Set.mem_ofPred_eq, homologyDim] at h1 h2 h3 hp₀ ⊢
    omega
  · exact ((isOpen_setOf_fibreDim_le _ _).inter (isOpen_setOf_fibreDim_le _ _)).inter
      ((isLocallyConstant_fibreDim _).isOpen_fiber _)
  · simp

/-- A finite sum of locally constant integer functions is locally constant. -/
lemma isLocallyConstant_finsetSum {X ι : Type*} [TopologicalSpace X] (s : Finset ι)
    (f : ι → X → ℤ) (h : ∀ i ∈ s, IsLocallyConstant (f i)) :
    IsLocallyConstant (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsLocallyConstant.const (0 : ℤ)
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The alternating sum of the fibre dimensions of the terms of a complex of finite projective
modules is locally constant. -/
theorem isLocallyConstant_sum_fibreDim
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)] (a : ℤ) (N : ℕ) :
    IsLocallyConstant
      (fun p : PrimeSpectrum R => ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * fibreDim (K.X (a + i)) p) :=
  isLocallyConstant_finsetSum _ _ fun i _ =>
    (isLocallyConstant_fibreDim (K.X (a + i))).comp fun d : ℕ => (-1 : ℤ) ^ i * d

/-- **Euler characteristic.** If `K` vanishes in degrees `a - 1` and `a + N`, the alternating
sum of the dimensions of `Hⁱ(K ⊗_R k)` over `[a, a + N)` is that of the fibre dimensions of the
terms at the kernel of `φ`. -/
theorem sum_negOnePow_finrank_homology_baseChange [∀ i, Module.Finite R (K.X i)] (a : ℤ) (N : ℕ)
    (ha : IsZero (K.X (a - 1))) (hb : IsZero (K.X (a + N))) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
        (Module.finrank k (((baseChange φ).obj K).homology (a + i)) : ℤ) =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * fibreDim (K.X (a + i)) (kerPrime φ) := by
  rw [sum_negOnePow_finrank_homology ((baseChange φ).obj K) a N
    ((ModuleCat.extendScalars φ).map_isZero ha) ((ModuleCat.extendScalars φ).map_isZero hb)]
  simp_rw [finrank_baseChange_X]

end BaseChangeComplex

end Langlands.Cohomology.FibreDimension
