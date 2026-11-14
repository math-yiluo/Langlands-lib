import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationGraded
import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationTranslate
import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationPsi
import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationQuotient
import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationChoice
import Langlands.GroupScheme.IntegralModel.Smoothening.Smoothness
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # A Hopf algebra with torsion-free cotangent module is smooth

Let `R` be a discrete valuation ring with fraction field `K` and algebraically closed residue field
`k`. Let `C` be a flat finitely generated commutative Hopf algebra over `R` whose generic fibre is
formally smooth. Suppose the cotangent module `T = I / I²` of the counit is torsion-free. Then `C` is
smooth over `R`.

The generic fibre is given as a formally smooth `K`-algebra `E` with an injective map `ι : C → E`
such that every element of `E` has a nonzero multiple in the image, and a `K`-point of `E`
extending the counit.

The proof does not use dimension theory.

1. `T` is free, with basis the classes of some `x i ∈ I`.
2. Formal smoothness of `E` shows that no nonzero homogeneous form of degree `n` in the `x i`
   lies in `I ^ (n + 1)`.
3. Hence every square-zero element of the special fibre `k ⊗ C` lies in every power of its
   augmentation ideal, so `k ⊗ C` is reduced by translation.
4. A reduced Hopf algebra over `k` is smooth, and the fibrewise criterion gives smoothness of `C`. -/

noncomputable section

universe u

open scoped TensorProduct
open IsLocalRing Coalgebra Bialgebra HopfAlgebra MvPolynomial

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type u} [CommRing R] [IsDomain R] {K : Type u} [Field K] [Algebra R K]
  [IsFractionRing R K]

section Cotangent

variable {C : Type u} [CommRing C] [Algebra R C] (ε : C →ₐ[R] R)

omit [IsDomain R] in
theorem mem_sq_of_dif_eq_zero {y : C} (hy : y ∈ augIdeal ε) (h : dif ε y = 0) :
    y ∈ augIdeal ε ^ 2 := by
  rw [dif_of_mem ε hy, Ideal.toCotangent_eq_zero] at h
  exact h

/-- Torsion-freeness of the cotangent module in terms of ideals. -/
theorem mem_sq_of_smul_mem_sq (htors : Submodule.torsion R (Cot ε) = ⊥) {s : R} (hs : s ≠ 0)
    {c : C} (hc : c ∈ augIdeal ε) (h : s • c ∈ augIdeal ε ^ 2) : c ∈ augIdeal ε ^ 2 := by
  refine mem_sq_of_dif_eq_zero ε hc ?_
  have h1 : dif ε c ∈ Submodule.torsion R (Cot ε) := by
    refine (Submodule.mem_torsion_iff _).mpr ⟨⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩, ?_⟩
    change s • dif ε c = 0
    rw [← map_smul]
    exact dif_eq_zero_of_mem_sq ε h
  rw [htors] at h1
  exact h1

end Cotangent

section Generic

variable {C : Type u} [CommRing C] [Algebra R C] (ε : C →ₐ[R] R)
  {E : Type u} [CommRing E] [Algebra R E] [Algebra K E] [IsScalarTower R K E]
  (ι : C →ₐ[R] E) (eE : E →ₐ[K] K)

/-- The elements of `E` with a nonzero multiple in the image of `I²`. -/
def satSq (hloc : ∀ e : E, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c) : Ideal E where
  carrier := {e | ∃ s : R, s ≠ 0 ∧ ∃ c ∈ augIdeal ε ^ 2, s • e = ι c}
  zero_mem' := ⟨1, one_ne_zero, 0, Ideal.zero_mem _, by simp⟩
  add_mem' := by
    rintro e e' ⟨s, hs, c, hc, he⟩ ⟨s', hs', c', hc', he'⟩
    refine ⟨s * s', mul_ne_zero hs hs', s' • c + s • c',
      Ideal.add_mem _ (Submodule.smul_of_tower_mem _ s' hc) (Submodule.smul_of_tower_mem _ s hc'),
      ?_⟩
    rw [map_add, map_smul, map_smul, ← he, ← he', smul_add, smul_smul, smul_smul, mul_comm s' s]
  smul_mem' := by
    rintro a e ⟨s, hs, c, hc, he⟩
    obtain ⟨t, ht, b, hb⟩ := hloc a
    refine ⟨t * s, mul_ne_zero ht hs, b * c, Ideal.mul_mem_left _ _ hc, ?_⟩
    rw [smul_eq_mul, map_mul, ← hb, ← he, smul_mul_smul_comm]

/-- The map from the base change of `C` to `E`. -/
def genericLift : K ⊗[R] C →ₐ[K] E :=
  Algebra.TensorProduct.lift (Algebra.ofId K E) ι fun _ _ => .all _ _

variable {ε ι eE}

omit [IsDomain R] in
theorem mem_augIdeal_of_smul_eq (heE : ∀ c, eE (ι c) = algebraMap R K (ε c)) {w : E} {r : R}
    {c : C} (hw : w ∈ augIdeal eE) (h : r • w = ι c) : c ∈ augIdeal ε := by
  have h0 : eE (ι c) = 0 := by
    rw [← h, ← algebraMap_smul K r w, map_smul, RingHom.mem_ker.mp hw, smul_zero]
  rw [heE, map_eq_zero_iff _ (IsFractionRing.injective R K)] at h0
  exact h0

theorem sq_le_satSq (hloc : ∀ e : E, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c) (heE : ∀ c, eE (ι c) = algebraMap R K (ε c)) :
    augIdeal eE ^ 2 ≤ satSq ε ι hloc := by
  rw [sq]
  refine Ideal.mul_le.mpr fun u hu v hv => ?_
  obtain ⟨s, hs, a, ha⟩ := hloc u
  obtain ⟨t, ht, b, hb⟩ := hloc v
  refine ⟨s * t, mul_ne_zero hs ht, a * b, ?_, ?_⟩
  · rw [sq]
    exact Ideal.mul_mem_mul (mem_augIdeal_of_smul_eq heE hu ha) (mem_augIdeal_of_smul_eq heE hv hb)
  · rw [map_mul, ← ha, ← hb, smul_mul_smul_comm]

theorem exists_smul_mem_sq (hloc : ∀ e : E, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c) (hι : Function.Injective ι)
    (heE : ∀ c, eE (ι c) = algebraMap R K (ε c)) {c : C} (h : ι c ∈ augIdeal eE ^ 2) :
    ∃ s : R, s ≠ 0 ∧ s • c ∈ augIdeal ε ^ 2 := by
  obtain ⟨s, hs, c', hc', he⟩ := sq_le_satSq hloc heE h
  refine ⟨s, hs, ?_⟩
  have : s • c = c' := hι (by rw [map_smul, he])
  rw [this]
  exact hc'

/-- The differentials of the `x i` stay independent in the generic fibre. -/
theorem linearIndependent_dif_generic
    (hloc : ∀ e : E, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c) (hι : Function.Injective ι)
    (heE : ∀ c, eE (ι c) = algebraMap R K (ε c)) (htors : Submodule.torsion R (Cot ε) = ⊥)
    {d : ℕ} (x : Fin d → C) (hx : ∀ i, x i ∈ augIdeal ε)
    (hind : LinearIndependent R fun i => dif ε (x i)) :
    LinearIndependent K fun i => dif eE (ι (x i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨⟨s, hs⟩, hsg⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ g
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  choose b' hb' using fun j => hsg j (Finset.mem_univ j)
  have hxE : ∀ j, ι (x j) ∈ augIdeal eE := fun j => by
    rw [RingHom.mem_ker, heE, show ε (x j) = 0 from hx j, map_zero]
  set y : E := ∑ j, g j • ι (x j)
  have hyI : y ∈ augIdeal eE :=
    Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hxE j)
  have hy : y ∈ augIdeal eE ^ 2 := by
    refine mem_sq_of_dif_eq_zero eE hyI ?_
    rw [map_sum]
    simp only [map_smul]
    exact hg
  have hb'' : ∀ j, algebraMap R K (b' j) = s • g j := hb'
  have hsy : s • y = ι (∑ j, b' j • x j) := by
    rw [Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_assoc, ← hb'' j, algebraMap_smul, map_smul]
  have hc : ι (∑ j, b' j • x j) ∈ augIdeal eE ^ 2 := by
    rw [← hsy]
    exact Submodule.smul_of_tower_mem _ s hy
  obtain ⟨s', hs', hs'c⟩ := exists_smul_mem_sq hloc hι heE hc
  have hcI : ∑ j, b' j • x j ∈ augIdeal ε :=
    Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hx j)
  have hc2 := mem_sq_of_smul_mem_sq ε htors hs' hcI hs'c
  have hd := dif_eq_zero_of_mem_sq ε hc2
  rw [map_sum] at hd
  simp only [map_smul] at hd
  have hb0 := Fintype.linearIndependent_iff.mp hind b' hd i
  have := hb' i
  rw [hb0, map_zero, Algebra.smul_def] at this
  rcases mul_eq_zero.mp this.symm with h | h
  · exact absurd h ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0)
  · exact h

/-- **Graded independence from the generic fibre.** -/
theorem eq_zero_of_isHomogeneous [Algebra.FormallySmooth K E] [Infinite K]
    (hloc : ∀ e : E, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c) (hι : Function.Injective ι) (heE : ∀ c, eE (ι c) = algebraMap R K (ε c))
    (htors : Submodule.torsion R (Cot ε) = ⊥) {d : ℕ} (x : Fin d → C)
    (hx : ∀ i, x i ∈ augIdeal ε) (hind : LinearIndependent R fun i => dif ε (x i)) (n : ℕ)
    (Q : MvPolynomial (Fin d) R) (hQ : Q.IsHomogeneous n)
    (hQx : aeval x Q ∈ augIdeal ε ^ (n + 1)) : Q = 0 := by
  have hxE : ∀ j, ι (x j) ∈ augIdeal eE := fun j => by
    rw [RingHom.mem_ker, heE, show ε (x j) = 0 from hx j, map_zero]
  have hlin := linearIndependent_dif_generic hloc hι heE htors x hx hind
  have hP : (map (algebraMap R E) Q).IsHomogeneous n := hQ.map _
  have hmap : Ideal.map ι (augIdeal ε) ≤ augIdeal eE := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker, heE, show ε c = 0 from hc, map_zero]
  have hPx : eval (fun i => ι (x i)) (map (algebraMap R E) Q) ∈ augIdeal eE ^ (n + 1) := by
    have heq : eval (fun i => ι (x i)) (map (algebraMap R E) Q) = ι (aeval x Q) := by
      rw [eval_map, ← aeval_def, MvPolynomial.comp_aeval_apply]
    rw [heq]
    have := Ideal.mem_map_of_mem ι hQx
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hmap _ this
  refine MvPolynomial.ext _ _ fun μ => ?_
  have h := coeff_eq_zero_of_formallySmooth eE (fun i => ι (x i)) hxE hlin n _ hP hPx μ
  rw [coeff_map, IsScalarTower.algebraMap_apply R K E, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply,
    map_eq_zero_iff _ (IsFractionRing.injective R K)] at h
  rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem genericLift_bijective (hloc : ∀ e : E, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c)
    (hι : Function.Injective ι) :
    Function.Bijective (genericLift (K := K) ι) := by
  constructor
  · intro z z' hzz'
    rw [← sub_eq_zero] at hzz' ⊢
    rw [← map_sub] at hzz'
    obtain ⟨s, c, hs, hsc⟩ := exists_smul_eq_one_tmul K C (z - z')
    have hs' : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
    have hsc' : algebraMap R K s • (z - z') = (1 : K) ⊗ₜ[R] c := by
      rw [algebraMap_smul]
      exact hsc
    have hc : ι c = 0 := by
      have := congrArg (genericLift (K := K) ι) hsc'
      rw [map_smul, hzz', smul_zero, genericLift, Algebra.TensorProduct.lift_tmul, map_one,
        one_mul] at this
      exact this.symm
    rw [map_eq_zero_iff ι hι] at hc
    rw [hc, TensorProduct.tmul_zero, ← algebraMap_smul K s] at hsc
    exact (smul_eq_zero.mp hsc).resolve_left hs'
  · intro e
    obtain ⟨s, hs, c, hc⟩ := hloc e
    have hs' : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
    refine ⟨(algebraMap R K s)⁻¹ ⊗ₜ c, ?_⟩
    rw [genericLift, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, ← hc,
      ← algebraMap_smul K s e, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hs', one_smul]

end Generic

section Special

variable [IsDiscreteValuationRing R] [IsAlgClosed (ResidueField R)]

omit [IsAlgClosed (ResidueField R)] [IsFractionRing R K] in
theorem infinite_of_isDiscreteValuationRing {R₀ : Type u} [CommRing R₀] [IsDomain R₀]
    [IsDiscreteValuationRing R₀] [Algebra R₀ K] [IsFractionRing R₀ K] : Infinite K := by
  have : Infinite R₀ := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact IsDiscreteValuationRing.not_isField R₀ (Finite.isField_of_domain R₀)
  exact Infinite.of_injective _ (IsFractionRing.injective R₀ K)

variable {C : Type u} [CommRing C] [HopfAlgebra R C] [Algebra.FiniteType R C]
  {E : Type u} [CommRing E] [Algebra R E] [Algebra K E] [IsScalarTower R K E]
  [Algebra.FormallySmooth K E]

/-- **The special fibre is reduced.** -/
theorem isReduced_special_fibre (ι : C →ₐ[R] E) (hι : Function.Injective ι)
    (hloc : ∀ e : E, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c) (eE : E →ₐ[K] K)
    (heE : ∀ c, eE (ι c) = algebraMap R K (counitAlgHom R C c))
    (htors : Submodule.torsion R (Cot (counitAlgHom R C)) = ⊥) :
    _root_.IsReduced (ResidueField R ⊗[R] C) := by
  have : Infinite K := infinite_of_isDiscreteValuationRing (R₀ := R)
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  have : Module.Finite R (Cot (counitAlgHom R C)) := cot_finite _
  have : Module.IsTorsionFree R (Cot (counitAlgHom R C)) :=
    Submodule.isTorsionFree_iff_torsion_eq_bot.mpr htors
  let b := Module.finBasis R (Cot (counitAlgHom R C))
  have hsurj : ∀ t : Cot (counitAlgHom R C), ∃ y ∈ augIdeal (counitAlgHom R C),
      dif (counitAlgHom R C) y = t := fun t => by
    obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
    exact ⟨y, hy, dif_of_mem _ hy⟩
  choose x hxI hxb using fun i => hsurj (b i)
  have hspan : ∀ y ∈ augIdeal (counitAlgHom R C), ∃ r : Fin _ → R,
      y - ∑ i, r i • x i ∈ augIdeal (counitAlgHom R C) ^ 2 := by
    intro y hy
    refine ⟨b.repr (dif _ y), mem_sq_of_dif_eq_zero _ ?_ ?_⟩
    · exact Ideal.sub_mem _ hy (Ideal.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (hxI i))
    · rw [map_sub, map_sum]
      simp only [map_smul, hxb]
      rw [b.sum_repr, sub_self]
  have hlin : LinearIndependent R fun i => dif (counitAlgHom R C) (x i) := by
    simpa only [hxb] using b.linearIndependent
  have hind := eq_zero_of_isHomogeneous hloc hι heE htors x hxI hlin
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm := hϖ.maximalIdeal_eq
  have hϖm : ϖ ∈ maximalIdeal R := (mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have hmapI : Ideal.map (Algebra.TensorProduct.includeRight : C →ₐ[R] ResidueField R ⊗[R] C)
      (augIdeal (counitAlgHom R C)) ≤
      RingHom.ker (counitAlgHom (ResidueField R) (ResidueField R ⊗[R] C)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change counitAlgHom _ _ ((1 : ResidueField R) ⊗ₜ[R] y) = 0
    rw [counitAlgHom_apply, counit_eq_evPt, evPt_tmul, one_mul,
      show counitAlgHom R C y = 0 from hy, map_zero]
  apply isReduced_of_forall_sq_eq_zero (k := ResidueField R)
  intro f hf j
  obtain ⟨c, rfl⟩ := exists_one_tmul_eq f
  have hc2 : c ^ 2 ∈ Ideal.span {algebraMap R C ϖ} := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, one_tmul_eq_zero_iff, hm,
      Submodule.ideal_span_singleton_smul] at hf
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hf
    rw [← hy, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨a, ha, p, hp, rfl⟩ :=
    Submodule.mem_sup.mp (mem_sup_of_sq_mem hxI hspan hind hϖ.prime hc2 j)
  have hp0 : (1 : ResidueField R) ⊗ₜ[R] p = 0 := by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [one_tmul_eq_zero_iff, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hϖm Submodule.mem_top
  rw [TensorProduct.tmul_add, hp0, add_zero]
  have := Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight :
    C →ₐ[R] ResidueField R ⊗[R] C) ha
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hmapI j this

/-- **Lemma S.** A flat finitely generated Hopf algebra over `R` with formally smooth generic
fibre and torsion-free cotangent module is smooth. -/
theorem smooth_of_torsion_eq_bot [Module.Flat R C] (ι : C →ₐ[R] E) (hι : Function.Injective ι)
    (hloc : ∀ e : E, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c) (eE : E →ₐ[K] K)
    (heE : ∀ c, eE (ι c) = algebraMap R K (counitAlgHom R C c))
    (htors : Submodule.torsion R (Cot (counitAlgHom R C)) = ⊥) : Algebra.Smooth R C := by
  have : _root_.IsReduced (ResidueField R ⊗[R] C) :=
    isReduced_special_fibre ι hι hloc eE heE htors
  have : Algebra.Smooth (ResidueField R) (ResidueField R ⊗[R] C) :=
    smooth_of_isReduced_of_isAlgClosed _
  have : Algebra.FormallySmooth K (K ⊗[R] C) :=
    .of_equiv (AlgEquiv.ofBijective (genericLift (K := K) ι)
      (genericLift_bijective hloc hι)).symm
  exact smooth_of_smooth_fibres (K := K) C

end Special

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
