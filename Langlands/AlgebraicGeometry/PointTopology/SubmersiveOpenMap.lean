import Langlands.RingTheory.LocalFieldDensity.ImplicitPoints
import Langlands.AlgebraicGeometry.PointTopology.Localization
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth

/-!
# Submersive and smooth algebra maps are open on points over complete fields

Let `K` be a complete nontrivially normed field and let `A → B` be a map of `K`-algebras admitting
a finite submersive presentation. Restriction of `K`-points along `A → B` is an open map in the
evaluation topologies. The proof applies the inverse function theorem to the relations of the
presentation, regarded as polynomials in the variables together with their finitely many
coefficients. Smooth algebra maps are locally standard smooth, which gives the smooth case.
-/

noncomputable section

open MvPolynomial Filter Topology

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.AlgebraicGeometry.PointManifold Langlands.RingTheory.LocalFieldDensity

namespace SubmersiveOpen

variable {K : Type*} [Field K]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra A B]
variable {ι σ : Type*}

/-- Indices of the coefficients of the relations: a relation together with one monomial in its
support. -/
abbrev CoeffIndex (P : Algebra.Presentation A B ι σ) : Type _ :=
  Σ j : σ, (P.relation j).support

/-- The coefficient of a relation at an indexed monomial. -/
def coeffVal (P : Algebra.Presentation A B ι σ) (k : CoeffIndex P) : A :=
  (P.relation k.1).coeff k.2

/-- The relation `j` with each coefficient replaced by a new variable. -/
def genericRelation (P : Algebra.Presentation A B ι σ) (j : σ) :
    MvPolynomial (CoeffIndex P ⊕ ι) K :=
  ∑ m : (P.relation j).support,
    X (Sum.inl ⟨j, m⟩) * rename Sum.inr (monomial (m : ι →₀ ℕ) (1 : K))

/-- Substitution of the actual coefficients for the coefficient variables. -/
def specialize (P : Algebra.Presentation A B ι σ) :
    MvPolynomial (CoeffIndex P ⊕ ι) K →ₐ[K] MvPolynomial ι A :=
  aeval (Sum.elim (fun k => C (coeffVal P k)) X)

theorem specialize_genericRelation (P : Algebra.Presentation A B ι σ) (j : σ) :
    specialize P (genericRelation (K := K) P j) = P.relation j := by
  classical
  have hterm : ∀ m : (P.relation j).support,
      specialize P (X (Sum.inl ⟨j, m⟩) * rename Sum.inr (monomial (m : ι →₀ ℕ) (1 : K))) =
        monomial (m : ι →₀ ℕ) ((P.relation j).coeff m) := by
    intro m
    simp only [specialize, map_mul, aeval_X, Sum.elim_inl, aeval_rename, Sum.elim_comp_inr,
      aeval_monomial, map_one, one_mul]
    rw [monomial_eq]
    rfl
  calc specialize P (genericRelation (K := K) P j)
      = ∑ m : (P.relation j).support, monomial (m : ι →₀ ℕ) ((P.relation j).coeff m) := by
        rw [genericRelation, map_sum]
        exact Finset.sum_congr rfl fun m _ => hterm m
    _ = ∑ m ∈ (P.relation j).support, monomial m ((P.relation j).coeff m) :=
        Finset.sum_coe_sort (P.relation j).support (fun m => monomial m ((P.relation j).coeff m))
    _ = P.relation j := (P.relation j).as_sum.symm

theorem specialize_pderiv (P : Algebra.Presentation A B ι σ) (i : ι)
    (p : MvPolynomial (CoeffIndex P ⊕ ι) K) :
    specialize P (pderiv (Sum.inr i) p) = pderiv i (specialize P p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [specialize]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    rw [pderiv_mul, map_add, map_mul, map_mul, hp, map_mul, pderiv_mul]
    congr 1
    rcases s with k | i'
    · simp [specialize]
    · simp only [specialize, pderiv_X, aeval_X, Sum.elim_inr, Pi.single_apply, Sum.inr.injEq]
      split_ifs <;> simp

/-- Evaluation of a polynomial in coefficient and ordinary variables, at coefficient values
coming from a point `y` of `A`, is evaluation of its specialization mapped along `y`. -/
theorem eval_elim_eq (P : Algebra.Presentation A B ι σ) (y : A →ₐ[K] K) (v : ι → K)
    (p : MvPolynomial (CoeffIndex P ⊕ ι) K) :
    eval (Sum.elim (fun k => y (coeffVal P k)) v) p =
      eval v (map (y : A →+* K) (specialize P p)) := by
  have h : (eval (Sum.elim (fun k => y (coeffVal P k)) v)) =
      ((eval v).comp (map (y : A →+* K))).comp (specialize P).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun s => ?_)
    · simp [specialize]
    · rcases s with k | i
      · simp [specialize]
      · simp [specialize]
  exact congrArg (fun g => g p) h

variable [Algebra K B] [IsScalarTower K A B]

/-- Evaluation at the coordinates of a point of `B`, after mapping along its restriction to `A`,
is the point applied to the image of the polynomial in `B`. -/
theorem eval_map_restrict (P : Algebra.Presentation A B ι σ) (x : B →ₐ[K] K)
    (q : MvPolynomial ι A) :
    eval (fun i => x (P.val i)) (map ((x.comp (IsScalarTower.toAlgHom K A B)) : A →+* K) q) =
      x (aeval P.val q) := by
  have h : (eval (fun i => x (P.val i))).comp
      (map ((x.comp (IsScalarTower.toAlgHom K A B)) : A →+* K)) =
      (x : B →+* K).comp (aeval (R := A) P.val).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp
    · simp
  exact congrArg (fun g => g q) h

/-- The `K`-algebra map `q ↦ eval v (map y q)` on polynomials over `A`. -/
def evalMap (y : A →ₐ[K] K) (v : ι → K) : MvPolynomial ι A →ₐ[K] K :=
  (aeval v).comp (mapAlgHom y)

omit [Algebra K B] [IsScalarTower K A B] in
@[simp] theorem evalMap_apply (y : A →ₐ[K] K) (v : ι → K) (q : MvPolynomial ι A) :
    evalMap y v q = eval v (map (y : A →+* K) q) := by
  simp [evalMap]

/-- A solution `v` of the relations with coefficients evaluated along `y` is a `K`-point of `B`
lying over `y`. -/
def liftPoint (P : Algebra.Presentation A B ι σ) (y : A →ₐ[K] K) (v : ι → K)
    (hv : ∀ j, eval v (map (y : A →+* K) (P.relation j)) = 0) : B →ₐ[K] K :=
  AlgHom.liftOfSurjective ((aeval (R := A) P.val).restrictScalars K) P.aeval_val_surjective
    (evalMap y v) (by
      change RingHom.ker (aeval (R := A) P.val) ≤ RingHom.ker (evalMap (K := K) y v)
      rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simpa using hv j)

theorem liftPoint_aeval (P : Algebra.Presentation A B ι σ) (y : A →ₐ[K] K) (v : ι → K)
    (hv : ∀ j, eval v (map (y : A →+* K) (P.relation j)) = 0) (q : MvPolynomial ι A) :
    liftPoint P y v hv (aeval P.val q) = eval v (map (y : A →+* K) q) := by
  have h := AlgHom.liftOfSurjective_apply ((aeval (R := A) P.val).restrictScalars K)
    P.aeval_val_surjective (evalMap y v) (by
      change RingHom.ker (aeval (R := A) P.val) ≤ RingHom.ker (evalMap (K := K) y v)
      rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simpa using hv j) q
  simpa [liftPoint] using h

theorem liftPoint_comp (P : Algebra.Presentation A B ι σ) (y : A →ₐ[K] K) (v : ι → K)
    (hv : ∀ j, eval v (map (y : A →+* K) (P.relation j)) = 0) :
    (liftPoint P y v hv).comp (IsScalarTower.toAlgHom K A B) = y := by
  ext a
  have h := liftPoint_aeval P y v hv (C a)
  rw [aeval_C, map_C, eval_C] at h
  simpa using h

theorem liftPoint_self (P : Algebra.Presentation A B ι σ) (x : B →ₐ[K] K)
    (hv : ∀ j, eval (fun i => x (P.val i))
      (map ((x.comp (IsScalarTower.toAlgHom K A B)) : A →+* K) (P.relation j)) = 0) :
    liftPoint P (x.comp (IsScalarTower.toAlgHom K A B)) (fun i => x (P.val i)) hv = x := by
  ext b
  obtain ⟨q, rfl⟩ := P.aeval_val_surjective b
  rw [liftPoint_aeval, eval_map_restrict]

section Analytic

variable {K : Type*} [NontriviallyNormedField K]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra A B]
variable {ι σ : Type*}

/-- Polynomial evaluation, with coefficients mapped along a point of `A`, depends continuously on
the point and on the values of the variables. -/
theorem continuous_eval_map (q : MvPolynomial ι A) :
    Continuous (fun p : AlgPoint K A K × (ι → K) =>
      eval p.2 (map (p.1.toAlgHom : A →+* K) q)) := by
  classical
  have h : (fun p : AlgPoint K A K × (ι → K) => eval p.2 (map (p.1.toAlgHom : A →+* K) q)) =
      fun p => ∑ d ∈ q.support, p.1 (q.coeff d) * ∏ i ∈ d.support, p.2 i ^ d i := by
    funext p
    rw [eval_map, eval₂_eq]
    rfl
  rw [h]
  refine continuous_finsetSum _ fun d _ => ?_
  refine ((AlgPoint.continuous_eval (q.coeff d)).comp continuous_fst).mul ?_
  exact continuous_finsetProd _ fun i _ => ((continuous_apply i).comp continuous_snd).pow _

variable [Algebra K B] [IsScalarTower K A B]

/-- Implicit function theorem for a submersive presentation with parameters: for coefficient
values near those of a `K`-point `x` of `B`, the relations with these coefficients have a solution
in any prescribed neighbourhood of the coordinates of `x`. -/
theorem eventually_exists_solution [CompleteSpace K] [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation A B ι σ) (x : B →ₐ[K] K) {W : Set (ι → K)}
    (hW : W ∈ 𝓝 (fun i => x (P.val i))) :
    ∀ᶠ a in 𝓝 (fun k : CoeffIndex P.toPresentation =>
        x (algebraMap A B (coeffVal P.toPresentation k))),
      ∃ v ∈ W, ∀ j, eval (Sum.elim a v) (genericRelation (K := K) P.toPresentation j) = 0 := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite σ
  set κ := CoeffIndex P.toPresentation
  set τ := FreeVar P.toPreSubmersivePresentation
  set y₀ : A →ₐ[K] K := x.comp (IsScalarTower.toAlgHom K A B)
  set v₀ : ι → K := fun i => x (P.val i)
  set a₀ : κ → K := fun k => x (algebraMap A B (coeffVal P.toPresentation k))
  set w₀ : κ ⊕ ι → K := Sum.elim a₀ v₀
  set R : σ → MvPolynomial (κ ⊕ ι) K := genericRelation P.toPresentation
  have heval₀ : ∀ p, eval w₀ p = x (aeval P.val (specialize P.toPresentation p)) := by
    intro p
    have h := eval_elim_eq P.toPresentation y₀ v₀ p
    rw [eval_map_restrict] at h
    exact h
  have hrel₀ : ∀ j, eval w₀ (R j) = 0 := fun j => by
    rw [heval₀, specialize_genericRelation, P.aeval_val_relation, map_zero]
  let Φ : (κ ⊕ ι → K) → (κ ⊕ (σ ⊕ τ) → K) := fun w =>
    Sum.elim (fun k => w (Sum.inl k))
      (Sum.elim (fun j => eval w (R j)) (fun i => w (Sum.inr (i : ι))))
  let D : (κ ⊕ ι → K) →L[K] (κ ⊕ (σ ⊕ τ) → K) :=
    ContinuousLinearMap.pi (Sum.elim (fun k => ContinuousLinearMap.proj (Sum.inl k))
      (Sum.elim (fun j => polynomialDerivative (R j) w₀)
        (fun i => ContinuousLinearMap.proj (Sum.inr (i : ι)))))
  have hD : HasStrictFDerivAt Φ D w₀ := by
    rw [hasStrictFDerivAt_pi']
    rintro (k | j | i)
    · simpa [Φ, D] using hasStrictFDerivAt_apply (𝕜 := K) (Sum.inl k) w₀
    · simpa [Φ, D] using hasStrictFDerivAt_polynomial_eval (R j) w₀
    · simpa [Φ, D] using hasStrictFDerivAt_apply (𝕜 := K) (Sum.inr (i : ι)) w₀
  have hpd : ∀ j k, eval w₀ (pderiv (Sum.inr (P.map k)) (R j)) =
      x (aeval P.val (pderiv (P.map k) (P.relation j))) := by
    intro j k
    rw [heval₀, specialize_pderiv, specialize_genericRelation]
  have hdet : (Matrix.of fun j k : σ => eval w₀ (pderiv (Sum.inr (P.map k)) (R j))).det ≠ 0 := by
    have h : (Matrix.of fun j k : σ => eval w₀ (pderiv (Sum.inr (P.map k)) (R j))) =
        (((x : B →+* K).comp (aeval (R := A) P.val).toRingHom).mapMatrix
          P.jacobiMatrix).transpose := by
      ext j k
      simp [hpd, P.jacobiMatrix_apply]
    rw [h, Matrix.det_transpose, ← RingHom.map_det]
    have hx : ((x : B →+* K).comp (aeval (R := A) P.val).toRingHom) P.jacobiMatrix.det =
        x P.jacobian := by
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_eq]
      rfl
    rw [hx]
    exact (P.jacobian_isUnit.map x).ne_zero
  have hinj : Function.Injective D := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    have hcoef : ∀ k : κ, h (Sum.inl k) = 0 := fun k => by
      simpa [D] using congrFun hh (Sum.inl k)
    have hfree : ∀ i : τ, h (Sum.inr (i : ι)) = 0 := fun i => by
      simpa [D] using congrFun hh (Sum.inr (Sum.inr i))
    have hmap : (fun k => h (Sum.inr (P.map k))) = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      ext j
      have hj := congrFun hh (Sum.inr (Sum.inl j))
      simp only [D, ContinuousLinearMap.pi_apply, Sum.elim_inr, Sum.elim_inl,
        polynomialDerivative_apply, Pi.zero_apply, Fintype.sum_sum_type, hcoef, mul_zero,
        Finset.sum_const_zero, zero_add] at hj
      rw [Pi.zero_apply, ← hj, Matrix.mulVec, dotProduct]
      refine Fintype.sum_of_injective P.map P.map_inj _ _ (fun i hi => ?_) (fun k => by simp)
      rw [hfree ⟨i, hi⟩, mul_zero]
    funext s
    rcases s with k | i
    · exact hcoef k
    · by_cases hi : i ∈ Set.range P.map
      · obtain ⟨k, rfl⟩ := hi
        exact congrFun hmap k
      · exact hfree ⟨i, hi⟩
  have hcard : Fintype.card (κ ⊕ (σ ⊕ τ)) = Fintype.card (κ ⊕ ι) := by
    exact Fintype.card_congr (Equiv.sumCongr (Equiv.refl κ)
      ((Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj) (Equiv.refl τ)).trans
        (Equiv.sumCompl (fun i => i ∈ Set.range P.map))))
  have hdim : Module.finrank K (κ ⊕ ι → K) = Module.finrank K (κ ⊕ (σ ⊕ τ) → K) := by
    simp only [Module.finrank_fintype_fun_eq_card, hcard]
  let f' : (κ ⊕ ι → K) ≃L[K] (κ ⊕ (σ ⊕ τ) → K) :=
    (LinearMap.linearEquivOfInjective D.toLinearMap hinj hdim).toContinuousLinearEquiv
  have hD' : HasStrictFDerivAt Φ (f' : (κ ⊕ ι → K) →L[K] (κ ⊕ (σ ⊕ τ) → K)) w₀ := by
    have : (f' : (κ ⊕ ι → K) →L[K] (κ ⊕ (σ ⊕ τ) → K)) = D := by
      ext h : 1
      rfl
    rw [this]
    exact hD
  have hmapnhds := hD'.map_nhds_eq_of_equiv
  have hW' : {w : κ ⊕ ι → K | (fun i => w (Sum.inr i)) ∈ W} ∈ 𝓝 w₀ := by
    have hc : Continuous (fun w : κ ⊕ ι → K => fun i => w (Sum.inr i)) :=
      continuous_pi fun i => continuous_apply _
    exact hc.continuousAt.preimage_mem_nhds hW
  let g : (κ → K) → (κ ⊕ (σ ⊕ τ) → K) := fun a =>
    Sum.elim a (Sum.elim (fun _ => 0) (fun i => v₀ i))
  have hg : Continuous g := continuous_pi fun s => by
    rcases s with k | j | i
    · exact continuous_apply k
    · exact continuous_const
    · exact continuous_const
  have hg₀ : g a₀ = Φ w₀ := by
    funext s
    rcases s with k | j | i
    · rfl
    · exact (hrel₀ j).symm
    · rfl
  have himage : Φ '' {w | (fun i => w (Sum.inr i)) ∈ W} ∈ 𝓝 (g a₀) := by
    rw [hg₀, ← hmapnhds]
    exact Filter.image_mem_map hW'
  filter_upwards [hg.continuousAt.preimage_mem_nhds himage] with a ha
  obtain ⟨w, hwW, hw⟩ := ha
  have hwa : Sum.elim a (fun i => w (Sum.inr i)) = w := by
    funext s
    rcases s with k | i
    · exact (congrFun hw (Sum.inl k)).symm
    · rfl
  refine ⟨fun i => w (Sum.inr i), hwW, fun j => ?_⟩
  rw [hwa]
  exact congrFun hw (Sum.inr (Sum.inl j))

/-- Restriction of `K`-points along an algebra map with a finite submersive presentation is an
open map. -/
theorem isOpenMap_precomp_of_submersivePresentation [CompleteSpace K] [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation A B ι σ) :
    IsOpenMap (AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A B)) := by
  classical
  rw [isOpenMap_iff_nhds_le]
  intro x S hS
  rw [Filter.mem_map] at hS
  set f := AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A B)
  let T : Set (AlgPoint K A K × (ι → K)) :=
    {p | ∀ j, eval p.2 (map (p.1.toAlgHom : A →+* K) (P.relation j)) = 0}
  let L : T → AlgPoint K B K := fun p =>
    AlgPoint.ofAlgHom (liftPoint P.toPresentation p.1.1.toAlgHom p.1.2 p.2)
  have hL : Continuous L := by
    rw [AlgPoint.continuous_iff]
    intro b
    obtain ⟨q, rfl⟩ := P.aeval_val_surjective b
    have hq : (fun p : T => L p (aeval P.val q)) =
        fun p => eval p.1.2 (map (p.1.1.toAlgHom : A →+* K) q) := by
      funext p
      exact liftPoint_aeval _ _ _ _ q
    rw [hq]
    exact (continuous_eval_map q).comp continuous_subtype_val
  have h₀ : (f x, fun i => x (P.val i)) ∈ T := fun j => by
    have h := eval_map_restrict P.toPresentation x.toAlgHom (P.relation j)
    rw [P.aeval_val_relation, map_zero] at h
    exact h
  have hLx : L ⟨_, h₀⟩ = x := liftPoint_self P.toPresentation x.toAlgHom h₀
  have hN : L ⁻¹' (f ⁻¹' S) ∈ 𝓝 (⟨_, h₀⟩ : T) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hLx]; exact hS)
  rw [nhds_subtype, Filter.mem_comap] at hN
  obtain ⟨U, hU, hUsub⟩ := hN
  rw [mem_nhds_prod_iff] at hU
  obtain ⟨U₁, hU₁, W, hW, hUW⟩ := hU
  have hsol := eventually_exists_solution P x.toAlgHom hW
  have hcont : Continuous (fun y : AlgPoint K A K =>
      fun k : CoeffIndex P.toPresentation => y (coeffVal P.toPresentation k)) :=
    continuous_pi fun k => AlgPoint.continuous_eval _
  have hev := (hcont.tendsto (f x)).eventually
    (p := fun a => ∃ v ∈ W, ∀ j,
      eval (Sum.elim a v) (genericRelation (K := K) P.toPresentation j) = 0) hsol
  filter_upwards [hU₁, hev] with y hy₁ hy
  obtain ⟨v, hvW, hv⟩ := hy
  have hvT : (y, v) ∈ T := fun j => by
    have h := eval_elim_eq P.toPresentation y.toAlgHom v (genericRelation P.toPresentation j)
    rw [specialize_genericRelation] at h
    rw [← h]
    exact hv j
  have hmem : L ⟨(y, v), hvT⟩ ∈ f ⁻¹' S := hUsub (hUW ⟨hy₁, hvW⟩)
  have hfL : f (L ⟨(y, v), hvT⟩) = y := liftPoint_comp P.toPresentation y.toAlgHom v hvT
  rw [← hfL]
  exact hmem

/-- Restriction of `K`-points along a standard smooth algebra map is an open map. -/
theorem isOpenMap_precomp_of_isStandardSmooth [CompleteSpace K] [Algebra.IsStandardSmooth A B] :
    IsOpenMap (AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A B)) := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth A B›.out
  exact isOpenMap_precomp_of_submersivePresentation P

end Analytic

section Smooth

universe u

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- Restriction of `K`-points along a smooth map of `K`-algebras is an open map. -/
theorem isOpenMap_precomp_of_smooth (φ : A →ₐ[K] B) (hφ : (φ : A →+* B).Smooth) :
    IsOpenMap (AlgPoint.precomp (S := K) φ) := by
  classical
  obtain ⟨s, hs, hst⟩ := RingHom.smooth_iff_locally_isStandardSmooth.mp hφ
  intro O hO
  have key : AlgPoint.precomp (S := K) φ '' O = ⋃ t ∈ s,
      AlgPoint.precomp (S := K) ((Algebra.algHom K B (Localization.Away t)).comp φ) ''
        (AlgPoint.precomp (S := K) (Algebra.algHom K B (Localization.Away t)) ⁻¹' O) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hunit : ∃ t ∈ s, IsUnit (x t) := by
        by_contra hne
        push Not at hne
        have hle : Ideal.span s ≤ RingHom.ker (x.toAlgHom : B →+* K) := by
          rw [Ideal.span_le]
          intro t ht
          have := hne t ht
          rw [isUnit_iff_ne_zero, not_not] at this
          exact this
        rw [hs] at hle
        have h1 : (x.toAlgHom : B →+* K) 1 = 0 :=
          RingHom.mem_ker.mp (hle (Submodule.mem_top (x := (1 : B))))
        rw [map_one] at h1
        exact one_ne_zero h1
      obtain ⟨t, ht, hxt⟩ := hunit
      have hx' : x ∈ Set.range (AlgPoint.precomp (S := K)
          (Algebra.algHom K B (Localization.Away t))) := by
        rw [AlgPoint.range_precomp_localization (R := K) (S := K) (L := Localization.Away t)
          (Submonoid.powers t)]
        exact (AlgPoint.unit_powers_iff t x).mpr hxt
      obtain ⟨p, rfl⟩ := hx'
      exact Set.mem_biUnion ht ⟨p, hx, AlgPoint.precomp_comp _ _ _⟩
    · simp only [Set.mem_iUnion]
      rintro ⟨t, _, p, hp, rfl⟩
      exact ⟨_, hp, (AlgPoint.precomp_comp _ _ _).symm⟩
  rw [key]
  refine isOpen_biUnion fun t ht => ?_
  let _ : Algebra A (Localization.Away t) :=
    ((algebraMap B (Localization.Away t)).comp (φ : A →+* B)).toAlgebra
  have : Algebra.IsStandardSmooth A (Localization.Away t) := hst t ht
  have : IsScalarTower K A (Localization.Away t) := IsScalarTower.of_algebraMap_eq fun k => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, AlgHom.coe_toRingHom, φ.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hφt : IsScalarTower.toAlgHom K A (Localization.Away t) =
      (Algebra.algHom K B (Localization.Away t)).comp φ := by
    ext a
    rfl
  rw [← hφt]
  exact isOpenMap_precomp_of_isStandardSmooth _
    ((AlgPoint.continuous_precomp _).isOpen_preimage _ hO)

end Smooth

end SubmersiveOpen

end Langlands.AlgebraicGeometry.PointTopology
