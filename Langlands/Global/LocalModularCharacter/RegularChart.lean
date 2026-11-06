import Langlands.AlgebraicGeometry.PointTopology.Localization
import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.AlgebraicGeometry.PointManifold.ZeroFibreChart
import Langlands.RingTheory.LocalFieldDensity.ImplicitPoints
import Langlands.AlgebraicGeometry.PointManifold.General.StandardSmoothNeighborhoods
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # Regular charts at points of smooth affine schemes over complete fields -/

noncomputable section

universe u

open CategoryTheory Topology Filter MvPolynomial
open _root_.AlgebraicGeometry

namespace Langlands.Global.LocalModularCharacter

open Langlands.AlgebraicGeometry.PointTopology Langlands.AlgebraicGeometry.PointManifold
open Langlands.RingTheory.LocalFieldDensity

section Polynomial

variable {F K : Type*} [Field F] [NontriviallyNormedField K] [Algebra F K]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem aeval_eq_eval_map (q : MvPolynomial ι F) (w : ι → K) :
    aeval w q = eval w (map (algebraMap F K) q) := by
  rw [aeval_def, eval₂_eq_eval_map]

/-- Evaluation of a polynomial with coefficients in `F` is strictly differentiable over `K`. -/
theorem hasStrictFDerivAt_aeval (q : MvPolynomial ι F) (w : ι → K) :
    HasStrictFDerivAt (fun y : ι → K => aeval y q)
      (polynomialDerivative (map (algebraMap F K) q) w) w := by
  simpa only [aeval_eq_eval_map] using
    hasStrictFDerivAt_polynomial_eval (map (algebraMap F K) q) w

theorem polynomialDerivative_map_apply (q : MvPolynomial ι F) (w v : ι → K) :
    polynomialDerivative (map (algebraMap F K) q) w v = ∑ i, aeval w (pderiv i q) * v i := by
  simp only [polynomialDerivative_apply, pderiv_map, aeval_eq_eval_map]

/-- Evaluation at a point of `K[ε]`: the `ε`-part is the formal derivative. -/
theorem aeval_trivSqZeroExt (q : MvPolynomial ι F) (w u : ι → K) :
    aeval (fun i => (TrivSqZeroExt.inl (w i) + TrivSqZeroExt.inr (u i) :
      TrivSqZeroExt K K)) q =
      TrivSqZeroExt.inl (aeval w q) + TrivSqZeroExt.inr (∑ i, aeval w (pderiv i q) * u i) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp [TrivSqZeroExt.algebraMap_eq_inl']
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add]
    simp only [map_add, add_mul, Finset.sum_add_distrib, TrivSqZeroExt.inl_add,
      TrivSqZeroExt.inr_add]
    abel
  | mul_X p i hp =>
    rw [map_mul, hp, aeval_X]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, smul_eq_mul, op_smul_eq_mul, add_zero, zero_add, Derivation.leibniz,
        pderiv_X, map_mul, map_add, aeval_X, mul_add, Pi.single_apply, apply_ite (aeval w),
        map_zero, mul_ite, mul_zero, mul_one, add_mul, Finset.sum_add_distrib, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_mul]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring

end Polynomial

section Presentation

variable {F K : Type*} [Field F] [NontriviallyNormedField K] [Algebra F K]
variable {A : Type*} [CommRing A] [Algebra F A] {ι σ : Type*}

/-- At a `K`-point `x` of a submersively presented algebra, a tangent vector which vanishes on
the free variables and is annihilated by the derivatives of all relations is zero. -/
theorem eq_zero_of_jacobian [Fintype ι] [Fintype σ] (P : Algebra.SubmersivePresentation F A ι σ)
    (x : A →ₐ[F] K) (u : ι → K) (hfree : ∀ i, i ∉ Set.range P.map → u i = 0)
    (hrel : ∀ j, ∑ i, aeval (fun l => x (P.val l)) (pderiv i (P.relation j)) * u i = 0) :
    u = 0 := by
  classical
  set w₀ : ι → K := fun l => x (P.val l)
  have hdet : (Matrix.of fun j k : σ =>
      aeval w₀ (pderiv (P.map k) (P.relation j))).det ≠ 0 := by
    have h : (Matrix.of fun j k : σ => aeval w₀ (pderiv (P.map k) (P.relation j))) =
        ((aeval w₀ : MvPolynomial ι F →ₐ[F] K).toRingHom.mapMatrix P.jacobiMatrix).transpose := by
      ext j k
      simp [P.jacobiMatrix_apply]
    rw [h, Matrix.det_transpose, ← RingHom.map_det]
    have hx : aeval w₀ P.jacobiMatrix.det = x P.jacobian := by
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_eq, AlgHom.coe_toRingHom,
        MvPolynomial.comp_aeval_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx]
    exact (P.jacobian_isUnit.map x).ne_zero
  have hmap : (fun k => u (P.map k)) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    ext j
    rw [Pi.zero_apply, ← hrel j, Matrix.mulVec, dotProduct]
    refine Fintype.sum_of_injective P.map P.map_inj _ _ (fun i hi => ?_) (fun k => by simp)
    rw [hfree i hi, mul_zero]
  funext i
  by_cases hi : i ∈ Set.range P.map
  · obtain ⟨k, rfl⟩ := hi
    exact congrFun hmap k
  · exact hfree i hi

/-- The values of the relations of a presentation at a point of `K^ι`. -/
def relationValues (P : Algebra.Presentation F A ι σ) (w : ι → K) : σ → K :=
  fun j => aeval w (P.relation j)

/-- A solution of the relations of a presentation is a `K`-point of the presented algebra. -/
def presentationPoint (P : Algebra.Presentation F A ι σ) (w : ι → K)
    (hw : relationValues P w = 0) : A →ₐ[F] K :=
  AlgHom.liftOfSurjective (aeval (R := F) P.val) P.aeval_val_surjective (aeval w) (by
    change RingHom.ker (aeval (R := F) P.val) ≤ RingHom.ker (aeval (R := F) w)
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact congrFun hw j)

theorem presentationPoint_aeval_val (P : Algebra.Presentation F A ι σ) (w : ι → K)
    (hw : relationValues P w = 0) (q : MvPolynomial ι F) :
    presentationPoint P w hw (aeval P.val q) = aeval w q := by
  rw [presentationPoint, AlgHom.liftOfSurjective_apply]

theorem presentationPoint_apply (P : Algebra.Presentation F A ι σ) (w : ι → K)
    (hw : relationValues P w = 0) (a : A) :
    presentationPoint P w hw a = aeval w (P.σ a) := by
  conv_lhs => rw [← P.aeval_val_σ a]
  exact presentationPoint_aeval_val P w hw _

theorem presentationPoint_val (P : Algebra.Presentation F A ι σ) (w : ι → K)
    (hw : relationValues P w = 0) (i : ι) :
    presentationPoint P w hw (P.val i) = w i := by
  rw [← aeval_X (R := F) P.val i, presentationPoint_aeval_val, aeval_X]

theorem relationValues_comp (P : Algebra.Presentation F A ι σ) (x : A →ₐ[F] K) :
    relationValues P (fun l => x (P.val l)) = 0 := by
  funext j
  rw [relationValues, ← MvPolynomial.comp_aeval_apply, P.aeval_val_relation, map_zero,
    Pi.zero_apply]

/-- The `K`-points of a presented algebra are the solutions of its relations in `K^ι`. -/
def presentationPointHomeomorph [Fintype ι] (P : Algebra.Presentation F A ι σ) :
    AlgPoint F A K ≃ₜ {w : ι → K // relationValues P w = 0} where
  toFun x := ⟨fun l => x (P.val l), relationValues_comp P x.toAlgHom⟩
  invFun w := AlgPoint.ofAlgHom (presentationPoint P w.1 w.2)
  left_inv x := by
    ext a
    rw [AlgPoint.ofAlgHom_apply, presentationPoint_apply, ← MvPolynomial.comp_aeval_apply]
    exact congrArg x.toAlgHom (P.aeval_val_σ a)
  right_inv w := Subtype.ext (funext fun i => presentationPoint_val P w.1 w.2 i)
  continuous_toFun := Continuous.subtype_mk
    (continuous_pi fun l => AlgPoint.continuous_eval (P.val l)) _
  continuous_invFun := by
    refine (AlgPoint.continuous_iff _).mpr fun a => ?_
    simp only [AlgPoint.ofAlgHom_apply, presentationPoint_apply]
    exact (continuous_iff_continuousAt.mpr fun w =>
      (hasStrictFDerivAt_aeval (P.σ a) w).continuousAt).comp continuous_subtype_val

end Presentation

section Core

variable {F K : Type*} [Field F] [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K]
variable {O A : Type*} [CommRing O] [CommRing A] [Algebra F O] [Algebra F A] [Algebra O A]
  [IsScalarTower F O A]

omit [CompleteSpace K] in
theorem derivation_map_one (x : O →ₐ[F] K) (D : O →ₗ[F] K)
    (hD : ∀ a b, D (a * b) = x a * D b + x b * D a) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, map_one x, one_mul] at h
  linear_combination -h

/-- A derivation at a point `x`, packaged as an algebra map into the dual numbers over `K`. -/
def dualNumberHom (x : O →ₐ[F] K) (D : O →ₗ[F] K)
    (hD : ∀ a b, D (a * b) = x a * D b + x b * D a) : O →ₐ[F] TrivSqZeroExt K K where
  toFun o := TrivSqZeroExt.inl (x o) + TrivSqZeroExt.inr (D o)
  map_one' := by
    rw [map_one, derivation_map_one x D hD, TrivSqZeroExt.inr_zero, add_zero,
      TrivSqZeroExt.inl_one]
  map_mul' a b := by
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, smul_eq_mul, op_smul_eq_mul, add_zero, zero_add, hD]
      ring
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one r, map_smul, map_smul, map_one x,
      derivation_map_one x D hD, smul_zero, TrivSqZeroExt.inr_zero, add_zero,
      ← Algebra.algebraMap_eq_smul_one, TrivSqZeroExt.algebraMap_eq_inl']

omit [CompleteSpace K] in
theorem dualNumberHom_apply (x : O →ₐ[F] K) (D : O →ₗ[F] K)
    (hD : ∀ a b, D (a * b) = x a * D b + x b * D a) (o : O) :
    dualNumberHom x D hD o = TrivSqZeroExt.inl (x o) + TrivSqZeroExt.inr (D o) := rfl

/-- Regular charts at points of the principal open `D(t)` of `Spec O`, whose coordinate ring
`A = O[1/t]` carries a submersive presentation. -/
theorem exists_regularChart_of_away {ι σ : Type*} [Finite ι] [Finite σ] (t : O)
    [IsLocalization.Away t A] (P : Algebra.SubmersivePresentation F A ι σ)
    (p : AlgPoint F O K) (hp : p t ≠ 0) :
    ∃ (d : ℕ) (φ : OpenPartialHomeomorph (AlgPoint F O K) (Fin d → K))
      (n : ℕ) (c : Fin n → O) (R : (Fin n → K) → (Fin d → K))
      (R' : (Fin n → K) →L[K] (Fin d → K)),
      p ∈ φ.source ∧ φ p = 0 ∧
      HasStrictFDerivAt R R' (fun j => p (c j)) ∧
      (∀ x ∈ φ.source, φ x = R (fun j => x (c j))) ∧
      (∀ a : O, ∃ L : (Fin d → K) →L[K] K, HasStrictFDerivAt (fun s => φ.symm s a) L 0) ∧
      (∀ D : O →ₗ[F] K, (∀ a b, D (a * b) = p a * D b + p b * D a) →
        R' (fun j => D (c j)) = 0 → D = 0) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite σ
  -- The point `p` is the restriction of a point `p'` of the localization `A`.
  set incl := AlgPoint.precomp (S := K) (Algebra.algHom F O A) with hincl
  have hj : IsOpenEmbedding incl := AlgPoint.isOpenEmbedding_precomp_away (R := F) (L := A) t
  obtain ⟨p', hp'⟩ : p ∈ Set.range incl := by
    rw [hincl, AlgPoint.range_precomp_localization (R := F) (L := A) (Submonoid.powers t)]
    exact (AlgPoint.unit_powers_iff t p).mpr hp.isUnit
  have hp'O (o : O) : p' (algebraMap O A o) = p o := by rw [← hp']; rfl
  -- The free variables of the presentation, indexed by `Fin d`.
  obtain ⟨d, ⟨eτ⟩⟩ : ∃ d, Nonempty (Fin d ≃ {i : ι // i ∉ Set.range P.map}) :=
    ⟨_, ⟨(Fintype.equivFin _).symm⟩⟩
  set free : Fin d → ι := fun k => (eτ k).1 with hfree_def
  have hfree_surj (i : ι) (hi : i ∉ Set.range P.map) : ∃ k, free k = i :=
    ⟨eτ.symm ⟨i, hi⟩, by simp [free]⟩
  have hcard : Fintype.card ι = d + Fintype.card σ := by
    rw [← Fintype.card_congr (Equiv.sumCompl (· ∈ Set.range P.map)), Fintype.card_sum,
      Set.card_range_of_injective P.map_inj, ← Fintype.card_congr eτ, Fintype.card_fin,
      add_comm]
  set w₀ : ι → K := fun l => p' (P.val l) with hw₀
  set b : Fin d → K := fun k => w₀ (free k) with hb
  choose m num hnum using fun k => IsLocalization.Away.surj t (P.val (free k))
  set Q : Fin d → MvPolynomial ι F := fun k => P.σ (algebraMap O A t ^ m k) with hQ_def
  have hQ (y : AlgPoint F A K) (k : Fin d) :
      aeval (fun l => y (P.val l)) (Q k) = y (algebraMap O A t) ^ m k := by
    rw [← MvPolynomial.comp_aeval_apply]
    change y.toAlgHom (aeval P.val (P.σ _)) = _
    rw [P.aeval_val_σ, map_pow]
    rfl
  have hQne (k : Fin d) : aeval w₀ (Q k) ≠ 0 := by
    rw [hQ p' k, hp'O]
    exact pow_ne_zero _ hp
  -- The ambient map: modified free coordinates together with the relations.
  let Φ : (ι → K) → (Fin d → K) × (σ → K) := fun w =>
    (fun k => (w (free k) - b k) * aeval w (Q k), relationValues P.toPresentation w)
  let Φ' : (ι → K) →L[K] (Fin d → K) × (σ → K) :=
    (ContinuousLinearMap.pi fun k => aeval w₀ (Q k) • ContinuousLinearMap.proj (free k)).prod
      (ContinuousLinearMap.pi fun j =>
        polynomialDerivative (map (algebraMap F K) (P.relation j)) w₀)
  have hΦ' : HasStrictFDerivAt Φ Φ' w₀ := by
    refine HasStrictFDerivAt.prodMk (hasStrictFDerivAt_pi.2 fun k => ?_)
      (hasStrictFDerivAt_pi.2 fun j => hasStrictFDerivAt_aeval (P.relation j) w₀)
    have h := ((hasStrictFDerivAt_apply (free k) w₀).sub_const (b k)).mul
      (hasStrictFDerivAt_aeval (Q k) w₀)
    convert h using 1
    simp [b]
  have hinj : Function.Injective Φ' := by
    refine (injective_iff_map_eq_zero Φ').mpr fun v hv => ?_
    refine eq_zero_of_jacobian P p'.toAlgHom v (fun i hi => ?_) (fun j => ?_)
    · obtain ⟨k, rfl⟩ := hfree_surj i hi
      have h := congrFun (congrArg Prod.fst hv) k
      simp only [Φ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
        smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        Prod.fst_zero, Pi.zero_apply] at h
      exact (mul_eq_zero.mp h).resolve_left (hQne k)
    · have h := congrFun (congrArg Prod.snd hv) j
      simp only [Φ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
        Prod.snd_zero, Pi.zero_apply, polynomialDerivative_map_apply] at h
      exact h
  have hbij : Function.Bijective Φ' := by
    refine ⟨hinj, ?_⟩
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Φ'.toLinearMap) ?_).mp hinj
    simp [Module.finrank_prod, hcard]
  let Φe : (ι → K) ≃L[K] (Fin d → K) × (σ → K) :=
    (LinearEquiv.ofBijective Φ'.toLinearMap hbij).toContinuousLinearEquiv
  have hΦ : HasStrictFDerivAt Φ (Φe : (ι → K) →L[K] (Fin d → K) × (σ → K)) w₀ := hΦ'
  have hΦw₀ : Φ w₀ = 0 := by
    refine Prod.ext (funext fun k => ?_) (relationValues_comp P.toPresentation p'.toAlgHom)
    simp [Φ, b]
  -- The chart.
  let e := hΦ.toOpenPartialHomeomorph Φ
  let H := presentationPointHomeomorph (K := K) P.toPresentation
  let Z := zeroFibreChart (relationValues P.toPresentation) e (fun _ _ => rfl)
    ⟨w₀, relationValues_comp P.toPresentation p'.toAlgHom⟩
  let ψ := H.transOpenPartialHomeomorph Z
  let φ := ψ.lift_openEmbedding hj
  have hsrc : p' ∈ ψ.source := hΦ.mem_toOpenPartialHomeomorph_source
  have hφj (y : AlgPoint F A K) : φ (incl y) = (Φ (fun l => y (P.val l))).1 := by
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  have hpsrc : p ∈ φ.source := ⟨p', hsrc, hp'⟩
  have hφp : φ p = 0 := by
    rw [← hp', hφj]
    exact congrArg Prod.fst hΦw₀
  -- The polynomial expression of the chart.
  let R' : (Fin (d + d) → K) →L[K] (Fin d → K) :=
    ContinuousLinearMap.pi fun k =>
      ContinuousLinearMap.proj (Fin.castAdd d k) - b k • ContinuousLinearMap.proj (Fin.natAdd d k)
  let c : Fin (d + d) → O := Fin.append num fun k => t ^ m k
  have hR'c (g : O → K) (k : Fin d) :
      R' (fun i => g (c i)) k = g (num k) - b k * g (t ^ m k) := by
    simp only [R', c, ContinuousLinearMap.pi_apply, sub_apply,
      smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Fin.append_left,
      Fin.append_right]
  refine ⟨d, φ, d + d, c, R', R', hpsrc, hφp, R'.hasStrictFDerivAt, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    rw [hφj]
    funext k
    rw [hR'c (fun z => incl y z) k]
    have h1 : incl y (num k) = y (P.val (free k)) * y (algebraMap O A t) ^ m k := by
      change y.toAlgHom (algebraMap O A (num k)) = _
      rw [← hnum k, map_mul, map_pow]
      rfl
    have h2 : incl y (t ^ m k) = y (algebraMap O A t) ^ m k := by
      change y.toAlgHom (algebraMap O A (t ^ m k)) = _
      rw [map_pow, map_pow]
      rfl
    change (y (P.val (free k)) - b k) * aeval (fun l => y (P.val l)) (Q k) = _
    rw [h1, h2, hQ y k]
    ring
  · intro o
    have h0 : (0 : Fin d → K) ∈ ψ.target := hφp ▸ φ.map_source hpsrc
    have hev : (fun s => aeval (e.symm (s, 0)) (P.σ (algebraMap O A o))) =ᶠ[𝓝 0]
        fun s => φ.symm s o := by
      filter_upwards [ψ.open_target.mem_nhds h0] with s hs
      rw [← zeroFibreChart_symm_val (relationValues P.toPresentation) e (fun _ _ => rfl)
        ⟨w₀, relationValues_comp P.toPresentation p'.toAlgHom⟩ hs]
      exact (presentationPoint_apply P.toPresentation _ (Z.symm s).2 _).symm
    have hinv := hΦ.to_localInverse
    rw [hΦw₀] at hinv
    have hpair : HasStrictFDerivAt (fun s : Fin d → K => (s, (0 : σ → K)))
        ((ContinuousLinearMap.id K (Fin d → K)).prod 0) 0 :=
      (hasStrictFDerivAt_id 0).prodMk (hasStrictFDerivAt_const 0 0)
    have hcomp := (hasStrictFDerivAt_aeval (P.σ (algebraMap O A o)) (e.symm (0, 0))).comp
      (f := fun s : Fin d → K => e.symm (s, 0)) 0 (hinv.comp (f := fun s : Fin d → K => (s, (0 : σ → K))) 0 hpair)
    exact ⟨_, hcomp.congr_of_eventuallyEq hev⟩
  · intro D hD hRD
    let δ := dualNumberHom p.toAlgHom D hD
    have hδapp (o : O) : δ o = TrivSqZeroExt.inl (p o) + TrivSqZeroExt.inr (D o) := rfl
    have hδunit : ∀ y : Submonoid.powers t, IsUnit (δ y) := by
      rintro ⟨_, n, rfl⟩
      rw [map_pow]
      refine IsUnit.pow n ?_
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hδapp, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      exact hp.isUnit
    let δ' : A →ₐ[F] TrivSqZeroExt K K := IsLocalization.liftAlgHom hδunit
    have hδ' (o : O) : δ' (algebraMap O A o) = δ o := IsLocalization.lift_eq _ o
    have hfst : (TrivSqZeroExt.fstHom F K K).comp δ' = p'.toAlgHom := by
      apply IsLocalization.algHom_ext (Submonoid.powers t)
      ext o
      change (δ' (algebraMap O A o)).fst = p' (algebraMap O A o)
      rw [hδ', hδapp, hp'O, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero]
    set u : ι → K := fun l => (δ' (P.val l)).snd with hu_def
    have hδ'val (l : ι) :
        δ' (P.val l) = TrivSqZeroExt.inl (w₀ l) + TrivSqZeroExt.inr (u l) := by
      ext
      · simpa using congrArg (fun g : A →ₐ[F] K => g (P.val l)) hfst
      · simp [u]
    have hδ'aeval (q : MvPolynomial ι F) : δ' (aeval P.val q) =
        TrivSqZeroExt.inl (aeval w₀ q) + TrivSqZeroExt.inr (∑ i, aeval w₀ (pderiv i q) * u i) := by
      rw [MvPolynomial.comp_aeval_apply]
      simp only [hδ'val]
      exact aeval_trivSqZeroExt q w₀ u
    have hu : u = 0 := by
      refine eq_zero_of_jacobian P p'.toAlgHom u (fun i hi => ?_) (fun j => ?_)
      · obtain ⟨k, rfl⟩ := hfree_surj i hi
        have h : (δ' (P.val (free k) * algebraMap O A (t ^ m k))).snd =
            (δ' (algebraMap O A (num k))).snd := by
          rw [map_pow, hnum k]
        rw [map_mul, hδ'val, hδ', hδ', hδapp, hδapp] at h
        simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
          TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.fst_inr, smul_eq_mul, op_smul_eq_mul, add_zero, zero_add] at h
        have hk := congrFun hRD k
        rw [hR'c D k, Pi.zero_apply] at hk
        have hbk : b k = w₀ (free k) := rfl
        have h2 : p (t ^ m k) * u (free k) = 0 := by
          linear_combination h + hk + D (t ^ m k) * hbk
        refine (mul_eq_zero.mp h2).resolve_left ?_
        change p.toAlgHom (t ^ m k) ≠ 0
        rw [map_pow]
        exact pow_ne_zero _ hp
      · have h := congrArg TrivSqZeroExt.snd (hδ'aeval (P.relation j))
        rw [P.aeval_val_relation, map_zero] at h
        simpa using h.symm
    ext o
    have h := congrArg TrivSqZeroExt.snd (hδ'aeval (P.σ (algebraMap O A o)))
    rw [P.aeval_val_σ, hδ', hu, hδapp] at h
    simpa using h

end Core

section Scheme

/-- The coordinate algebra of a smooth affine scheme over a field is a smooth algebra. -/
theorem smooth_affineCoordinateRing {F : Type u} [Field F] (X : Over (Spec (CommRingCat.of F)))
    [IsAffine X.left] (hX : Smooth X.hom) :
    Algebra.Smooth F (AffineCoordinateRing F X) := by
  rw [← RingHom.smooth_algebraMap]
  change (affineCoordinateMap F X).Smooth
  rw [General.affineCoordinateMap_eq_appTop]
  exact RingHom.Smooth.respectsIso.right X.hom.appTop.hom
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
    (HasRingHomProperty.appTop @Smooth X.hom hX)

/-- Regular charts at the `K`-points of a smooth affine scheme over a field `F`, for a complete
nontrivially normed field `K` over `F`. The chart `φ` is, on its source, a polynomial expression
`R` in finitely many coordinate functions `c`, strictly differentiable at the point; every
coordinate function is strictly differentiable along the inverse chart at `0`; and a derivation
at the point that is killed by the derivative of `R` vanishes. -/
theorem exists_regularChart {F : Type u} [Field F] (X : Over (Spec (CommRingCat.of F)))
    [IsAffine X.left] [LocallyOfFiniteType X.hom] (hX : Smooth X.hom)
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K]
    (p : AlgPoint F (AffineCoordinateRing F X) K) :
    ∃ (d : ℕ) (φ : OpenPartialHomeomorph (AlgPoint F (AffineCoordinateRing F X) K) (Fin d → K))
      (n : ℕ) (c : Fin n → AffineCoordinateRing F X) (R : (Fin n → K) → (Fin d → K))
      (R' : (Fin n → K) →L[K] (Fin d → K)),
      p ∈ φ.source ∧ φ p = 0 ∧
      HasStrictFDerivAt R R' (fun j => p (c j)) ∧
      (∀ x ∈ φ.source, φ x = R (fun j => x (c j))) ∧
      (∀ a : AffineCoordinateRing F X, ∃ L : (Fin d → K) →L[K] K,
          HasStrictFDerivAt (fun s => φ.symm s a) L 0) ∧
      (∀ D : AffineCoordinateRing F X →ₗ[F] K,
          (∀ a b, D (a * b) = p a * D b + p b * D a) →
          R' (fun j => D (c j)) = 0 → D = 0) := by
  have := smooth_affineCoordinateRing X hX
  obtain ⟨s, hs, hstd⟩ :=
    Algebra.Smooth.exists_span_eq_top_isStandardSmooth F (AffineCoordinateRing F X)
  obtain ⟨t, hts, ht⟩ : ∃ t ∈ s, p t ≠ 0 := by
    by_contra! h
    have hle : Ideal.span s ≤ RingHom.ker p.toAlgHom :=
      Ideal.span_le.mpr fun t ht => RingHom.mem_ker.mpr (h t ht)
    rw [hs] at hle
    have h1 := RingHom.mem_ker.mp (hle (Submodule.mem_top (x := 1)))
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := (hstd t hts).out
  exact exists_regularChart_of_away (A := Localization.Away t) t P p ht

end Scheme

end Langlands.Global.LocalModularCharacter
