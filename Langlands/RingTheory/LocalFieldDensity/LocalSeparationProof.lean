import Langlands.RingTheory.LocalFieldDensity.LocalSeparationStatement
import Langlands.RingTheory.LocalFieldDensity.Density
import Langlands.AlgebraicGeometry.PointTopology.Affine

/-! # Local separation in the actual evaluation topology -/

noncomputable section

universe u v

open MvPolynomial Filter Topology
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.RingTheory.LocalFieldDensity

open Langlands.AlgebraicGeometry.PointManifold

variable {K : Type*} [NontriviallyNormedField K]
variable {S : Type*} [CommRing S] [Algebra K S] {ι σ : Type*}

/-- The implicit-point construction preserves any prescribed evaluation neighbourhood. -/
theorem eventually_exists_algHom_mem [CompleteSpace K] [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation K S ι σ) (x : S →ₐ[K] K)
    (U : Set (AlgPoint K S K)) (hU : U ∈ 𝓝 (AlgPoint.ofAlgHom x)) :
    ∀ᶠ t in 𝓝 (fun i : FreeVar P.toPreSubmersivePresentation => x (P.val i)),
      ∃ y ∈ U, ∀ i : FreeVar P.toPreSubmersivePresentation, y (P.val i) = t i := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite σ
  set τ := FreeVar P.toPreSubmersivePresentation
  set v₀ : ι → K := fun i => x (P.val i)
  have hrel₀ : ∀ j, eval v₀ (P.relation j) = 0 := fun j => by
    have h := congrArg x (P.aeval_val_relation j)
    rwa [MvPolynomial.comp_aeval_apply, map_zero] at h
  let T : Set (ι → K) := {v | ∀ j, eval v (P.relation j) = 0}
  let L : T → AlgPoint K S K := fun v =>
    AlgPoint.ofAlgHom (pointOfSolution P.toPresentation v.val v.property)
  have hL : Continuous L := by
    rw [AlgPoint.continuous_iff]
    intro b
    obtain ⟨q, rfl⟩ := P.aeval_val_surjective b
    have heq : (fun v : T => L v (aeval P.val q)) = fun v => eval v.val q := by
      funext v
      change pointOfSolution P.toPresentation v.val v.property (aeval P.val q) = _
      rw [pointOfSolution, AlgHom.liftOfSurjective_apply]
      rfl
    rw [heq]
    exact (contDiff_polynomial_eval q 0).continuous.comp continuous_subtype_val
  have hLx : L ⟨v₀, hrel₀⟩ = AlgPoint.ofAlgHom x := by
    apply AlgPoint.ext
    intro b
    obtain ⟨q, rfl⟩ := P.aeval_val_surjective b
    change pointOfSolution P.toPresentation v₀ hrel₀ (aeval P.val q) = x (aeval P.val q)
    rw [pointOfSolution, AlgHom.liftOfSurjective_apply, MvPolynomial.comp_aeval_apply]
  have hN : L ⁻¹' U ∈ 𝓝 (⟨v₀, hrel₀⟩ : T) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hLx]; exact hU)
  rw [nhds_subtype, Filter.mem_comap] at hN
  obtain ⟨W, hW, hWsub⟩ := hN
  -- the relations together with the free variables
  let Φ : (ι → K) → (σ ⊕ τ → K) :=
    fun v => Sum.elim (fun j => eval v (P.relation j)) (fun i => v i)
  let D : (ι → K) →L[K] (σ ⊕ τ → K) :=
    ContinuousLinearMap.pi
      (Sum.elim (fun j => polynomialDerivative (P.relation j) v₀)
        (fun i => ContinuousLinearMap.proj (i : ι)))
  have hD : HasStrictFDerivAt Φ D v₀ := by
    rw [hasStrictFDerivAt_pi']
    rintro (j | i)
    · simpa [Φ, D] using hasStrictFDerivAt_polynomial_eval (P.relation j) v₀
    · simpa [Φ, D] using hasStrictFDerivAt_apply (𝕜 := K) (i : ι) v₀
  -- the derivative is injective since the Jacobian is a unit
  have hdet : (Matrix.of fun j k : σ =>
      eval v₀ (pderiv (P.map k) (P.relation j))).det ≠ 0 := by
    have h : (Matrix.of fun j k : σ => eval v₀ (pderiv (P.map k) (P.relation j))) =
        ((eval v₀).mapMatrix P.jacobiMatrix).transpose := by
      ext j k
      simp [P.jacobiMatrix_apply]
    rw [h, Matrix.det_transpose, ← RingHom.map_det]
    have hx : eval v₀ P.jacobiMatrix.det = x P.jacobian := by
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_eq, AlgHom.coe_toRingHom,
        MvPolynomial.comp_aeval_apply]
      rfl
    rw [hx]
    exact (P.jacobian_isUnit.map x).ne_zero
  have hinj : Function.Injective D := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    have hfree : ∀ i : τ, h i = 0 := fun i => by
      simpa [D] using congrFun hh (Sum.inr i)
    have hmap : (fun k => h (P.map k)) = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      ext j
      have hj := congrFun hh (Sum.inl j)
      simp only [D, ContinuousLinearMap.pi_apply, Sum.elim_inl, polynomialDerivative_apply,
        Pi.zero_apply] at hj
      rw [Pi.zero_apply, ← hj, Matrix.mulVec, dotProduct]
      refine Fintype.sum_of_injective P.map P.map_inj _ _ (fun i hi => ?_) (fun k => by simp)
      rw [hfree ⟨i, hi⟩, mul_zero]
    funext i
    by_cases hi : i ∈ Set.range P.map
    · obtain ⟨k, rfl⟩ := hi
      exact congrFun hmap k
    · exact hfree ⟨i, hi⟩
  have hcard : Fintype.card (σ ⊕ τ) = Fintype.card ι :=
    Fintype.card_congr ((Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj) (Equiv.refl τ)).trans
      (Equiv.sumCompl (fun i => i ∈ Set.range P.map)))
  have hdim : Module.finrank K (ι → K) = Module.finrank K (σ ⊕ τ → K) := by
    simp only [Module.finrank_fintype_fun_eq_card, hcard]
  let f' : (ι → K) ≃L[K] (σ ⊕ τ → K) :=
    (LinearMap.linearEquivOfInjective D.toLinearMap hinj hdim).toContinuousLinearEquiv
  have hD' : HasStrictFDerivAt Φ (f' : (ι → K) →L[K] (σ ⊕ τ → K)) v₀ := by
    have : (f' : (ι → K) →L[K] (σ ⊕ τ → K)) = D := by
      ext h : 1
      rfl
    rw [this]
    exact hD
  have hmapnhds := hD'.map_nhds_eq_of_equiv
  -- points with prescribed free coordinates
  let g : (τ → K) → (σ ⊕ τ → K) := fun t => Sum.elim (fun _ => 0) t
  have hg : Continuous g := continuous_pi fun k => by
    rcases k with j | i
    · exact continuous_const
    · exact continuous_apply i
  have hg₀ : g (fun i => v₀ i) = Φ v₀ := by
    funext k
    rcases k with j | i
    · exact (hrel₀ j).symm
    · rfl
  have hrange : Φ '' W ∈ 𝓝 (g (fun i => v₀ i)) := by
    rw [hg₀, ← hmapnhds]
    exact Filter.image_mem_map hW
  filter_upwards [hg.continuousAt.preimage_mem_nhds hrange] with t ht
  obtain ⟨v, hvW, hv⟩ := ht
  have hvrel : ∀ j, eval v (P.relation j) = 0 := fun j => congrFun hv (Sum.inl j)
  refine ⟨L ⟨v, hvrel⟩, hWsub hvW, fun i => ?_⟩
  change pointOfSolution P.toPresentation v hvrel (P.val i) = _
  rw [pointOfSolution_val]
  exact congrFun hv (Sum.inr i)

section LocalSeparation

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]

/-- Every evaluation neighbourhood of a smooth-domain point separates nonzero elements. -/
theorem exists_algPoint_mem_apply_ne_zero [Algebra.Smooth K A] [IsDomain A] (x : A →ₐ[K] K)
    (U : Set (AlgPoint K A K)) (hU : U ∈ 𝓝 (AlgPoint.ofAlgHom x))
    {a : A} (ha : a ≠ 0) : ∃ y ∈ U, y a ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K (RingHom.ker x)
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hstd.out
  set S := Localization.Away f
  have hxf : x f ≠ 0 := fun h => hf (RingHom.mem_ker.mpr h)
  have hf0 : f ≠ 0 := fun h => hxf (by rw [h, map_zero])
  have hpow := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  have : IsDomain S := IsLocalization.isDomain_localization hpow
  let x' : S →ₐ[K] K := IsLocalization.Away.liftAlgHom f (isUnit_iff_ne_zero.mpr hxf)
  set φ := freeCoordinates P.toPreSubmersivePresentation
  have hev : ∀ (y : S →ₐ[K] K) (c : MvPolynomial (FreeVar P.toPreSubmersivePresentation) K),
      y (φ c) = eval (fun i : FreeVar P.toPreSubmersivePresentation => y (P.val i)) c :=
    fun y c => by
      change y (aeval (fun i : FreeVar P.toPreSubmersivePresentation => P.val i) c) = _
      rw [MvPolynomial.comp_aeval_apply]; rfl
  have hN := eventually_exists_algHom P x'
  -- the free coordinates are algebraically independent
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    refine eq_zero_of_eventually_eval_eq_zero (hN.mono fun t ht => ?_)
    obtain ⟨y, hy⟩ := ht
    have : (fun i : FreeVar P.toPreSubmersivePresentation => y (P.val i)) = t := funext hy
    rw [← this, ← hev, hc, map_zero]
  have hh : algebraMap A S a ≠ 0 := fun h =>
    ha (IsLocalization.injective S hpow (by rw [h, map_zero]))
  obtain ⟨c, hc0, b, hcb⟩ := exists_ne_zero_freeCoordinates_eq_mul P hinj hh
  let r := AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A S)
  have hx'r : r (AlgPoint.ofAlgHom x') = AlgPoint.ofAlgHom x := by
    apply AlgPoint.ext
    intro a
    exact IsLocalization.Away.lift_eq f (isUnit_iff_ne_zero.mpr hxf) a
  have hU' : r ⁻¹' U ∈ 𝓝 (AlgPoint.ofAlgHom x') :=
    (AlgPoint.continuous_precomp _).continuousAt.preimage_mem_nhds
      (by change U ∈ 𝓝 (r (AlgPoint.ofAlgHom x')); rw [hx'r]; exact hU)
  have hNU := eventually_exists_algHom_mem P x' (r ⁻¹' U) hU'
  refine hc0 (eq_zero_of_eventually_eval_eq_zero (hNU.mono fun t ht => ?_))
  obtain ⟨y, hyU, hy⟩ := ht
  have hyt : (fun i : FreeVar P.toPreSubmersivePresentation => y.toAlgHom (P.val i)) = t :=
    funext hy
  have hya : y.toAlgHom (algebraMap A S a) = 0 := hcon (r y) hyU
  rw [← hyt, ← hev y.toAlgHom, hcb, map_mul, hya, zero_mul]


end LocalSeparation

/-- The complete local separation proposition, with independent universes. -/
theorem localSeparation : LocalSeparationStatement.{u,v} := by
  intro K _ _ A _ _ _ _ x U hU a ha
  exact exists_algPoint_mem_apply_ne_zero x.toAlgHom U hU ha

end Langlands.RingTheory.LocalFieldDensity
