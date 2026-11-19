import Langlands.Automorphic.Unramified.HeckeCharacterRigidityStatement
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.GlobalCompletionWeakApproximation

/-! # Rigidity of Hecke characters from almost all finite components -/

noncomputable section

universe u

open Filter Topology

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.HeckeFunctionalEquation

namespace HeckeRigidity

variable {K : Type u} [Field K] [NumberField K]

/-- The quotient character `χ / η` on the full idele group. -/
def ratio (χ η : HeckeCharacter K) : Ideles K →ₜ* ℂˣ where
  toFun x := χ.onIdeles x / η.onIdeles x
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    exact mul_div_mul_comm _ _ _ _
  continuous_toFun := χ.onIdeles.continuous.div' η.onIdeles.continuous

theorem ratio_apply (χ η : HeckeCharacter K) (x : Ideles K) :
    ratio χ η x = χ.onIdeles x / η.onIdeles x := rfl

theorem eq_of_ratio_eq_one (χ η : HeckeCharacter K) (h : ∀ x, ratio χ η x = 1) : χ = η := by
  apply DFunLike.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx := h x
    rw [ratio_apply, div_eq_one] at hx
    exact hx

/-- Step A: the ratio is trivial on every local multiplicative group outside `S`. -/
theorem ratio_finiteIdeleInclusion (χ η : HeckeCharacter K) (v : FinitePlace K)
    (hv : χ.finiteComponent v = η.finiteComponent v) (a : (FiniteCompletion K v)ˣ) :
    ratio χ η (finiteIdeleInclusion K v a) = 1 := by
  rw [ratio_apply, div_eq_one]
  exact DFunLike.congr_fun hv a

/-- Step B: the ratio is trivial on integral units equal to one on `S`. -/
theorem ratio_integralUnitIdeles (χ η : HeckeCharacter K) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, χ.finiteComponent v = η.finiteComponent v)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) (hu : ∀ v ∈ S, u v = 1) :
    ratio χ η (integralUnitIdeles K u) = 1 := by
  classical
  let Φ := (ratio χ η).comp (integralUnitIdeles K)
  let U : Set (∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :=
    {x | ‖(Φ x : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hU : U ∈ 𝓝 (1 : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) := by
    apply (isOpen_lt ((Units.continuous_val.comp Φ.continuous).sub
      continuous_const).norm continuous_const).mem_nhds
    simp
  simp only [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨T, t, ht, hTU⟩ := hU
  -- Triviality on elements equal to one on `T`.
  have htriv : ∀ w : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
      (∀ v ∈ T, w v = 1) → Φ w = 1 := by
    intro w hw
    apply Units.ext
    apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
    intro n
    have hwn : w ^ n ∈ U := by
      apply hTU
      intro j hj
      simpa only [Pi.pow_apply, hw j hj, one_pow, Pi.one_apply] using mem_of_mem_nhds (ht j)
    change ‖(Φ (w ^ n) : ℂ) - 1‖ < (1 / 2 : ℝ) at hwn
    simpa only [map_pow, Units.val_pow_eq_pow_val] using hwn
  -- Remove the finitely many coordinates in `T`.
  let u₁ : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ :=
    ∏ v ∈ T, Pi.mulSingle v (u v)
  have hu₁ : ∀ j, u₁ j = if j ∈ T then u j else 1 := by
    intro j
    simp only [u₁, Finset.prod_apply]
    exact Finset.prod_pi_mulSingle j u T
  have hΦu₁ : Φ u₁ = 1 := by
    simp only [u₁, map_prod]
    apply Finset.prod_eq_one
    intro v _
    by_cases hvS : v ∈ S
    · rw [hu v hvS, Pi.mulSingle_one, map_one]
    · change ratio χ η (integralUnitIdeles K (Pi.mulSingle v (u v))) = 1
      rw [integralUnitIdeles_mulSingle]
      exact ratio_finiteIdeleInclusion χ η v (hS v hvS) _
  have hw : ∀ j ∈ T, (u * u₁⁻¹) j = 1 := by
    intro j hj
    simp only [Pi.mul_apply, Pi.inv_apply, hu₁ j, hj, ite_true, mul_inv_cancel]
  have h := htriv (u * u₁⁻¹) hw
  rw [map_mul, map_inv, hΦu₁, inv_one, mul_one] at h
  exact h


/-- The finite coordinate of an idele as a monoid homomorphism. -/
def coord (v : FinitePlace K) : Ideles K →* FiniteCompletion K v :=
  (finiteProjection K v).toMonoidHom.comp (Units.coeHom (Adeles K))

/-- The infinite part of an idele as a monoid homomorphism. -/
def infPart : Ideles K →* InfiniteAdeles K :=
  (MonoidHom.fst (InfiniteAdeles K) (FiniteAdeles K)).comp (Units.coeHom (Adeles K))

theorem idele_ext {x y : Ideles K} (hinf : infPart x = infPart y)
    (hf : ∀ v, coord v x = coord v y) : x = y := by
  apply Units.ext
  apply Prod.ext hinf
  apply RestrictedProduct.ext
  intro v
  exact hf v

open scoped Classical in
theorem coord_finiteIdeleInclusion (v w : FinitePlace K) (a : (FiniteCompletion K v)ˣ) :
    coord w (finiteIdeleInclusion K v a) =
      (Pi.mulSingle v a.val : ∀ w : FinitePlace K, FiniteCompletion K w) w := rfl

theorem infPart_finiteIdeleInclusion (v : FinitePlace K) (a : (FiniteCompletion K v)ˣ) :
    infPart (finiteIdeleInclusion K v a) = 1 := rfl

theorem coord_infiniteIdelesInclusion (w : FinitePlace K) (z : (InfiniteAdeles K)ˣ) :
    coord w (infiniteIdelesInclusion K z) = 1 := rfl

theorem infPart_infiniteIdelesInclusion (z : (InfiniteAdeles K)ˣ) :
    infPart (infiniteIdelesInclusion K z) = z.val := rfl

theorem coord_integralUnitIdeles (w : FinitePlace K)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    coord w (integralUnitIdeles K u) = ((u w).val : FiniteCompletion K w) := rfl

theorem infPart_integralUnitIdeles (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    infPart (integralUnitIdeles K u) = 1 := rfl

/-- The ratio is determined by the infinite part and the components at `S`. -/
theorem ratio_eq_local (χ η : HeckeCharacter K) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, χ.finiteComponent v = η.finiteComponent v) (x : Ideles K) :
    ratio χ η x = ratio χ η (infiniteIdelesInclusion K (ideleProductEquiv K x).1) *
      ∏ v ∈ S, ratio χ η (finiteIdeleInclusion K v (finiteIdeleProjection K v x)) := by
  classical
  let P : FinitePlace K → Prop := fun v =>
    coord v x ∈ v.adicCompletionIntegers K ∧ coord v x⁻¹ ∈ v.adicCompletionIntegers K
  have hev : ∀ᶠ v in cofinite, P v :=
    (IsDedekindDomain.FiniteAdeleRing.cofinite_mem_adicCompletionIntegers x.val.2).and
      (IsDedekindDomain.FiniteAdeleRing.cofinite_mem_adicCompletionIntegers (x⁻¹).val.2)
  have hfin : {v | ¬ P v}.Finite := Filter.eventually_cofinite.mp hev
  let R : Finset (FinitePlace K) := hfin.toFinset ∪ S
  have hSR : S ⊆ R := Finset.subset_union_right
  have hPR : ∀ v ∉ R, P v := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (hfin.mem_toFinset.mpr h))
  let c : ∀ v : FinitePlace K, (FiniteCompletion K v)ˣ := fun v => finiteIdeleProjection K v x
  let a : Ideles K := ∏ v ∈ R, finiteIdeleInclusion K v (c v)
  let u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ := fun v =>
    if h : v ∈ R then 1 else
      { val := ⟨coord v x, (hPR v h).1⟩
        inv := ⟨coord v x⁻¹, (hPR v h).2⟩
        val_inv := Subtype.ext (by
          change coord v x * coord v x⁻¹ = 1
          rw [← map_mul, mul_inv_cancel, map_one])
        inv_val := Subtype.ext (by
          change coord v x⁻¹ * coord v x = 1
          rw [← map_mul, inv_mul_cancel, map_one]) }
  have hu : ∀ v ∈ S, u v = 1 := fun v hv => by simp [u, hSR hv]
  have hcoord_a : ∀ w, coord w a = if w ∈ R then coord w x else 1 := by
    intro w
    simp only [a, map_prod, coord_finiteIdeleInclusion]
    exact Finset.prod_pi_mulSingle w (fun v => (c v).val) R
  have hinf_a : infPart a = 1 := by
    simp only [a, map_prod, infPart_finiteIdeleInclusion, Finset.prod_const_one]
  have hdecomp : x = infiniteIdelesInclusion K (ideleProductEquiv K x).1 * a *
      integralUnitIdeles K u := by
    apply idele_ext
    · rw [map_mul, map_mul, infPart_infiniteIdelesInclusion, hinf_a,
        infPart_integralUnitIdeles, mul_one, mul_one]
      rfl
    · intro w
      rw [map_mul, map_mul, coord_infiniteIdelesInclusion, hcoord_a, coord_integralUnitIdeles,
        one_mul]
      by_cases hw : w ∈ R
      · simp [u, hw]
      · simp [u, hw]
  have hratio_u : ratio χ η (integralUnitIdeles K u) = 1 :=
    ratio_integralUnitIdeles χ η S hS u hu
  have hratio_a : ratio χ η a =
      ∏ v ∈ S, ratio χ η (finiteIdeleInclusion K v (finiteIdeleProjection K v x)) := by
    simp only [a, map_prod]
    symm
    apply Finset.prod_subset hSR
    intro v _ hvS
    exact ratio_finiteIdeleInclusion χ η v (hS v hvS) _
  conv_lhs => rw [hdecomp]
  rw [map_mul, map_mul, hratio_u, mul_one, hratio_a]

/-- The archimedean and `S`-adic unit groups, coordinatewise. -/
abbrev LocalUnits (S : Finset (FinitePlace K)) :=
  (∀ w : InfinitePlace K, (InfiniteCompletion K w)ˣ) × (∀ v : S, (FiniteCompletion K v.val)ˣ)

/-- The diagonal embedding of `Kˣ` in the archimedean and `S`-adic units. -/
def localDiagonal (S : Finset (FinitePlace K)) (a : Kˣ) : LocalUnits (K := K) S :=
  (fun w => Units.map (algebraMap K (InfiniteCompletion K w)).toMonoidHom a,
    fun v => Units.map (algebraMap K (FiniteCompletion K v.val)).toMonoidHom a)

/-- Weak approximation: `Kˣ` is dense in the archimedean and `S`-adic units. -/
theorem denseRange_localDiagonal (S : Finset (FinitePlace K)) :
    DenseRange (localDiagonal (K := K) S) := by
  classical
  let Y := (∀ w : InfinitePlace K, InfiniteCompletion K w) × (∀ v : S, FiniteCompletion K v.val)
  let j : LocalUnits (K := K) S → Y :=
    Prod.map (Pi.map fun w => (Units.val : (InfiniteCompletion K w)ˣ → _))
      (Pi.map fun v => (Units.val : (FiniteCompletion K v.val)ˣ → _))
  have hj : Topology.IsInducing j :=
    ((Topology.IsEmbedding.piMap fun _ => Units.isEmbedding_val₀).prodMap
      (Topology.IsEmbedding.piMap fun _ => Units.isEmbedding_val₀)).isInducing
  let U : Set Y := (Set.univ.pi fun _ => {0}ᶜ) ×ˢ (Set.univ.pi fun _ => {0}ᶜ)
  have hU : IsOpen U :=
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_compl_singleton).prod
      (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_compl_singleton)
  have hD := denseRange_numberFieldFiniteCompletionDiagonal K S
  have hsub : U ∩ Set.range (numberFieldFiniteCompletionDiagonal K S) ⊆
      j '' Set.range (localDiagonal (K := K) S) := by
    rintro y ⟨hyU, x, rfl⟩
    have hx : x ≠ 0 := by
      intro hx0
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
      have h := hyU.1 w (Set.mem_univ w)
      apply h
      change algebraMap K (InfiniteCompletion K w) x = 0
      rw [hx0, map_zero]
    refine ⟨localDiagonal S (Units.mk0 x hx), ⟨_, rfl⟩, ?_⟩
    rfl
  rw [DenseRange, hj.dense_iff]
  intro q
  have hq : j q ∈ U := by
    refine ⟨fun w _ => (q.1 w).ne_zero, fun v _ => (q.2 v).ne_zero⟩
  exact closure_mono hsub (hD.open_subset_closure_inter hU hq)

/-- The local character on archimedean and `S`-adic units. -/
def localRatio (χ η : HeckeCharacter K) (S : Finset (FinitePlace K))
    (q : LocalUnits (K := K) S) : ℂˣ :=
  ratio χ η (infiniteIdelesInclusion K
      ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace K => InfiniteCompletion K w)).symm
        q.1)) *
    ∏ v : S, ratio χ η (finiteIdeleInclusion K v.val (q.2 v))

theorem continuous_localRatio (χ η : HeckeCharacter K) (S : Finset (FinitePlace K)) :
    Continuous (localRatio χ η S) := by
  apply Continuous.mul
  · exact (ratio χ η).continuous.comp ((infiniteIdelesInclusion K).continuous.comp
      ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace K =>
        InfiniteCompletion K w)).symm.continuous.comp continuous_fst))
  · apply continuous_finsetProd
    intro v _
    exact (ratio χ η).continuous.comp ((finiteIdeleInclusion K v.val).continuous.comp
      ((continuous_apply v).comp continuous_snd))

theorem ratio_eq_localRatio (χ η : HeckeCharacter K) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, χ.finiteComponent v = η.finiteComponent v) (x : Ideles K) :
    ratio χ η x = localRatio χ η S
      (ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace K => InfiniteCompletion K w)
        (ideleProductEquiv K x).1, fun v => finiteIdeleProjection K v.val x) := by
  rw [ratio_eq_local χ η S hS x, localRatio]
  congr 1
  exact (Finset.prod_coe_sort S (fun v => ratio χ η (finiteIdeleInclusion K v
    (finiteIdeleProjection K v x)))).symm

theorem localRatio_localDiagonal (χ η : HeckeCharacter K) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, χ.finiteComponent v = η.finiteComponent v) (a : Kˣ) :
    localRatio χ η S (localDiagonal S a) = 1 := by
  have h := ratio_eq_localRatio χ η S hS (diagonalUnits K a)
  have hdiag : ratio χ η (diagonalUnits K a) = 1 := by
    rw [ratio_apply, HeckeCharacter.onIdeles_diagonalUnits,
      HeckeCharacter.onIdeles_diagonalUnits, div_one]
  rw [hdiag] at h
  rw [h]
  rfl

end HeckeRigidity

open HeckeRigidity in
/-- Two Hecke characters whose finite components agree, and are unramified,
outside a finite set of finite places are equal. -/
theorem heckeLocalComponentRigidity : HeckeLocalComponentRigidityStatement.{u} := by
  intro K _ _ χ η S h
  have hS : ∀ v ∉ S, χ.finiteComponent v = η.finiteComponent v := fun v hv => (h v hv).2.2
  have hloc : localRatio χ η S = fun _ => 1 :=
    (denseRange_localDiagonal (K := K) S).equalizer (continuous_localRatio χ η S)
      continuous_const (funext (localRatio_localDiagonal χ η S hS))
  apply eq_of_ratio_eq_one
  intro x
  rw [ratio_eq_localRatio χ η S hS x, hloc]

end Langlands.Automorphic.Unramified
