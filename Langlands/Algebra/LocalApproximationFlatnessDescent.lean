import Langlands.Algebra.LocalApproximationFlatnessDescentStatement
import Langlands.Algebra.IdealLocalFlatnessCriterion
import Langlands.Algebra.IdealTensorRelation
import Langlands.Algebra.TensorKernelTransitionReduction
import Langlands.Algebra.DirectedModuleFlatnessAscent
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

/-! # Flatness descent along local approximation systems (Stacks 00R6) -/

open scoped TensorProduct

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra
namespace LocalApproximationFlatnessDescentProof

open DirectedModuleFlatnessAscentProof

section Directed

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
  (P : DirectedModuleSystem.{uI, uA, uN, uR, uM} ι R M)

theorem baseMap_baseMap {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (a : P.base i) :
    P.baseMap j k hjk (P.baseMap i j hij a) = P.baseMap i k (hij.trans hjk) a :=
  P.base_directed.map_map hij hjk a

theorem map_map {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : P.obj i) :
    P.map j k hjk (P.map i j hij x) = P.map i k (hij.trans hjk) x :=
  P.directed.map_map hij hjk x

/-- In a flat colimit, a relation at one stage becomes trivial at a later stage. -/
theorem exists_isTrivialRelation_of_flat (hP : P.IsColimit) [Module.Flat R M]
    {n : ℕ} (i : ι) (a : Fin n → P.base i) (x : Fin n → P.obj i)
    (hax : ∑ k, a k • x k = 0) :
    ∃ (j : ι) (h : i ≤ j), Module.IsTrivialRelation (fun k ↦ P.baseMap i j h (a k))
      (fun k ↦ P.map i j h (x k)) := by
  classical
  let : DirectedSystem P.obj (fun i j h ↦ (P.map i j h).toAddMonoidHom) := P.directed
  -- The relation becomes trivial in the flat colimit.
  have hM : ∑ k, P.baseι i (a k) • P.ιM i (x k) = 0 := by
    simpa only [map_sum, LinearMap.map_smulₛₗ, map_zero] using congrArg (P.ιM i) hax
  obtain ⟨m, c, y, hxy, hcy⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hM
  -- Consequences of the colimit property.
  have hRsurj : ∀ r : R, ∃ (i : ι) (b : P.base i), P.baseι i b = r := fun r ↦ by
    obtain ⟨z, hz⟩ := hP.1.2 r
    obtain ⟨i, b, rfl⟩ := Ring.DirectLimit.exists_of z
    exact ⟨i, b, by simpa only [DirectedModuleSystem.ringColimitMap_of] using hz⟩
  have hMsurj : ∀ v : M, ∃ (i : ι) (w : P.obj i), P.ιM i w = v := fun v ↦ by
    obtain ⟨z, hz⟩ := hP.2.2 v
    induction z using AddCommGroup.DirectLimit.induction_on with
    | ih i w =>
      exact ⟨i, w, by simpa only [DirectedModuleSystem.moduleColimitMap_of] using hz⟩
  have hzR : ∀ (j : ι) (b : P.base j), P.baseι j b = 0 →
      ∃ (j' : ι) (h : j ≤ j'), P.baseMap j j' h b = 0 := by
    intro j b hb
    apply Ring.DirectLimit.of.zero_exact
    apply hP.1.1
    simpa only [DirectedModuleSystem.ringColimitMap_of, map_zero] using hb
  have hzM : ∀ (j : ι) (w : P.obj j), P.ιM j w = 0 →
      ∃ (j' : ι) (h : j ≤ j'), P.map j j' h w = 0 := by
    intro j w hw
    let := Classical.decEq ι
    obtain ⟨j', h, hw'⟩ := AddCommGroup.DirectLimit.of.zero_exact (G := P.obj)
      (f := fun i j h ↦ (P.map i j h).toAddMonoidHom) j w
      (hP.2.1 (by simpa only [DirectedModuleSystem.moduleColimitMap_of, map_zero] using hw))
    exact ⟨j', h, hw'⟩
  -- Lift the coefficients and the elements to a common stage `j₀`.
  obtain ⟨i₁, c₁, hc₁⟩ := finite_lift (A := P.base) (fun i j h ↦ ⇑(P.baseMap i j h))
    (fun i ↦ ⇑(P.baseι i)) P.baseι_compat hRsurj (fun p : Fin n × Fin m ↦ c p.1 p.2)
  obtain ⟨i₂, y₂, hy₂⟩ := finite_lift (A := P.obj) (fun i j h ↦ ⇑(P.map i j h))
    (fun i ↦ ⇑(P.ιM i)) P.ιM_compat hMsurj y
  obtain ⟨j₁, hij₁, hi₁j₁⟩ := exists_ge_ge i i₁
  obtain ⟨j₀, hj₁j₀, hi₂j₀⟩ := exists_ge_ge j₁ i₂
  have hij₀ := hij₁.trans hj₁j₀
  have hi₁j₀ := hi₁j₁.trans hj₁j₀
  let a₀ : Fin n → P.base j₀ := fun k ↦ P.baseMap i j₀ hij₀ (a k)
  let x₀ : Fin n → P.obj j₀ := fun k ↦ P.map i j₀ hij₀ (x k)
  let c₀ : Fin n → Fin m → P.base j₀ := fun k l ↦ P.baseMap i₁ j₀ hi₁j₀ (c₁ (k, l))
  let y₀ : Fin m → P.obj j₀ := fun l ↦ P.map i₂ j₀ hi₂j₀ (y₂ l)
  have hd : ∀ k, P.ιM j₀ (x₀ k - ∑ l, c₀ k l • y₀ l) = 0 := by
    intro k
    simp only [map_sub, map_sum, LinearMap.map_smulₛₗ, x₀, c₀, y₀, P.ιM_compat,
      P.baseι_compat, hc₁, hy₂, hxy k, sub_self]
  have he : ∀ l, P.baseι j₀ (∑ k, a₀ k * c₀ k l) = 0 := by
    intro l
    simp only [map_sum, map_mul, a₀, c₀, P.baseι_compat, hc₁]
    exact hcy l
  -- The defects vanish at a common later stage `j`.
  choose jk hjk hjk0 using fun k ↦ hzM j₀ _ (hd k)
  choose jl hjl hjl0 using fun l ↦ hzR j₀ _ (he l)
  obtain ⟨j₂, hj₂⟩ := Finite.exists_le (Sum.elim jk jl)
  obtain ⟨j, hj₀j, hj₂j⟩ := exists_ge_ge j₀ j₂
  have hkj : ∀ k, jk k ≤ j := fun k ↦ (hj₂ (Sum.inl k)).trans hj₂j
  have hlj : ∀ l, jl l ≤ j := fun l ↦ (hj₂ (Sum.inr l)).trans hj₂j
  refine ⟨j, hij₀.trans hj₀j, m, fun k l ↦ P.baseMap j₀ j hj₀j (c₀ k l),
    fun l ↦ P.map j₀ j hj₀j (y₀ l), fun k ↦ ?_, fun l ↦ ?_⟩
  · have h1 := congrArg (P.map (jk k) j (hkj k)) (hjk0 k)
    rw [map_zero, map_map, map_sub, map_sum, sub_eq_zero] at h1
    simp only [LinearMap.map_smulₛₗ] at h1
    rw [← h1, map_map]
  · have h1 := congrArg (P.baseMap (jl l) j (hlj l)) (hjl0 l)
    rw [map_zero, baseMap_baseMap, map_sum] at h1
    simpa only [map_mul, a₀, baseMap_baseMap] using h1

/-- A finite family of relations with the same coefficients becomes trivial at one stage. -/
theorem exists_forall_isTrivialRelation_of_flat (hP : P.IsColimit) [Module.Flat R M]
    {n L : ℕ} (i : ι) (a : Fin n → P.base i) (x : Fin L → Fin n → P.obj i)
    (hax : ∀ l, ∑ k, a k • x l k = 0) :
    ∃ (j : ι) (h : i ≤ j), ∀ l, Module.IsTrivialRelation (fun k ↦ P.baseMap i j h (a k))
      (fun k ↦ P.map i j h (x l k)) := by
  choose j h ht using fun l ↦ exists_isTrivialRelation_of_flat P hP i a (x l) (hax l)
  obtain ⟨j₁, hj₁⟩ := Finite.exists_le j
  obtain ⟨j₂, hij₂, hj₁j₂⟩ := exists_ge_ge i j₁
  refine ⟨j₂, hij₂, fun l ↦ ?_⟩
  have hm := map_trivial_relation (P.baseMap (j l) j₂ ((hj₁ l).trans hj₁j₂))
    (P.map (j l) j₂ ((hj₁ l).trans hj₁j₂)).toAddMonoidHom
    (fun b w ↦ (P.map _ _ _).map_smulₛₗ b w) (ht l)
  simpa only [LinearMap.toAddMonoidHom_coe, baseMap_baseMap, map_map] using hm

end Directed

section Noetherian

variable {A : Type uA} {B : Type uB} {N : Type uN} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

variable (B N) in
/-- The relations among a finite family of scalars of `A`, as a `B`-submodule. -/
def relations {r : ℕ} (g : Fin r → A) : Submodule B (Fin r → N) where
  carrier := {x | ∑ k, g k • x k = 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, smul_add, Finset.sum_add_distrib] at *
    rw [hx, hy, add_zero]
  zero_mem' := by simp
  smul_mem' b x hx := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply] at *
    simp_rw [smul_comm (g _) b]
    rw [← Finset.smul_sum, hx, smul_zero]

/-- Over a Noetherian ring, the relations of a finite module are finitely generated: a property
of families that is closed under the module operations and holds on finitely many relations
holds on all relations. -/
theorem exists_relations_induction [IsNoetherianRing B] [Module.Finite B N] {r : ℕ}
    (g : Fin r → A) :
    ∃ (L : ℕ) (z : Fin L → Fin r → N), (∀ l, ∑ k, g k • z l k = 0) ∧
      ∀ p : (Fin r → N) → Prop, p 0 → (∀ x y, p x → p y → p (x + y)) →
        (∀ (b : B) x, p x → p (b • x)) → (∀ l, p (z l)) →
        ∀ x, ∑ k, g k • x k = 0 → p x := by
  obtain ⟨L, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (relations B N g))
  refine ⟨L, z, fun l ↦ ?_, fun p h0 hadd hsmul hgen x hx ↦ ?_⟩
  · have : z l ∈ relations B N g := hz ▸ Submodule.subset_span ⟨l, rfl⟩
    exact this
  · have hx' : x ∈ Submodule.span B (Set.range z) := by rw [hz]; exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      exact hgen l
    | zero => exact h0
    | add y y' _ _ hy hy' => exact hadd y y' hy hy'
    | smul b y _ hy => exact hsmul b y hy

end Noetherian

section Transition

variable {R R' S S' M M' : Type*}
  [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R R'] [Algebra R S] [Algebra S S'] [Algebra R' S'] [Algebra R S']
  [IsScalarTower R S S'] [IsScalarTower R R' S']
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup M'] [Module R' M'] [Module S M'] [Module S' M']
  [IsScalarTower R' S' M'] [IsScalarTower S S' M']

variable (S') in
include S' in
/-- An `S`-linear map `M → M'` is semilinear over `R → R'`. -/
theorem map_smul_base (f : M →ₗ[S] M') (a : R) (m : M) :
    f (a • m) = algebraMap R R' a • f m := by
  rw [← algebraMap_smul S a m, f.map_smul, ← algebraMap_smul S' (algebraMap R S a) (f m),
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' S', algebraMap_smul]

/-- The elementwise Tor-transition hypothesis follows from its case of generator relations. -/
theorem transition_of_generators (f : M →+ M')
    (hf : ∀ (a : R) (m : M), f (a • m) = algebraMap R R' a • f m) (I : Ideal R) {r : ℕ}
    (g : Fin r → I)
    (hg : Ideal.span (Set.range fun k ↦ (g k : R)) = I)
    (h : ∀ y : Fin r → M, ∑ k, (g k : R) • y k = 0 →
      ∑ k, (⟨algebraMap R R' (g k), Ideal.mem_map_of_mem _ (g k).2⟩ :
          I.map (algebraMap R R')) ⊗ₜ[R'] f (y k) = 0)
    (n : ℕ) (a : Fin n → I) (m : Fin n → M) (ha : ∑ k, (a k : R) • m k = 0) :
    ∑ k, (⟨algebraMap R R' (a k), Ideal.mem_map_of_mem _ (a k).2⟩ :
        I.map (algebraMap R R')) ⊗ₜ[R'] f (m k) = 0 := by
  have hc : ∀ k, ∃ c : Fin r → R, ∑ l, c l * g l = a k := fun k ↦ by
    have : (a k : R) ∈ Ideal.span (Set.range fun l ↦ (g l : R)) := by rw [hg]; exact (a k).2
    exact Ideal.mem_span_range_iff_exists_fun.mp this
  choose c hc using hc
  have hy : ∑ l, (g l : R) • ∑ k, c k l • m k = 0 := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, mul_comm (g _ : R) (c _ _), hc]
    exact ha
  have ha' : ∀ k, (⟨algebraMap R R' (a k), Ideal.mem_map_of_mem _ (a k).2⟩ :
      I.map (algebraMap R R')) = ∑ l, algebraMap R R' (c k l) •
        (⟨algebraMap R R' (g l), Ideal.mem_map_of_mem _ (g l).2⟩ :
          I.map (algebraMap R R')) := fun k ↦ by
    apply Subtype.ext
    simp [← hc k, map_sum, map_mul, Algebra.smul_def]
  have h' := h (fun l ↦ ∑ k, c k l • m k) hy
  simp_rw [ha', TensorProduct.sum_tmul, TensorProduct.smul_tmul]
  rw [Finset.sum_comm]
  simp_rw [← TensorProduct.tmul_sum, ← hf, ← map_sum]
  exact h'

end Transition

/-- The 00R6 assembly from the ideal local flatness criterion (00ML) and the tensor-kernel
transition reduction (00MO). -/
theorem descent_of
    (h00ML : IdealLocalFlatnessCriterionStatement.{uA, uB, uN})
    (hred : TensorKernelTransitionReductionStatement.{uA, uA, uB, uB, uN, uN}) :
    LocalApproximationFlatnessDescentStatement.{uI, uA, uB, uN, uR, uS, uM} := by
  intro ι _ _ _ R S M _ _ _ _ _ _ _ _ D E _ _ hE hM
  let : Module R M := Module.compHom M (algebraMap R S)
  have : Module.Flat R M := hM
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : ∀ i, Module (D.base i) (E.obj i) := fun i ↦
    Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))
  have : ∀ i, IsScalarTower (D.base i) (D.alg i) (E.obj i) := fun i ↦
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : ∀ i, IsNoetherianRing (D.base i) := fun i ↦
    have := hE.2.1 i
    Algebra.EssFiniteType.isNoetherianRing ℤ (D.base i)
  have : ∀ i, IsNoetherianRing (D.alg i) := fun i ↦
    have := hE.2.2.1 i
    Algebra.EssFiniteType.isNoetherianRing (D.base i) (D.alg i)
  have : ∀ i, Module.Finite (D.alg i) (E.obj i) := hE.2.2.2.1
  let i := Classical.arbitrary ι
  -- Generators of the maximal ideal and finitely many generating relations at stage `i`.
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal (D.base i)))
  obtain ⟨L, z, hz, hind⟩ := exists_relations_induction (B := D.alg i) (N := E.obj i) g
  -- They become trivial at a later stage `j`.
  obtain ⟨j, hij, htriv⟩ := exists_forall_isTrivialRelation_of_flat E.toDirectedModuleSystem
    ⟨hE.1.1.1, hE.1.2⟩ i g z hz
  -- The commutative square of the transition `i ≤ j`.
  let : Algebra (D.base i) (D.base j) := (D.baseMap i j hij).toAlgebra
  let : Algebra (D.alg i) (D.alg j) := (D.algMap i j hij).toAlgebra
  let : Algebra (D.base i) (D.alg j) :=
    ((algebraMap (D.base j) (D.alg j)).comp (D.baseMap i j hij)).toAlgebra
  have : IsScalarTower (D.base i) (D.alg i) (D.alg j) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (D.map_comm i j hij a).symm
  have : IsScalarTower (D.base i) (D.base j) (D.alg j) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module (D.alg i) (E.obj j) := Module.compHom (E.obj j) (D.algMap i j hij)
  have : IsScalarTower (D.alg i) (D.alg j) (E.obj j) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f : E.obj i →ₗ[D.alg i] E.obj j :=
    { toFun := E.map i j hij
      map_add' := (E.map i j hij).map_add
      map_smul' := (E.map i j hij).map_smulₛₗ }
  let I := IsLocalRing.maximalIdeal (D.base i)
  let gI : Fin r → I := fun k ↦ ⟨g k, hg.le (Submodule.subset_span ⟨k, rfl⟩)⟩
  -- The Tor transition vanishes.
  have hgen : ∀ y : Fin r → E.obj i, ∑ k, (gI k : D.base i) • y k = 0 →
      ∑ k, (⟨algebraMap (D.base i) (D.base j) (gI k), Ideal.mem_map_of_mem _ (gI k).2⟩ :
          I.map (algebraMap (D.base i) (D.base j))) ⊗ₜ[D.base j] f (y k) = 0 := by
    refine hind _ (by simp) (fun x y hx hy ↦ ?_) (fun b x hx ↦ ?_) (fun l ↦ ?_)
    · simp only [Pi.add_apply, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy,
        add_zero]
    · let μ : E.obj j →ₗ[D.base j] E.obj j :=
        (LinearMap.lsmul (D.alg j) (E.obj j) (D.algMap i j hij b)).restrictScalars (D.base j)
      have hμ := congrArg (LinearMap.lTensor (I.map (algebraMap (D.base i) (D.base j))) μ) hx
      simp only [map_sum, LinearMap.lTensor_tmul, map_zero] at hμ
      simp only [Pi.smul_apply, LinearMap.map_smul]
      exact hμ
    · exact IdealTensorRelation.sum_tmul_eq_zero_of_isTrivialRelation _ _ (htriv l)
  have htor := transition_of_generators (R' := D.base j) f.toAddMonoidHom
    (map_smul_base (D.alg j) f) I gI hg hgen
  -- The localization and base-change hypotheses.
  obtain ⟨p, hp, hploc⟩ := hE.2.2.2.2.1 i j hij
  have hprod : (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom (D.base i) (D.alg i) (D.alg j))
      (IsScalarTower.toAlgHom (D.base i) (D.base j) (D.alg j))).toRingHom =
        D.ringBaseChangeMap hij := by
    apply RingHom.ext
    intro t
    induction t with
    | tmul s a => rfl
    | add t t' ht ht' => simp only [map_add, ht, ht']
  have hloc : letI : Algebra (D.alg i ⊗[D.base i] D.base j) (D.alg j) :=
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom (D.base i) (D.alg i) (D.alg j))
        (IsScalarTower.toAlgHom (D.base i) (D.base j) (D.alg j))).toRingHom.toAlgebra
      IsLocalization p.primeCompl (D.alg j) := by
    rw [hprod]
    exact hploc
  have hbc : IsBaseChange (D.alg j) f :=
    IsBaseChange.of_equiv
      (LinearEquiv.ofBijective (E.moduleBaseChangeMap hij) (hE.2.2.2.2.2 i j hij))
      fun x ↦ by
        rw [LinearEquiv.ofBijective_apply, LocalModuleSystem.moduleBaseChangeMap_tmul, one_smul]
        rfl
  have hflatq : Module.Flat (D.base i ⧸ I) ((D.base i ⧸ I) ⊗[D.base i] E.obj i) := by
    let := Ideal.Quotient.field I
    have : Module.Free (D.base i ⧸ I) ((D.base i ⧸ I) ⊗[D.base i] E.obj i) :=
      Module.Free.of_divisionRing _ _
    exact Module.Flat.of_free
  -- The reduction gives the hypotheses of 00ML at stage `j`.
  obtain ⟨hinj, hflat'⟩ := hred (D.base i) (D.base j) (D.alg i) (D.alg j) (E.obj i) (E.obj j)
    I p.primeCompl f (IsNoetherian.noetherian I) hloc hbc hflatq htor
  have := D.structure_local j
  have : IsLocalHom (algebraMap (D.base i) (D.base j)) := D.baseMap_local i j hij
  have hne : I.map (algebraMap (D.base i) (D.base j)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (D.base j)).ne_top
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (map_mem_nonunits_iff (algebraMap (D.base i) (D.base j)) x).mpr hx
  exact ⟨j, h00ML (D.base j) (D.alg j) (E.obj j) _ hne inferInstance hinj hflat'⟩

/-- The 00R6 assembly from the ideal local flatness criterion (00ML) alone, using the proved
tensor-kernel transition reduction. -/
theorem descent_of_idealLocalFlatnessCriterion
    (h00ML : IdealLocalFlatnessCriterionStatement.{uA, uB, uN}) :
    LocalApproximationFlatnessDescentStatement.{uI, uA, uB, uN, uR, uS, uM} :=
  descent_of h00ML tensorKernelTransitionReduction

end LocalApproximationFlatnessDescentProof
end Langlands.Algebra

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.128.3 (00R6): for a local approximation system of a flat target
module, some component module is flat over its base ring. -/
theorem localApproximationFlatnessDescent :
    LocalApproximationFlatnessDescentStatement.{uI, uA, uB, uN, uR, uS, uM} :=
  LocalApproximationFlatnessDescentProof.descent_of_idealLocalFlatnessCriterion
    idealLocalFlatnessCriterion

end Langlands.Algebra
