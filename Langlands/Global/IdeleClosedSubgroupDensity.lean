import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.GlobalCompletionWeakApproximation

/-! # Closed subgroups of the idele group containing the principal and almost all local ideles

Let `H` be a closed subgroup of the idele group of a number field `K` which contains the
principal ideles and, for every finite place `v` outside a finite set `S`, the whole local
multiplicative group `K_v^×` inserted at `v`. Then `H` is the whole idele group.

The argument is the density argument from Worker 116's draft proof of Hecke-character
rigidity (shared draft of task `34b81620-20d7-4059-9b08-6bedd1c1c029`), recast for a closed subgroup instead of the kernel of a
character quotient:

* every idele of integral units equal to one on `S` is a limit of finite products of
  local integral units at places outside `S`, hence lies in `H`;
* every idele is the product of its archimedean part, its components at finitely many
  finite places, and such an integral unit idele; so `x ∈ H` as soon as the product of its
  archimedean part and its components at `S` lies in `H`;
* that product is a continuous function of the archimedean and `S`-adic components, the
  set of components where it lies in `H` is closed, and it contains the diagonal image of
  `Kˣ`, which is dense by weak approximation.
-/

noncomputable section

universe u

open Filter Topology

namespace Langlands.Global.IdeleDensity

open Langlands.Global Langlands.Global.HeckeFunctionalEquation

variable {K : Type u} [Field K] [NumberField K]

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

variable (H : Subgroup (Ideles K)) (S : Finset (FinitePlace K))

/-- An idele of integral units that is one on `S` lies in every closed subgroup containing
the local groups at all finite places outside `S`. -/
theorem integralUnitIdeles_mem (hH : IsClosed (H : Set (Ideles K)))
    (hloc : ∀ v ∉ S, ∀ a : (FiniteCompletion K v)ˣ, finiteIdeleInclusion K v a ∈ H)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) (hu : ∀ v ∈ S, u v = 1) :
    integralUnitIdeles K u ∈ H := by
  classical
  have hcl : IsClosed ((integralUnitIdeles K) ⁻¹' (H : Set (Ideles K))) :=
    hH.preimage (integralUnitIdeles K).continuous
  have hmem : u ∈ closure ((integralUnitIdeles K) ⁻¹' (H : Set (Ideles K))) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    rw [nhds_pi, Filter.mem_pi'] at hN
    obtain ⟨T, t, ht, hTN⟩ := hN
    let u₁ : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ :=
      ∏ v ∈ T, Pi.mulSingle v (u v)
    have hu₁ : ∀ j, u₁ j = if j ∈ T then u j else 1 := by
      intro j
      simp only [u₁, Finset.prod_apply]
      exact Finset.prod_pi_mulSingle j u T
    refine ⟨u₁, hTN fun j hj => ?_, ?_⟩
    · have hj' : j ∈ T := hj
      simp only [hu₁ j, hj', ↓reduceIte]
      exact mem_of_mem_nhds (ht j)
    · change integralUnitIdeles K u₁ ∈ H
      simp only [u₁, map_prod]
      apply H.prod_mem
      intro v _
      by_cases hvS : v ∈ S
      · rw [hu v hvS, Pi.mulSingle_one, map_one]
        exact H.one_mem
      · rw [integralUnitIdeles_mulSingle]
        exact hloc v hvS _
  rw [hcl.closure_eq] at hmem
  exact hmem

/-- The archimedean and `S`-adic unit groups, coordinatewise. -/
abbrev LocalUnits :=
  (∀ w : InfinitePlace K, (InfiniteCompletion K w)ˣ) × (∀ v : S, (FiniteCompletion K v.val)ˣ)

/-- The diagonal embedding of `Kˣ` in the archimedean and `S`-adic units. -/
def localDiagonal (a : Kˣ) : LocalUnits (K := K) S :=
  (fun w => Units.map (algebraMap K (InfiniteCompletion K w)).toMonoidHom a,
    fun v => Units.map (algebraMap K (FiniteCompletion K v.val)).toMonoidHom a)

/-- Weak approximation: `Kˣ` is dense in the archimedean and `S`-adic units. -/
theorem denseRange_localDiagonal : DenseRange (localDiagonal (K := K) S) := by
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

/-- The idele with prescribed archimedean and `S`-adic components and all other finite
components equal to one. -/
def localIdele (q : LocalUnits (K := K) S) : Ideles K :=
  infiniteIdelesInclusion K
      ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace K => InfiniteCompletion K w)).symm
        q.1) *
    ∏ v : S, finiteIdeleInclusion K v.val (q.2 v)

theorem continuous_localIdele : Continuous (localIdele (K := K) S) := by
  apply Continuous.mul
  · exact (infiniteIdelesInclusion K).continuous.comp
      ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace K =>
        InfiniteCompletion K w)).symm.continuous.comp continuous_fst)
  · apply continuous_finsetProd
    intro v _
    exact (finiteIdeleInclusion K v.val).continuous.comp
      ((continuous_apply v).comp continuous_snd)

/-- The archimedean and `S`-adic components of an idele. -/
def localComponents (x : Ideles K) : LocalUnits (K := K) S :=
  (ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace K => InfiniteCompletion K w)
    (ideleProductEquiv K x).1, fun v => finiteIdeleProjection K v.val x)

theorem localComponents_diagonalUnits (a : Kˣ) :
    localComponents S (diagonalUnits K a) = localDiagonal S a := rfl

/-- Every idele differs from the idele of its archimedean and `S`-adic components by an
element of `H`. -/
theorem mul_inv_localIdele_mem (hH : IsClosed (H : Set (Ideles K)))
    (hloc : ∀ v ∉ S, ∀ a : (FiniteCompletion K v)ˣ, finiteIdeleInclusion K v a ∈ H)
    (x : Ideles K) : (localIdele S (localComponents S x))⁻¹ * x ∈ H := by
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
  have hsplit : a = (∏ v ∈ S, finiteIdeleInclusion K v (c v)) *
      ∏ v ∈ R \ S, finiteIdeleInclusion K v (c v) := by
    rw [mul_comm]
    exact (Finset.prod_sdiff hSR).symm
  have hlocal : localIdele S (localComponents S x) =
      infiniteIdelesInclusion K (ideleProductEquiv K x).1 *
        ∏ v ∈ S, finiteIdeleInclusion K v (c v) := by
    rw [localIdele]
    congr 1
    exact Finset.prod_coe_sort S (fun v => finiteIdeleInclusion K v (c v))
  have hrest : (∏ v ∈ R \ S, finiteIdeleInclusion K v (c v)) ∈ H := by
    apply H.prod_mem
    intro v hv
    exact hloc v (Finset.mem_sdiff.mp hv).2 _
  have hu_mem : integralUnitIdeles K u ∈ H := integralUnitIdeles_mem H S hH hloc u hu
  have key : (localIdele S (localComponents S x))⁻¹ * x =
      (∏ v ∈ R \ S, finiteIdeleInclusion K v (c v)) * integralUnitIdeles K u := by
    rw [hlocal, inv_mul_eq_iff_eq_mul]
    conv_lhs => rw [hdecomp, hsplit]
    simp only [mul_assoc]
  rw [key]
  exact H.mul_mem hrest hu_mem

/-- A closed subgroup of the ideles containing the principal ideles and, outside a finite
set of finite places, every local multiplicative group, is the whole idele group. -/
theorem eq_top_of_isClosed (hH : IsClosed (H : Set (Ideles K)))
    (hprin : ∀ a : Kˣ, diagonalUnits K a ∈ H)
    (hloc : ∀ v ∉ S, ∀ a : (FiniteCompletion K v)ˣ, finiteIdeleInclusion K v a ∈ H) :
    H = ⊤ := by
  have hclosed : IsClosed {q : LocalUnits (K := K) S | localIdele S q ∈ H} :=
    hH.preimage (continuous_localIdele S)
  have hdiag : ∀ a : Kˣ, localIdele S (localDiagonal S a) ∈ H := by
    intro a
    have h := mul_inv_localIdele_mem H S hH hloc (diagonalUnits K a)
    rw [localComponents_diagonalUnits] at h
    have h' := H.mul_mem (hprin a) (H.inv_mem h)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h'
  have hall : ∀ q : LocalUnits (K := K) S, localIdele S q ∈ H := by
    intro q
    have hq : q ∈ closure (Set.range (localDiagonal (K := K) S)) :=
      denseRange_localDiagonal S q
    have hsub : Set.range (localDiagonal (K := K) S) ⊆
        {q : LocalUnits (K := K) S | localIdele S q ∈ H} := by
      rintro _ ⟨a, rfl⟩
      exact hdiag a
    exact hclosed.closure_subset_iff.mpr hsub hq
  rw [eq_top_iff]
  intro x _
  have h := mul_inv_localIdele_mem H S hH hloc x
  have h' := H.mul_mem (hall (localComponents S x)) h
  rwa [mul_inv_cancel_left] at h'

end Langlands.Global.IdeleDensity
