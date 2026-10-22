import Langlands.Galois.FiniteField.Comparison

noncomputable section

namespace Langlands.Galois.FiniteField

open CategoryTheory Opposite ProfiniteGrp
open Langlands.Weil

universe u v

private def finiteKernel {H : Type v} [Group H] [Finite H]
    (f : Degree →* H) : FiniteIndexNormalSubgroup Degree :=
  FiniteIndexNormalSubgroup.ofSubgroup f.ker

private def liftFinite {H : Type v} [Group H] [Finite H] [TopologicalSpace H]
    (f : Degree →* H) : ProfiniteIntegers →ₜ* H where
  toFun x := QuotientGroup.lift f.ker f (by intro x hx; exact hx) (x.val (finiteKernel f))
  map_one' := map_one _
  map_mul' x y := map_mul _ _ _
  continuous_toFun := by
    let Q := (ProfiniteCompletion.diagram (GrpCat.of Degree)).obj (finiteKernel f)
    have : Finite Q := by
      change Finite (Degree ⧸ f.ker)
      infer_instance
    have : DiscreteTopology Q := inferInstance
    let π : ProfiniteIntegers →ₜ* Q :=
      ((limitCone (ProfiniteCompletion.diagram (GrpCat.of Degree))).π.app (finiteKernel f)).hom
    exact (continuous_of_discreteTopology (f := fun q : Q =>
      QuotientGroup.lift f.ker f (by intro x hx; exact hx) q)).comp π.continuous

private theorem liftFinite_eta {H : Type v} [Group H] [Finite H] [TopologicalSpace H]
    (f : Degree →* H) (n : Degree) : liftFinite f (frobenius n) = f n := rfl

variable (k : Type u) [Field k] [Finite k]

theorem arithmetic_apply (K : Type v) [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] (x : K) :
    arithmetic k K x = x ^ Nat.card k := by
  simp [arithmetic, Fintype.card_eq_nat_card]

theorem arithmetic_restrict (L : IntermediateField k (AlgebraicClosure k))
    [FiniteDimensional k L] :
    finiteRestriction k L (arithmeticFrobenius k) = arithmetic k L := by
  let : Finite L := Module.finite_of_finite k
  let : IsGalois k L := inferInstance
  ext x
  change ((AlgEquiv.restrictNormalHom L) (arithmetic k (AlgebraicClosure k)) x).val = _
  rw [AlgEquiv.restrictNormalHom_apply]
  simp only [arithmetic_apply, IntermediateField.coe_pow]

theorem geometric_restrict (L : IntermediateField k (AlgebraicClosure k))
    [FiniteDimensional k L] :
    finiteRestriction k L (geometricFrobenius k) = geometric k L := by
  change finiteRestriction k L ((arithmeticFrobenius k)⁻¹) = _
  rw [map_inv, arithmetic_restrict]
  rfl

private instance closureGalois : IsGalois k (AlgebraicClosure k) := {}

private def component (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    ProfiniteIntegers →ₜ*
      (InfiniteGalois.asProfiniteGaloisGroupFunctor k (AlgebraicClosure k)).obj (op L) :=
  have : Finite ((InfiniteGalois.asProfiniteGaloisGroupFunctor k (AlgebraicClosure k)).obj (op L)) := by
    change Finite Gal(L/k)
    infer_instance
  liftFinite (zpowersHom _ (geometric k L))

private theorem component_eta (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (n : Degree) :
    component k L (frobenius n) = (geometric k L) ^ n.toAdd := rfl

private theorem component_eta_limit
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) (n : Degree) :
    component k L (frobenius n) =
      (InfiniteGalois.algEquivToLimit k (AlgebraicClosure k)
        ((geometric k (AlgebraicClosure k)) ^ n.toAdd)).val (op L) := by
  change (geometric k L) ^ n.toAdd =
    (finiteRestriction k L.toIntermediateField)
      ((geometricFrobenius k) ^ n.toAdd)
  rw [map_zpow, geometric_restrict]

private def toGaloisLimit :
    ProfiniteIntegers →ₜ*
      limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k (AlgebraicClosure k)) where
  toFun x :=
    ⟨fun L => component k L.unop x, by
      intro L₁ L₂ f
      have h :
          (fun z => (InfiniteGalois.asProfiniteGaloisGroupFunctor k (AlgebraicClosure k)).map f
            (component k L₁.unop z)) = component k L₂.unop := by
        apply (ProfiniteCompletion.denseRange (G := GrpCat.of Degree)).equalizer
          (((InfiniteGalois.asProfiniteGaloisGroupFunctor k (AlgebraicClosure k)).map f).hom.continuous.comp
            (component k L₁.unop).continuous) (component k L₂.unop).continuous
        funext n
        change (InfiniteGalois.asProfiniteGaloisGroupFunctor k (AlgebraicClosure k)).map f
          (component k L₁.unop (frobenius n)) = component k L₂.unop (frobenius n)
        rw [component_eta_limit, component_eta_limit]
        exact (InfiniteGalois.algEquivToLimit k (AlgebraicClosure k)
          ((geometric k (AlgebraicClosure k)) ^
            Multiplicative.toAdd (show Degree from n))).property f
      exact congrFun h x⟩
  map_one' := by
    apply Subtype.ext
    funext L
    exact map_one (component k L.unop)
  map_mul' x y := by
    apply Subtype.ext
    funext L
    exact map_mul (component k L.unop) x y
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_pi (fun L => (component k L.unop).continuous)

private def fromProfinite : ProfiniteIntegers →ₜ* Field.absoluteGaloisGroup k :=
  (ContinuousMonoidHom.toContinuousMonoidHom (closureAction k).symm).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom
      (InfiniteGalois.continuousMulEquivToLimit k (AlgebraicClosure k)).symm).comp
      (toGaloisLimit k))

private theorem fromProfinite_eta (n : Degree) :
    fromProfinite k (frobenius n) = (geometricFrobenius k) ^ n.toAdd := by
  apply (closureAction k).injective
  apply (InfiniteGalois.continuousMulEquivToLimit k (AlgebraicClosure k)).injective
  change (InfiniteGalois.continuousMulEquivToLimit k (AlgebraicClosure k))
      ((InfiniteGalois.continuousMulEquivToLimit k (AlgebraicClosure k)).symm
        (toGaloisLimit k (frobenius n))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  apply Subtype.ext
  funext L
  exact component_eta_limit k L.unop n

theorem arithmetic_order (K : Type v) [Field K] [Algebra k K] [Finite K] :
    orderOf (arithmetic k K) = Module.finrank k K := by
  let := Fintype.ofFinite k
  exact _root_.FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k K

theorem geometric_order (K : Type v) [Field K] [Algebra k K] [Finite K] :
    orderOf (geometric k K) = Module.finrank k K := by
  rw [geometric, orderOf_inv, arithmetic_order]

theorem arithmetic_generates (K : Type v) [Field K] [Algebra k K] [Finite K]
    (σ : Gal(K/k)) :
    ∃ i : Fin (Module.finrank k K), (arithmetic k K) ^ i.val = σ := by
  let := Fintype.ofFinite k
  exact (_root_.FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k K).surjective σ

theorem geometric_generates (K : Type v) [Field K] [Algebra k K] [Finite K]
    (σ : Gal(K/k)) :
    ∃ i : Fin (Module.finrank k K), (geometric k K) ^ i.val = σ := by
  obtain ⟨i, hi⟩ := arithmetic_generates k K σ⁻¹
  refine ⟨i, ?_⟩
  simpa [geometric, inv_pow] using congrArg Inv.inv hi

private theorem exists_intermediate_degree (n : ℕ) (hn : n ≠ 0) :
    ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k), Module.finrank k L = n := by
  let : NeZero n := ⟨hn⟩
  obtain ⟨p, hp⟩ := CharP.exists k
  let : CharP k p := hp
  let : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let E := _root_.FiniteField.Extension k p n
  let f : E →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  have : Finite f.fieldRange := Finite.of_equiv E f.equivFieldRange.toEquiv
  let L : FiniteGaloisIntermediateField k (AlgebraicClosure k) :=
    { toIntermediateField := f.fieldRange }
  refine ⟨L, ?_⟩
  exact f.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans
    (_root_.FiniteField.finrank_extension k p n)

private theorem geometric_dense :
    DenseRange (fun n : Degree => (geometric k (AlgebraicClosure k)) ^ n.toAdd) := by
  intro σ
  apply mem_closure_iff_nhds_one.mpr
  intro U hU
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois U).mp hU
  have : Finite L := Module.finite_of_finite k
  obtain ⟨i, hi⟩ := geometric_generates k L (AlgEquiv.restrictNormalHom L σ)
  refine ⟨(geometric k (AlgebraicClosure k)) ^ (i.val : ℤ),
    ⟨Multiplicative.ofAdd (i.val : ℤ), rfl⟩, hL ?_⟩
  apply (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff _ L).mpr
  rw [map_div, map_zpow]
  change ((finiteRestriction k L.toIntermediateField) (geometricFrobenius k)) ^ (i.val : ℤ) /
    AlgEquiv.restrictNormalHom L σ = 1
  rw [geometric_restrict, zpow_natCast, hi, div_self']

private theorem fromProfinite_surjective : Function.Surjective (fromProfinite k) := by
  let : T2Space (Field.absoluteGaloisGroup k) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure k/k))
  have hd : DenseRange (fun n : Degree => (geometricFrobenius k) ^ n.toAdd) :=
    geometric_dense k
  have hs : Set.range (fun n : Degree => (geometricFrobenius k) ^ n.toAdd) ⊆
      Set.range (fromProfinite k) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨frobenius n, fromProfinite_eta k n⟩
  have hr : IsClosed (Set.range (fromProfinite k)) :=
    (fromProfinite k).continuous.isClosedMap.isClosed_range
  intro σ
  have hσ := closure_mono hs (hd σ)
  rw [closure_eq_iff_isClosed.mpr hr] at hσ
  exact hσ

private theorem fromProfinite_restrict
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) (x : ProfiniteIntegers) :
    component k L x = finiteRestriction k L.toIntermediateField (fromProfinite k x) := by
  exact (congrArg (fun z => z.val (op L))
    ((InfiniteGalois.continuousMulEquivToLimit k (AlgebraicClosure k)).apply_symm_apply
      (toGaloisLimit k x))).symm

private theorem liftFinite_eq_one {H : Type v} [Group H] [Finite H] [TopologicalSpace H]
    (f : Degree →* H) (x : ProfiniteIntegers) (hx : liftFinite f x = 1) :
    x.val (finiteKernel f) = 1 := by
  apply (QuotientGroup.injective_lift_iff f.ker f (by intro a ha; exact ha)).mpr rfl
  exact hx.trans (map_one _).symm

private theorem fromProfinite_injective : Function.Injective (fromProfinite k) := by
  apply (injective_iff_map_eq_one (fromProfinite k)).mpr
  intro x hx
  apply Subtype.ext
  funext N
  let n := N.toSubgroup.index
  have hn : n ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨L, hL⟩ := exists_intermediate_degree k n hn
  let f := zpowersHom (Gal(L/k)) (geometric k L)
  have hc : liftFinite f x = 1 := by
    change component k L x = 1
    rw [fromProfinite_restrict, hx, map_one]
    rfl
  have hzero := liftFinite_eq_one f x hc
  have hle : finiteKernel f ≤ N := by
    intro m hm
    have hm' : (geometric k L) ^ m.toAdd = 1 := hm
    have horder : orderOf (geometric k L) = n := by
      have : Finite L := Module.finite_of_finite k
      exact (geometric_order k L).trans hL
    have hdiv : (n : ℤ) ∣ m.toAdd := by
      rw [← horder]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hm'
    obtain ⟨t, ht⟩ := hdiv
    have hmem := N.toSubgroup.pow_index_mem (Multiplicative.ofAdd (1 : ℤ))
    have heq : m = ((Multiplicative.ofAdd (1 : ℤ)) ^ n) ^ t := by
      apply Multiplicative.ext
      simp [ht, mul_comm]
    rw [heq]
    exact N.toSubgroup.zpow_mem hmem t
  have hcompat := x.property (homOfLE hle)
  change x.val N = 1
  calc
    x.val N = (ProfiniteCompletion.diagram (GrpCat.of Degree)).map (homOfLE hle)
        (x.val (finiteKernel f)) := hcompat.symm
    _ = (ProfiniteCompletion.diagram (GrpCat.of Degree)).map (homOfLE hle) 1 :=
      congrArg _ hzero
    _ = 1 := map_one ((ProfiniteCompletion.diagram (GrpCat.of Degree)).map (homOfLE hle)).hom

/-- The actual finite-field absolute Galois group, normalized so geometric
Frobenius corresponds to positive one, as a topological group of profinite
integers. Its construction uses finite Galois restrictions in every universe. -/
def profiniteEquivalence :
    Field.absoluteGaloisGroup k ≃ₜ* ProfiniteIntegers := by
  let : T2Space (Field.absoluteGaloisGroup k) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure k/k))
  exact
    ({ Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofBijective (fromProfinite k)
          ⟨fromProfinite_injective k, fromProfinite_surjective k⟩)
        (fromProfinite k).continuous with
      map_mul' := (fromProfinite k).map_mul } :
        ProfiniteIntegers ≃ₜ* Field.absoluteGaloisGroup k).symm

/-- A directly composable continuous homomorphism for a later residue map. -/
def toProfiniteIntegers : Field.absoluteGaloisGroup k →ₜ* ProfiniteIntegers :=
  ContinuousMonoidHom.toContinuousMonoidHom (profiniteEquivalence k)

theorem profiniteEquivalence_symm_frobenius (n : Degree) :
    (profiniteEquivalence k).symm (frobenius n) = (geometricFrobenius k) ^ n.toAdd :=
  fromProfinite_eta k n

theorem profiniteEquivalence_geometric :
    profiniteEquivalence k (geometricFrobenius k) = frobenius (Multiplicative.ofAdd 1) := by
  apply (profiniteEquivalence k).symm.injective
  rw [ContinuousMulEquiv.symm_apply_apply, profiniteEquivalence_symm_frobenius]
  simp

theorem profiniteEquivalence_arithmetic :
    profiniteEquivalence k (arithmeticFrobenius k) =
      frobenius (Multiplicative.ofAdd (-1)) := by
  have h : arithmeticFrobenius k = (geometricFrobenius k)⁻¹ := by
    simp [geometricFrobenius]
  rw [h, map_inv, profiniteEquivalence_geometric, ← map_inv]
  rfl

/-- The complete comparison target: both topological directions, normalization,
the actual power action, and the laws for all finite intermediate fields. -/
theorem frobeniusComparison : FrobeniusComparison.{u} := by
  intro k _ _
  refine ⟨⟨profiniteEquivalence k, profiniteEquivalence_geometric k,
    profiniteEquivalence_arithmetic k⟩, ?_, ?_⟩
  · exact arithmetic_apply k (AlgebraicClosure k)
  · intro L _
    have : Finite L := Module.finite_of_finite k
    exact ⟨arithmetic_restrict k L, geometric_restrict k L,
      arithmetic_apply k L, arithmetic_order k L, geometric_order k L,
      arithmetic_generates k L, geometric_generates k L⟩

end Langlands.Galois.FiniteField
