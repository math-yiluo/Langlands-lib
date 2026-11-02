import Langlands.AlgebraicGeometry.GroupoidCoactionGenericEvaluation
import Langlands.AlgebraicGeometry.GroupoidCoactionPushout
import Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelationQuotient
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Finite effective covers of ring étale equivalence relations and their quotients

A `FiniteEffectiveCover t` of a ring étale equivalence relation `t : B →+* C` packages the cover
data used by `GroupoidCoaction.exists_genericEvaluation`: a finite `B`-algebra `D` with
`Spec D → Spec B` surjective, a covering relation `td : D →+* P` that is source-cartesian over
`t` (`P ≅ D ⊗[B] C`), such that `D` is faithfully flat over the invariant ring `A` of `td` and
`P ≅ D ⊗[A] D`. The constructor `FiniteEffectiveCover.quotient` restricts such a cover to the
quotient relation `B ⧸ I → C ⧸ I C` for an invariant ideal `I`, with covering rings `D ⧸ I D`
and `P ⧸ I P`.
-/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

/-- A finite effective cover of the ring étale equivalence relation `t : B →+* C`: a finite
`B`-algebra `D` with `Spec D → Spec B` surjective and a covering relation `td : D →+* P` with
`P ≅ D ⊗[B] C` compatibly with `t` (source-cartesian), such that `D` is faithfully flat over the
invariant ring `A = invariantRing td` and `ε : P ≅ D ⊗[A] D` sends `td d` to `1 ⊗ d`. These are
exactly the cover hypotheses of `exists_genericEvaluation`. -/
structure FiniteEffectiveCover (t : B →+* C) where
  /-- The covering ring. -/
  D : Type u
  /-- The ring of the covering relation. -/
  P : Type u
  [commRingD : CommRing D]
  [commRingP : CommRing P]
  [algebraBD : Algebra B D]
  [algebraDP : Algebra D P]
  [algebraBP : Algebra B P]
  [isScalarTower : IsScalarTower B D P]
  /-- The target map of the covering relation. -/
  td : D →+* P
  /-- The covering relation is a ring étale equivalence relation. -/
  relation : RingEtaleEquivalenceRelation td
  /-- The covering relation is source-cartesian over `t`. -/
  e : P ≃ₐ[D] D ⊗[B] C
  /-- Compatibility of `e` with the target maps. -/
  cartesian : (cartesianBaseMap e).comp t = td.comp (algebraMap B D)
  [faithfullyFlat : Module.FaithfullyFlat (invariantRing td) D]
  /-- The covering relation is the tensor square over the invariant ring. -/
  ε : P ≃ₐ[D] D ⊗[invariantRing td] D
  /-- Compatibility of `ε` with the target map. -/
  ε_target : ∀ d : D, ε (td d) = (1 : D) ⊗ₜ[invariantRing td] d
  [finite : Module.Finite B D]
  /-- `Spec D → Spec B` is surjective. -/
  comap_surjective : Function.Surjective (PrimeSpectrum.comap (algebraMap B D))

attribute [instance] FiniteEffectiveCover.commRingD FiniteEffectiveCover.commRingP
  FiniteEffectiveCover.algebraBD FiniteEffectiveCover.algebraDP FiniteEffectiveCover.algebraBP
  FiniteEffectiveCover.isScalarTower FiniteEffectiveCover.faithfullyFlat
  FiniteEffectiveCover.finite

namespace FiniteEffectiveCover

variable {t : B →+* C} (X : FiniteEffectiveCover t)

/-- `exists_genericEvaluation` for a finite effective cover. -/
theorem exists_genericEvaluation (hE : RingEtaleEquivalenceRelation t)
    [IsNoetherianRing B] [IsReduced B] [Nontrivial B]
    (H : Type u) [AddCommGroup H] [Module B H] [Module.Finite B H]
    (θH : GroupoidCoaction t H) :
    ∃ (q : Ideal (invariantRing X.td)) (_ : q.IsPrime) (r : ℕ) (_ : 0 < r)
      (a : Fin r → invariantRing X.td ⧸ q) (I : Ideal B),
      I ≠ ⊥ ∧ IsInvariantIdeal t I ∧
      Module.Finite B (X.D ⊗[invariantRing X.td] (invariantRing X.td ⧸ q)) ∧
      I ≤ (Module.annihilator B (LinearMap.ker (genericEvaluation B X.td q a H))).radical ∧
      I ≤ (Module.annihilator B
        ((Fin r → H) ⧸ LinearMap.range (genericEvaluation B X.td q a H))).radical :=
  GroupoidCoaction.exists_genericEvaluation hE X.relation X.e X.cartesian X.ε X.ε_target
    X.comap_surjective H θH

section Quotient

variable (I : Ideal B)

/-- The ideal `I D` of the covering ring. -/
abbrev coverIdeal : Ideal X.D := I.map (algebraMap B X.D)

/-- The ideal `I P` of the covering relation ring, generated through the source map. -/
abbrev relationIdeal : Ideal X.P := (X.coverIdeal I).map (algebraMap X.D X.P)

/-- For an invariant ideal `I`, the source and target extensions of `I D` to `P` agree. -/
lemma relationIdeal_eq_map_td (hI : IsInvariantIdeal t I) :
    X.relationIdeal I = (X.coverIdeal I).map X.td := by
  simp only [relationIdeal, coverIdeal, Ideal.map_map]
  rw [← cartesianBaseMap_comp_source X.e, ← Ideal.map_map, ← hI, Ideal.map_map, X.cartesian]

lemma map_le_comap_cartesianBaseMap :
    I.map (algebraMap B C) ≤ (X.relationIdeal I).comap (cartesianBaseMap X.e) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, cartesianBaseMap_comp_source, ← Ideal.map_map]

variable {I}

/-- The target map of the quotient covering relation `D ⧸ I D → P ⧸ I P`. -/
def quotientTd (hI : IsInvariantIdeal t I) : X.D ⧸ X.coverIdeal I →+* X.P ⧸ X.relationIdeal I :=
  RingEtaleEquivalenceRelation.quotientTarget (X.coverIdeal I) (X.relationIdeal_eq_map_td I hI)

@[simp]
lemma quotientTd_mk (hI : IsInvariantIdeal t I) (d : X.D) :
    X.quotientTd hI (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (X.td d) :=
  rfl

lemma quotient_relation (hI : IsInvariantIdeal t I) :
    RingEtaleEquivalenceRelation (X.quotientTd hI) :=
  X.relation.quotient (X.coverIdeal I) (X.relationIdeal_eq_map_td I hI)

lemma algebraMap_quotient_mk (d : X.D) :
    algebraMap (X.D ⧸ X.coverIdeal I) (X.P ⧸ X.relationIdeal I) (Ideal.Quotient.mk _ d) =
      Ideal.Quotient.mk _ (algebraMap X.D X.P d) :=
  Ideal.Quotient.algebraMap_quotient_map_quotient d

/-- Reduction of invariants: the invariant ring of `td` maps to that of the quotient relation. -/
def quotientInvariantMap (hI : IsInvariantIdeal t I) :
    invariantRing X.td →+* invariantRing (X.quotientTd hI) :=
  ((Ideal.Quotient.mk (X.coverIdeal I)).comp (invariantRing X.td).subtype).codRestrict _
    fun a => by
      change X.quotientTd hI (Ideal.Quotient.mk _ (a : X.D)) =
        algebraMap _ _ (Ideal.Quotient.mk (X.coverIdeal I) (a : X.D))
      rw [quotientTd_mk, algebraMap_quotient_mk]
      exact congrArg (Ideal.Quotient.mk _) a.property

@[simp]
lemma quotientInvariantMap_coe (hI : IsInvariantIdeal t I) (a : invariantRing X.td) :
    (X.quotientInvariantMap hI a : X.D ⧸ X.coverIdeal I) = Ideal.Quotient.mk _ (a : X.D) :=
  rfl

/-- Every invariant of the quotient relation lifts to an invariant of `td`. -/
lemma quotientInvariantMap_surjective (hI : IsInvariantIdeal t I) :
    Function.Surjective (X.quotientInvariantMap hI) := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hy' : Ideal.Quotient.mk (X.relationIdeal I) (X.td x) =
      Ideal.Quotient.mk (X.relationIdeal I) (algebraMap X.D X.P x) := by
    rw [← X.quotientTd_mk hI, ← X.algebraMap_quotient_mk]
    exact hy
  have hmem : X.td x - algebraMap X.D X.P x ∈ (X.coverIdeal I).map X.td := by
    rw [← X.relationIdeal_eq_map_td I hI]
    exact Ideal.Quotient.eq.mp hy'
  let ρ : X.D ⊗[invariantRing X.td] X.D →ₐ[invariantRing X.td]
      X.D ⊗[invariantRing X.td] (X.D ⧸ X.coverIdeal I) :=
    Algebra.TensorProduct.map (AlgHom.id _ X.D) (Ideal.Quotient.mkₐ _ (X.coverIdeal I))
  have hρ : ∀ d d' : X.D, ρ (d ⊗ₜ d') = d ⊗ₜ Ideal.Quotient.mk (X.coverIdeal I) d' :=
    fun d d' => rfl
  have hker : (X.coverIdeal I).map X.td ≤
      RingHom.ker ((ρ : X.D ⊗[invariantRing X.td] X.D →+*
          X.D ⊗[invariantRing X.td] (X.D ⧸ X.coverIdeal I)).comp
        (X.ε : X.P →+* X.D ⊗[invariantRing X.td] X.D)) := by
    refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change ρ (X.ε (X.td j)) = 0
    rw [X.ε_target, hρ, Ideal.Quotient.eq_zero_iff_mem.mpr hj, tmul_zero]
  have h2 : ρ (X.ε (X.td x)) = ρ (X.ε (algebraMap X.D X.P x)) := by
    have h0 := hker hmem
    rw [RingHom.mem_ker] at h0
    change ρ (X.ε (X.td x - algebraMap X.D X.P x)) = 0 at h0
    rw [map_sub, map_sub, sub_eq_zero] at h0
    exact h0
  have h1 : (1 : X.D) ⊗ₜ[invariantRing X.td] (Ideal.Quotient.mk (X.coverIdeal I) x) =
      x ⊗ₜ[invariantRing X.td] (1 : X.D ⧸ X.coverIdeal I) := by
    rw [X.ε_target, AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, hρ, hρ, map_one] at h2
    exact h2
  let S : Submodule (invariantRing X.td) (X.D ⧸ X.coverIdeal I) :=
    LinearMap.range (Algebra.linearMap (invariantRing X.td) (X.D ⧸ X.coverIdeal I))
  have h3 : (1 : X.D) ⊗ₜ[invariantRing X.td] S.mkQ (Ideal.Quotient.mk (X.coverIdeal I) x) =
      0 := by
    have h4 := congrArg (LinearMap.lTensor X.D S.mkQ) h1
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul] at h4
    rw [h4, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).mpr ⟨1, by simp⟩,
      tmul_zero]
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h3
  obtain ⟨a, ha⟩ := h3
  exact ⟨a, Subtype.ext ha⟩

/-- The kernel of the reduction of invariants. -/
abbrev invariantKernel (hI : IsInvariantIdeal t I) : Ideal (invariantRing X.td) :=
  RingHom.ker (X.quotientInvariantMap hI)

lemma mem_invariantKernel (hI : IsInvariantIdeal t I) (a : invariantRing X.td) :
    a ∈ X.invariantKernel hI ↔ (a : X.D) ∈ X.coverIdeal I := by
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Descent of the invariant ideal `I D`: it is generated by its invariant elements. This is the
faithfully flat descent step; it uses flatness of `D` over the invariant ring and `ε`. -/
lemma coverIdeal_eq_map_invariantKernel (hI : IsInvariantIdeal t I) :
    X.coverIdeal I = (X.invariantKernel hI).map (algebraMap (invariantRing X.td) X.D) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    let ρ : X.D ⊗[invariantRing X.td] X.D →ₐ[invariantRing X.td]
        (X.D ⧸ X.coverIdeal I) ⊗[invariantRing X.td] X.D :=
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ _ (X.coverIdeal I)) (AlgHom.id _ X.D)
    have hρ : ∀ d d' : X.D, ρ (d ⊗ₜ d') = Ideal.Quotient.mk (X.coverIdeal I) d ⊗ₜ d' :=
      fun d d' => rfl
    have hx' : X.td x ∈ X.relationIdeal I := by
      rw [X.relationIdeal_eq_map_td I hI]
      exact Ideal.mem_map_of_mem _ hx
    have hker : X.relationIdeal I ≤
        RingHom.ker ((ρ : X.D ⊗[invariantRing X.td] X.D →+*
            (X.D ⧸ X.coverIdeal I) ⊗[invariantRing X.td] X.D).comp
          (X.ε : X.P →+* X.D ⊗[invariantRing X.td] X.D)) := by
      refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change ρ (X.ε (algebraMap X.D X.P j)) = 0
      rw [AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, hρ, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_tmul]
    have h1 : (1 : X.D ⧸ X.coverIdeal I) ⊗ₜ[invariantRing X.td] x = 0 := by
      have h0 := hker hx'
      rw [RingHom.mem_ker] at h0
      change ρ (X.ε (X.td x)) = 0 at h0
      rwa [X.ε_target, hρ, map_one] at h0
    let f : invariantRing X.td →ₗ[invariantRing X.td] X.D ⧸ X.coverIdeal I :=
      Algebra.linearMap _ _
    have hexact : Function.Exact (X.invariantKernel hI).subtype f := by
      intro y
      constructor
      · intro hy
        refine ⟨⟨y, ?_⟩, rfl⟩
        rw [X.mem_invariantKernel hI, ← Ideal.Quotient.eq_zero_iff_mem]
        exact hy
      · rintro ⟨z, rfl⟩
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ((X.mem_invariantKernel hI z).mp z.property)
    have hex := Module.Flat.rTensor_exact X.D hexact
    obtain ⟨z, hz⟩ := (hex ((1 : invariantRing X.td) ⊗ₜ[invariantRing X.td] x)).mp (by
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
      exact h1)
    have hmem : ∀ w : X.invariantKernel hI ⊗[invariantRing X.td] X.D,
        TensorProduct.lid (invariantRing X.td) X.D
            ((X.invariantKernel hI).subtype.rTensor X.D w) ∈
          (X.invariantKernel hI).map (algebraMap (invariantRing X.td) X.D) := by
      intro w
      induction w with
      | tmul i d =>
        rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Submodule.subtype_apply,
          Algebra.smul_def]
        exact Ideal.mul_mem_right d _ (Ideal.mem_map_of_mem _ i.2)
      | add w w' hw hw' =>
        rw [map_add, map_add]
        exact add_mem hw hw'
    have := hmem z
    rwa [hz, TensorProduct.lid_tmul, one_smul] at this
  · refine Ideal.map_le_iff_le_comap.mpr fun y hy => ?_
    exact (X.mem_invariantKernel hI y).mp hy

/-- The reduction of invariants identifies `A ⧸ (A ∩ I D)` with the invariant ring of the
quotient relation. -/
noncomputable def quotientInvariantEquiv (hI : IsInvariantIdeal t I) :
    (invariantRing X.td ⧸ X.invariantKernel hI) ≃+* invariantRing (X.quotientTd hI) :=
  RingHom.quotientKerEquivOfSurjective (X.quotientInvariantMap_surjective hI)

lemma quotientInvariantEquiv_symm_apply (hI : IsInvariantIdeal t I) (w : invariantRing X.td) :
    (X.quotientInvariantEquiv hI).symm (X.quotientInvariantMap hI w) =
      Ideal.Quotient.mk (X.invariantKernel hI) w :=
  RingHom.quotientKerEquivOfSurjective_symm_apply _ w

/-- `D ⧸ I D` is the base change of `D` along `A → A ⧸ (A ∩ I D)`. -/
noncomputable def quotientBaseChangeEquiv (hI : IsInvariantIdeal t I) :
    (invariantRing X.td ⧸ X.invariantKernel hI) ⊗[invariantRing X.td] X.D ≃+*
      X.D ⧸ X.coverIdeal I :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor X.D
      (X.invariantKernel hI)).symm.toRingEquiv.trans
    (Ideal.quotEquivOfEq (X.coverIdeal_eq_map_invariantKernel hI).symm)

lemma quotientBaseChangeEquiv_one_tmul (hI : IsInvariantIdeal t I) (d : X.D) :
    X.quotientBaseChangeEquiv hI (1 ⊗ₜ d) = Ideal.Quotient.mk (X.coverIdeal I) d := by
  have hψ : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor X.D
      (X.invariantKernel hI)).symm (1 ⊗ₜ d) = Ideal.Quotient.mk _ d := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  change Ideal.quotEquivOfEq (X.coverIdeal_eq_map_invariantKernel hI).symm
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor X.D
      (X.invariantKernel hI)).symm (1 ⊗ₜ d)) = _
  rw [hψ, Ideal.quotEquivOfEq_mk]

lemma algebraMap_quotient_eq_comp (hI : IsInvariantIdeal t I) :
    algebraMap (invariantRing (X.quotientTd hI)) (X.D ⧸ X.coverIdeal I) =
      (((X.quotientBaseChangeEquiv hI : (invariantRing X.td ⧸ X.invariantKernel hI) ⊗[
          invariantRing X.td] X.D →+* X.D ⧸ X.coverIdeal I)).comp
        (algebraMap (invariantRing X.td ⧸ X.invariantKernel hI)
          ((invariantRing X.td ⧸ X.invariantKernel hI) ⊗[invariantRing X.td] X.D))).comp
        ((X.quotientInvariantEquiv hI).symm : invariantRing (X.quotientTd hI) →+*
          invariantRing X.td ⧸ X.invariantKernel hI) := by
  refine RingHom.ext fun y => ?_
  obtain ⟨w, rfl⟩ := X.quotientInvariantMap_surjective hI y
  rw [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom,
    RingEquiv.coe_toRingHom, quotientInvariantEquiv_symm_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact ((congrArg (X.quotientBaseChangeEquiv hI)
    (Algebra.TensorProduct.tmul_one_eq_one_tmul w)).trans
      (X.quotientBaseChangeEquiv_one_tmul hI w)).symm

lemma faithfullyFlat_algebraMap_quotient_tensor (hI : IsInvariantIdeal t I) :
    RingHom.FaithfullyFlat (R := invariantRing X.td ⧸ X.invariantKernel hI)
      (S := (invariantRing X.td ⧸ X.invariantKernel hI) ⊗[invariantRing X.td] X.D)
      (algebraMap _ _) :=
  RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

/-- The quotient covering ring is faithfully flat over the invariant ring of the quotient
relation: it is the base change of `D` along `A → A ⧸ (A ∩ I D)`. -/
lemma quotient_faithfullyFlat (hI : IsInvariantIdeal t I) :
    Module.FaithfullyFlat (invariantRing (X.quotientTd hI)) (X.D ⧸ X.coverIdeal I) := by
  have h₂ := RingHom.FaithfullyFlat.of_bijective
    (R := (invariantRing X.td ⧸ X.invariantKernel hI) ⊗[invariantRing X.td] X.D)
    (S := X.D ⧸ X.coverIdeal I) (f := (X.quotientBaseChangeEquiv hI).toRingHom)
    (X.quotientBaseChangeEquiv hI).bijective
  have h₃ := RingHom.FaithfullyFlat.of_bijective
    (f := (X.quotientInvariantEquiv hI).symm.toRingHom) (X.quotientInvariantEquiv hI).symm.bijective
  have h :
      (algebraMap (invariantRing (X.quotientTd hI)) (X.D ⧸ X.coverIdeal I)).FaithfullyFlat := by
    rw [X.algebraMap_quotient_eq_comp hI]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _ h₃
      (RingHom.FaithfullyFlat.stableUnderComposition _ _
        (X.faithfullyFlat_algebraMap_quotient_tensor hI) h₂)
  exact RingHom.faithfullyFlat_algebraMap_iff.mp h

/-- The reduction `D ⊗[A] D → D' ⊗[A'] D'` of tensor squares, `D' = D ⧸ I D`, `A'` the invariant
ring of the quotient relation. -/
noncomputable def quotientTensorMap (hI : IsInvariantIdeal t I) :
    X.D ⊗[invariantRing X.td] X.D →+*
      (X.D ⧸ X.coverIdeal I) ⊗[invariantRing (X.quotientTd hI)] (X.D ⧸ X.coverIdeal I) :=
  tensorRingLift
    (Algebra.TensorProduct.includeLeftRingHom.comp (Ideal.Quotient.mk (X.coverIdeal I)))
    ((Algebra.TensorProduct.includeRight :
        (X.D ⧸ X.coverIdeal I) →ₐ[invariantRing (X.quotientTd hI)]
          (X.D ⧸ X.coverIdeal I) ⊗[invariantRing (X.quotientTd hI)]
            (X.D ⧸ X.coverIdeal I)).toRingHom.comp
      (Ideal.Quotient.mk (X.coverIdeal I)))
    (by
      refine RingHom.ext fun a => ?_
      change algebraMap (invariantRing (X.quotientTd hI)) (X.D ⧸ X.coverIdeal I)
          (X.quotientInvariantMap hI a) ⊗ₜ 1 =
        1 ⊗ₜ algebraMap (invariantRing (X.quotientTd hI)) (X.D ⧸ X.coverIdeal I)
          (X.quotientInvariantMap hI a)
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul _)

lemma quotientTensorMap_tmul (hI : IsInvariantIdeal t I) (d d' : X.D) :
    X.quotientTensorMap hI (d ⊗ₜ d') =
      Ideal.Quotient.mk (X.coverIdeal I) d ⊗ₜ Ideal.Quotient.mk (X.coverIdeal I) d' := by
  rw [quotientTensorMap, tensorRingLift_tmul]
  change (Ideal.Quotient.mk (X.coverIdeal I) d ⊗ₜ (1 : X.D ⧸ X.coverIdeal I)) *
    ((1 : X.D ⧸ X.coverIdeal I) ⊗ₜ Ideal.Quotient.mk (X.coverIdeal I) d') = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The inverse of the tensor-square map of the quotient relation. -/
noncomputable def quotientSquareInv (hI : IsInvariantIdeal t I) :
    X.P ⧸ X.relationIdeal I →+*
      (X.D ⧸ X.coverIdeal I) ⊗[invariantRing (X.quotientTd hI)] (X.D ⧸ X.coverIdeal I) :=
  Ideal.Quotient.lift (X.relationIdeal I)
    ((X.quotientTensorMap hI).comp (X.ε : X.P →+* X.D ⊗[invariantRing X.td] X.D))
    (by
      have hle : X.relationIdeal I ≤
          RingHom.ker ((X.quotientTensorMap hI).comp
            (X.ε : X.P →+* X.D ⊗[invariantRing X.td] X.D)) := by
        refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change X.quotientTensorMap hI (X.ε (algebraMap X.D X.P j)) = 0
        rw [AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, quotientTensorMap_tmul, Ideal.Quotient.eq_zero_iff_mem.mpr hj,
          zero_tmul]
      exact fun p hp => hle hp)

lemma quotientSquareInv_mk (hI : IsInvariantIdeal t I) (p : X.P) :
    X.quotientSquareInv hI (Ideal.Quotient.mk _ p) = X.quotientTensorMap hI (X.ε p) :=
  rfl

lemma ε_symm_tmul (d d' : X.D) :
    X.ε.symm (d ⊗ₜ d') = algebraMap X.D X.P d * X.td d' := by
  rw [AlgEquiv.symm_apply_eq, map_mul, AlgEquiv.commutes, X.ε_target,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The tensor-square map of the quotient relation is bijective. -/
lemma quotient_relationTensorHom_bijective (hI : IsInvariantIdeal t I) :
    Function.Bijective (relationTensorHom (X.quotientTd hI)) := by
  constructor
  · refine Function.LeftInverse.injective (g := X.quotientSquareInv hI) fun z => ?_
    induction z with
    | tmul y y' =>
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective y'
      rw [relationTensorHom_tmul, algebraMap_quotient_mk, quotientTd_mk,
        ← map_mul (Ideal.Quotient.mk (X.relationIdeal I)), quotientSquareInv_mk,
        ← ε_symm_tmul, AlgEquiv.apply_symm_apply, quotientTensorMap_tmul]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  · intro w
    refine ⟨X.quotientSquareInv hI w, ?_⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨u, rfl⟩ := X.ε.symm.surjective p
    rw [quotientSquareInv_mk, AlgEquiv.apply_symm_apply]
    induction u with
    | tmul d d' =>
      rw [quotientTensorMap_tmul, relationTensorHom_tmul, algebraMap_quotient_mk, quotientTd_mk,
        ← map_mul (Ideal.Quotient.mk (X.relationIdeal I)), ε_symm_tmul]
    | add u u' hu hu' =>
      simp only [map_add, hu, hu']

/-- The tensor-square equivalence of the quotient relation. -/
noncomputable def quotientε (hI : IsInvariantIdeal t I) :
    (X.P ⧸ X.relationIdeal I) ≃ₐ[X.D ⧸ X.coverIdeal I]
      (X.D ⧸ X.coverIdeal I) ⊗[invariantRing (X.quotientTd hI)] (X.D ⧸ X.coverIdeal I) :=
  (AlgEquiv.ofBijective (relationTensorHom (X.quotientTd hI))
    (X.quotient_relationTensorHom_bijective hI)).symm

lemma quotientε_target (hI : IsInvariantIdeal t I) (d : X.D ⧸ X.coverIdeal I) :
    X.quotientε hI (X.quotientTd hI d) = (1 : X.D ⧸ X.coverIdeal I) ⊗ₜ d := by
  rw [quotientε, AlgEquiv.symm_apply_eq, AlgEquiv.ofBijective_apply, relationTensorHom_tmul,
    map_one, one_mul]

variable (I)

/-- The reduction `D ⊗[B] C → D' ⊗[B ⧸ I] C'` of the cartesian tensor product,
`D' = D ⧸ I D`, `C' = C ⧸ I C`. -/
noncomputable def quotientCartesianTensorMap :
    X.D ⊗[B] C →+* (X.D ⧸ X.coverIdeal I) ⊗[B ⧸ I] (C ⧸ I.map (algebraMap B C)) :=
  tensorRingLift
    (Algebra.TensorProduct.includeLeftRingHom.comp (Ideal.Quotient.mk (X.coverIdeal I)))
    ((Algebra.TensorProduct.includeRight :
        (C ⧸ I.map (algebraMap B C)) →ₐ[B ⧸ I]
          (X.D ⧸ X.coverIdeal I) ⊗[B ⧸ I] (C ⧸ I.map (algebraMap B C))).toRingHom.comp
      (Ideal.Quotient.mk (I.map (algebraMap B C))))
    (by
      refine RingHom.ext fun b => ?_
      change algebraMap (B ⧸ I) (X.D ⧸ X.coverIdeal I) (Ideal.Quotient.mk I b) ⊗ₜ 1 =
        1 ⊗ₜ algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C)) (Ideal.Quotient.mk I b)
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul _)

lemma quotientCartesianTensorMap_tmul (d : X.D) (c : C) :
    X.quotientCartesianTensorMap I (d ⊗ₜ c) =
      Ideal.Quotient.mk (X.coverIdeal I) d ⊗ₜ Ideal.Quotient.mk (I.map (algebraMap B C)) c := by
  rw [quotientCartesianTensorMap, tensorRingLift_tmul]
  change (Ideal.Quotient.mk (X.coverIdeal I) d ⊗ₜ (1 : C ⧸ I.map (algebraMap B C))) *
    ((1 : X.D ⧸ X.coverIdeal I) ⊗ₜ Ideal.Quotient.mk (I.map (algebraMap B C)) c) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

lemma e_symm_tmul (d : X.D) (c : C) :
    X.e.symm (d ⊗ₜ c) = algebraMap X.D X.P d * cartesianBaseMap X.e c := by
  rw [AlgEquiv.symm_apply_eq, map_mul, AlgEquiv.commutes, cartesianBaseMap_apply,
    AlgEquiv.apply_symm_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The reduction of `e`: the map `P ⧸ I P → D' ⊗[B ⧸ I] C'`. -/
noncomputable def quotientCartesianHom :
    X.P ⧸ X.relationIdeal I →+*
      (X.D ⧸ X.coverIdeal I) ⊗[B ⧸ I] (C ⧸ I.map (algebraMap B C)) :=
  Ideal.Quotient.lift (X.relationIdeal I)
    ((X.quotientCartesianTensorMap I).comp (X.e : X.P →+* X.D ⊗[B] C))
    (by
      have hle : X.relationIdeal I ≤
          RingHom.ker ((X.quotientCartesianTensorMap I).comp (X.e : X.P →+* X.D ⊗[B] C)) := by
        refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change X.quotientCartesianTensorMap I (X.e (algebraMap X.D X.P j)) = 0
        rw [AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, quotientCartesianTensorMap_tmul,
          Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_tmul]
      exact fun p hp => hle hp)

lemma quotientCartesianHom_mk (p : X.P) :
    X.quotientCartesianHom I (Ideal.Quotient.mk _ p) =
      X.quotientCartesianTensorMap I (X.e p) :=
  rfl

/-- The inverse map `D' ⊗[B ⧸ I] C' → P ⧸ I P`. -/
noncomputable def quotientCartesianInv :
    (X.D ⧸ X.coverIdeal I) ⊗[B ⧸ I] (C ⧸ I.map (algebraMap B C)) →+*
      X.P ⧸ X.relationIdeal I :=
  tensorRingLift (algebraMap (X.D ⧸ X.coverIdeal I) (X.P ⧸ X.relationIdeal I))
    (Ideal.quotientMap (X.relationIdeal I) (cartesianBaseMap X.e)
      (X.map_le_comap_cartesianBaseMap I))
    (by
      refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
      change Ideal.Quotient.mk (X.relationIdeal I) (algebraMap X.D X.P (algebraMap B X.D b)) =
        Ideal.Quotient.mk (X.relationIdeal I) (cartesianBaseMap X.e (algebraMap B C b))
      rw [cartesianBaseMap_source])

lemma quotientCartesianInv_tmul (d : X.D) (c : C) :
    X.quotientCartesianInv I
        (Ideal.Quotient.mk (X.coverIdeal I) d ⊗ₜ Ideal.Quotient.mk (I.map (algebraMap B C)) c) =
      Ideal.Quotient.mk (X.relationIdeal I) (algebraMap X.D X.P d * cartesianBaseMap X.e c) := by
  rw [quotientCartesianInv, tensorRingLift_tmul, algebraMap_quotient_mk, Ideal.quotientMap_mk,
    map_mul]

lemma quotientCartesianInv_comp_hom :
    (X.quotientCartesianInv I).comp (X.quotientCartesianHom I) = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
  obtain ⟨u, rfl⟩ := X.e.symm.surjective p
  change X.quotientCartesianInv I (X.quotientCartesianHom I (Ideal.Quotient.mk _ (X.e.symm u))) =
    Ideal.Quotient.mk _ (X.e.symm u)
  rw [quotientCartesianHom_mk, AlgEquiv.apply_symm_apply]
  induction u with
  | tmul d c => rw [quotientCartesianTensorMap_tmul, quotientCartesianInv_tmul, e_symm_tmul]
  | add u u' hu hu' => simp only [map_add, hu, hu']

lemma quotientCartesianHom_comp_inv :
    (X.quotientCartesianHom I).comp (X.quotientCartesianInv I) = RingHom.id _ := by
  refine RingHom.ext fun z => ?_
  change X.quotientCartesianHom I (X.quotientCartesianInv I z) = z
  induction z with
  | tmul y y' =>
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y'
    rw [quotientCartesianInv_tmul, ← e_symm_tmul, quotientCartesianHom_mk,
      AlgEquiv.apply_symm_apply, quotientCartesianTensorMap_tmul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- The quotient covering relation is source-cartesian over the quotient relation:
`P ⧸ I P ≅ (D ⧸ I D) ⊗[B ⧸ I] (C ⧸ I C)`. -/
noncomputable def quotientEquiv :
    (X.P ⧸ X.relationIdeal I) ≃ₐ[X.D ⧸ X.coverIdeal I]
      (X.D ⧸ X.coverIdeal I) ⊗[B ⧸ I] (C ⧸ I.map (algebraMap B C)) :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom (X.quotientCartesianHom I) (X.quotientCartesianInv I)
      (X.quotientCartesianHom_comp_inv I) (X.quotientCartesianInv_comp_hom I))
    (fun y => by
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
      change X.quotientCartesianHom I (algebraMap (X.D ⧸ X.coverIdeal I)
        (X.P ⧸ X.relationIdeal I) (Ideal.Quotient.mk _ d)) = _
      rw [algebraMap_quotient_mk, quotientCartesianHom_mk, AlgEquiv.commutes,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        quotientCartesianTensorMap_tmul, map_one, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply])

lemma quotientEquiv_symm_apply
    (z : (X.D ⧸ X.coverIdeal I) ⊗[B ⧸ I] (C ⧸ I.map (algebraMap B C))) :
    (X.quotientEquiv I).symm z = X.quotientCartesianInv I z :=
  rfl

variable {I}

lemma quotient_cartesian (hI : IsInvariantIdeal t I) :
    (cartesianBaseMap (X.quotientEquiv I)).comp
        (RingEtaleEquivalenceRelation.quotientTarget I (Eq.symm hI)) =
      (X.quotientTd hI).comp (algebraMap (B ⧸ I) (X.D ⧸ X.coverIdeal I)) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
  change X.quotientCartesianInv I
      ((1 : X.D ⧸ X.coverIdeal I) ⊗ₜ Ideal.Quotient.mk (I.map (algebraMap B C)) (t b)) =
    Ideal.Quotient.mk (X.relationIdeal I) (X.td (algebraMap B X.D b))
  rw [← map_one (Ideal.Quotient.mk (X.coverIdeal I)), quotientCartesianInv_tmul, map_one,
    one_mul]
  exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun X.cartesian b)

variable (I)

lemma quotient_finite : Module.Finite (B ⧸ I) (X.D ⧸ X.coverIdeal I) :=
  Module.Finite.of_restrictScalars_finite B (B ⧸ I) (X.D ⧸ X.coverIdeal I)

lemma quotient_comap_surjective :
    Function.Surjective (PrimeSpectrum.comap (algebraMap (B ⧸ I) (X.D ⧸ X.coverIdeal I))) := by
  intro p'
  obtain ⟨Q, hQ⟩ := X.comap_surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I) p')
  have hmem : ∀ b : B, algebraMap B X.D b ∈ Q.asIdeal ↔ Ideal.Quotient.mk I b ∈ p'.asIdeal :=
    fun b => Iff.of_eq (congrArg (fun q : PrimeSpectrum B => b ∈ q.asIdeal) hQ)
  have hJQ : X.coverIdeal I ≤ Q.asIdeal := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx => (hmem x).mpr ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p'.asIdeal.zero_mem
  have hker : RingHom.ker (Ideal.Quotient.mk (X.coverIdeal I)) ≤ Q.asIdeal := by
    rw [Ideal.mk_ker]
    exact hJQ
  have := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  refine ⟨⟨Q.asIdeal.map (Ideal.Quotient.mk (X.coverIdeal I)), this⟩, ?_⟩
  ext x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (X.coverIdeal I) (algebraMap B X.D b) ∈
    Q.asIdeal.map (Ideal.Quotient.mk (X.coverIdeal I)) ↔ _
  rw [Ideal.mem_quotient_iff_mem hJQ]
  exact hmem b

/-- The `B ⧸ I`-algebra structure on `P ⧸ I P` through `D ⧸ I D`. -/
noncomputable abbrev quotientAlgebraBP : Algebra (B ⧸ I) (X.P ⧸ X.relationIdeal I) :=
  ((algebraMap (X.D ⧸ X.coverIdeal I) (X.P ⧸ X.relationIdeal I)).comp
    (algebraMap (B ⧸ I) (X.D ⧸ X.coverIdeal I))).toAlgebra

variable {I}

/-- The finite effective cover of the quotient relation `B ⧸ I → C ⧸ I C` by an invariant ideal
`I`: the covering rings are `D ⧸ I D` and `P ⧸ I P`. -/
noncomputable def quotient (hI : IsInvariantIdeal t I) :
    FiniteEffectiveCover (RingEtaleEquivalenceRelation.quotientTarget I (Eq.symm hI)) :=
  letI := X.quotientAlgebraBP I
  haveI : IsScalarTower (B ⧸ I) (X.D ⧸ X.coverIdeal I) (X.P ⧸ X.relationIdeal I) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI := X.quotient_faithfullyFlat hI
  haveI := X.quotient_finite I
  { D := X.D ⧸ X.coverIdeal I
    P := X.P ⧸ X.relationIdeal I
    td := X.quotientTd hI
    relation := X.quotient_relation hI
    e := X.quotientEquiv I
    cartesian := X.quotient_cartesian hI
    ε := X.quotientε hI
    ε_target := X.quotientε_target hI
    comap_surjective := X.quotient_comap_surjective I }

end Quotient

end FiniteEffectiveCover

end Langlands.AlgebraicGeometry.GroupoidCoaction
