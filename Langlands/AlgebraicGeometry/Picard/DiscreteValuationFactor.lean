import Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import Mathlib.RingTheory.RingHom.EssFiniteType

/-! # Discrete valuation factors of essentially finite type field maps -/

universe u v

open IsLocalRing

namespace Langlands.AlgebraicGeometry.DiscreteValuationFactor

lemma isFractionRing_of_closure_eq_top
    (D K : Type*) [CommRing D] [IsDomain D] [Field K] [Algebra D K]
    [FaithfulSMul D K]
    (h : Subfield.closure (Set.range (algebraMap D K)) = ⊤) :
    IsFractionRing D K := by
  let φ : FractionRing D →ₐ[D] K :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId D K)
      (FaithfulSMul.algebraMap_injective D K)
  have hr : φ.toRingHom.fieldRange = ⊤ := by
    rw [IsFractionRing.ringHom_fieldRange_eq_of_comp_eq
      (show φ.toRingHom.comp (algebraMap D (FractionRing D)) = algebraMap D K from
        RingHom.ext φ.commutes)]
    exact h
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofBijective φ ⟨φ.injective, RingHom.fieldRange_eq_top_iff.mp hr⟩)

/-- Finite field generators can be represented inside any valuation ring containing the base. -/
lemma exists_finiteType_subalgebra
    (A : Type u) [CommRing A] (K : Type v) [Field K] [Algebra A K]
    [Algebra.EssFiniteType A K] (V : ValuationSubring K)
    (hV : ∀ a : A, algebraMap A K a ∈ V) :
    ∃ (D : Subalgebra A K), D.FG ∧ D.toSubring ≤ V.toSubring ∧ IsFractionRing D K := by
  classical
  let s := Algebra.EssFiniteType.finset A K
  obtain ⟨a, b, hab⟩ : ∃ a b : K → V, ∀ x : K, x = (a x : K) / (b x : K) := by
    have h : ∀ x : K, ∃ a b : V, x = (a : K) / (b : K) := by
      intro x
      obtain ⟨a, b, _, h⟩ := IsFractionRing.div_surjective V x
      exact ⟨a, b, h.symm⟩
    choose a b hab using h
    exact ⟨a, b, hab⟩
  let t : Finset K := s.image (fun x => (a x : K)) ∪ s.image (fun x => (b x : K))
  let D : Subalgebra A K := Algebra.adjoin A (t : Set K)
  have hD : D.toSubring ≤ V.toSubring := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hx
          exact (a x).property
        · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hx
          exact (b x).property
    | algebraMap x => exact hV x
    | add x y _ _ hx hy => exact V.toSubring.add_mem hx hy
    | mul x y _ _ hx hy => exact V.toSubring.mul_mem hx hy
  refine ⟨D, ⟨t, rfl⟩, hD, ?_⟩
  apply isFractionRing_of_closure_eq_top
  let F := Subfield.closure (Set.range (algebraMap D K))
  have hbase : ∀ x : A, algebraMap A K x ∈ F := by
    intro x
    exact Subfield.subset_closure ⟨algebraMap A D x, rfl⟩
  have hs : ∀ x ∈ s, x ∈ F := by
    intro x hx
    rw [hab x]
    apply F.div_mem
    · exact Subfield.subset_closure
        ⟨⟨_, Algebra.subset_adjoin (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨x, hx, rfl⟩))⟩, rfl⟩
    · exact Subfield.subset_closure
        ⟨⟨_, Algebra.subset_adjoin (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨x, hx, rfl⟩))⟩, rfl⟩
  have hC : (Algebra.EssFiniteType.subalgebra A K).toSubring ≤ F.toSubring := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap x => exact hbase x
    | add x y _ _ hx hy => exact F.add_mem hx hy
    | mul x y _ _ hx hy => exact F.mul_mem hx hy
  apply top_unique
  intro x _
  obtain ⟨⟨c, d⟩, h⟩ :=
    IsLocalization.surj (Algebra.EssFiniteType.submonoid A K) x
  have hd : (d.1 : K) ≠ 0 := d.property.ne_zero
  have he : x = (c : K) / (d.1 : K) := (eq_div_iff hd).mpr h
  rw [he]
  exact F.div_mem (hC c.property) (hC d.1.property)

/-- A nonlocal essentially finite type field map admits a local DVR factor in that field. -/
lemma exists_discrete_valuation_factor
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : Type v) [Field K] (f : A →+* K) (hf : f.EssFiniteType)
    (hn : ¬ IsLocalHom f) :
    ∃ (W : ValuationSubring K) (hW : ∀ a : A, f a ∈ W),
      IsDiscreteValuationRing W ∧ IsLocalHom (f.codRestrict W.toSubring hW) := by
  classical
  let : Algebra A K := f.toAlgebra
  have : Algebra.EssFiniteType A K := hf
  obtain ⟨V, hV, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  have := hlocal
  obtain ⟨D, hfg, hD, hfrac⟩ := exists_finiteType_subalgebra A K V hV
  have : Algebra.FiniteType A D := D.fg_iff_finiteType.mp hfg
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A D
  have : IsFractionRing D K := hfrac
  let dV : D →+* V := Subring.inclusion hD
  let q : Ideal D := (maximalIdeal V).comap dV
  have : q.IsPrime := Ideal.comap_isPrime dV (maximalIdeal V)
  let B : Subring K := (LocalSubring.ofPrime D.toSubring q).toSubring
  let dB : D →+* B := Subring.inclusion (LocalSubring.le_ofPrime D.toSubring q)
  let g : A →+* B := dB.comp (algebraMap A D)
  let : Algebra D B :=
    inferInstanceAs (Algebra D.toSubring (LocalSubring.ofPrime D.toSubring q).toSubring)
  have : IsLocalization q.primeCompl B :=
    IsLocalization.isLocalization_of_algEquiv q.primeCompl
      (LocalSubring.ofPrimeEquiv D.toSubring q)
  have : IsScalarTower D B K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsLocalRing B := LocalSubring.isLocalRing _
  have : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing q.primeCompl B inferInstance
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl B K
  have hg : IsLocalHom g := by
    constructor
    intro a ha
    have ha' : IsUnit (algebraMap D B (algebraMap A D a)) := ha
    have hq := (IsLocalization.AtPrime.isUnit_to_map_iff B q _).mp ha'
    have hu : IsUnit ((f.codRestrict V.toSubring hV) a) := by
      change ¬ ¬ IsUnit (dV (algebraMap A D a)) at hq
      exact not_not.mp hq
    exact IsLocalHom.map_nonunit a hu
  have := hg
  have hB : ¬ IsField B := by
    intro hb
    let : Field B := hb.toField
    have hc : (B.subtype.comp g) = f := by ext; rfl
    apply hn
    rw [← hc]
    infer_instance
  obtain ⟨W, hdvr, hBW, hdom⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates hB K
  let bw : B →+* W := (algebraMap B K).codRestrict W.toSubring hBW
  have hbw : IsLocalHom bw := by
    constructor
    intro b hb
    by_contra h
    have hm : b ∈ maximalIdeal B := h
    have hmW := (hdom b).mp hm
    have hnW : bw b ∈ maximalIdeal W := W.coe_mem_nonunits_iff.mp hmW
    exact hnW hb
  have := hbw
  have hW : ∀ a : A, f a ∈ W := fun a => hBW (g a)
  refine ⟨W, hW, hdvr, ?_⟩
  have hc : bw.comp g = f.codRestrict W.toSubring hW := by ext; rfl
  rw [← hc]
  infer_instance

end Langlands.AlgebraicGeometry.DiscreteValuationFactor
