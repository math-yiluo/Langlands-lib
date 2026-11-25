import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction
import Langlands.ClassFieldTheory.Global.IdeleLocalInjectivity
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Counting Galois conjugates of a finite place

For a Galois extension `L/K` of number fields, the Galois group acts on the finite places of
`L` through `finitePlaceEquiv`. The action preserves ramification indices and inertia
degrees. Its stabilizer at a place `u` above `v` has `e(u|v) f(u|v)` elements. For an
intermediate field `M`, exactly `[L : M] e(w|v) f(w|v)` elements `σ` move `u` to a place
above a given place `w` of `M` over `v`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Pointwise

section Action

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem finitePlaceEquiv_algEquiv_mul (σ τ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv (σ * τ).toRingEquiv w =
      finitePlaceEquiv τ.toRingEquiv (finitePlaceEquiv σ.toRingEquiv w) := by
  change finitePlaceEquiv (τ.toRingEquiv.trans σ.toRingEquiv) w = _
  rw [finitePlaceEquiv_trans]
  rfl

theorem finitePlaceEquiv_algEquiv_one (w : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv (1 : L ≃ₐ[K] L).toRingEquiv w = w := by
  change finitePlaceEquiv (RingEquiv.refl L) w = w
  rw [finitePlaceEquiv_refl]
  rfl

theorem finitePlaceEquiv_algEquiv_inv_apply (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv σ⁻¹.toRingEquiv (finitePlaceEquiv σ.toRingEquiv w) = w := by
  rw [← finitePlaceEquiv_algEquiv_mul, mul_inv_cancel, finitePlaceEquiv_algEquiv_one]

theorem finitePlaceEquiv_algEquiv_apply_inv (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv σ.toRingEquiv (finitePlaceEquiv σ⁻¹.toRingEquiv w) = w := by
  rw [← finitePlaceEquiv_algEquiv_mul, inv_mul_cancel, finitePlaceEquiv_algEquiv_one]

/-- The pulled-back place is the Galois translate by `σ⁻¹` of the ideal. -/
theorem asIdeal_finitePlaceEquiv_algEquiv (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv σ.toRingEquiv w).asIdeal = σ⁻¹ • w.asIdeal := by
  ext x
  rw [finitePlaceEquiv_mem, Ideal.mem_inv_pointwise_smul_iff]
  rfl

variable [NumberField K] [NumberField L]

/-- Galois automorphisms commute with the `𝓞 K`-module structure of `𝓞 L`. -/
instance smulCommClass_ringOfIntegers : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm σ a x := by
    apply RingOfIntegers.ext
    change σ ((a • x : 𝓞 L) : L) = ((a • (σ • x) : 𝓞 L) : L)
    rw [Algebra.smul_def, Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap,
      RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_mul]
    congr 1
    change σ (algebraMap K L (a : K)) = algebraMap K L (a : K)
    exact σ.commutes _

omit [NumberField K] [NumberField L] in
@[simp] theorem ramificationIdx_finitePlaceEquiv_algEquiv (σ : L ≃ₐ[K] L)
    (w : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv σ.toRingEquiv w).asIdeal.ramificationIdx (𝓞 K) =
      w.asIdeal.ramificationIdx (𝓞 K) := by
  rw [asIdeal_finitePlaceEquiv_algEquiv, Ideal.ramificationIdx_smul]

omit [NumberField K] [NumberField L] in
@[simp] theorem inertiaDeg_finitePlaceEquiv_algEquiv (σ : L ≃ₐ[K] L)
    (w : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv σ.toRingEquiv w).asIdeal.inertiaDeg (𝓞 K) =
      w.asIdeal.inertiaDeg (𝓞 K) := by
  rw [asIdeal_finitePlaceEquiv_algEquiv, Ideal.inertiaDeg_smul]

end Action

section Count

open Classical

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The places of `L` above `v`, as a finite set. -/
def placesAbove (L : Type u) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 L)) :=
  (Finset.univ : Finset (FinitePlacesAbove L v)).map (Function.Embedding.subtype _)

theorem mem_placesAbove {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)} :
    u ∈ placesAbove L v ↔ u.asIdeal.LiesOver v.asIdeal := by
  simp [placesAbove]

theorem card_placesAbove (v : HeightOneSpectrum (𝓞 K)) :
    (placesAbove L v).card = Fintype.card (FinitePlacesAbove L v) := by
  simp [placesAbove]

/-- If all places above `v` have the same `e f`, their number times `e f` is `[L : K]`. -/
theorem card_mul_eq_finrank_of_forall (v : HeightOneSpectrum (𝓞 K)) (c : ℕ)
    (hc : ∀ q : FinitePlacesAbove L v,
      q.1.asIdeal.ramificationIdx (𝓞 K) * q.1.asIdeal.inertiaDeg (𝓞 K) = c) :
    (placesAbove L v).card * c = Module.finrank K L := by
  rw [← finitePlacesAbove_sum_ramification_inertia v, card_placesAbove]
  simp [hc]

/-- Some place of `L` lies above every finite place of `K`. -/
theorem nonempty_finitePlacesAbove (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (FinitePlacesAbove L v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsum := finitePlacesAbove_sum_ramification_inertia (L := L) v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact Module.finrank_pos.ne hsum

/-- The Galois elements moving `u` into a set `S` of places above `v` number `|S|` times the
stabilizer of `u`. -/
theorem card_filter_finitePlaceEquiv_mem [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
    (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : ∀ u' ∈ S, u'.asIdeal.LiesOver v.asIdeal) :
    (Finset.univ.filter fun σ : L ≃ₐ[K] L => finitePlaceEquiv σ.toRingEquiv u ∈ S).card =
      S.card *
        (Finset.univ.filter fun σ : L ≃ₐ[K] L => finitePlaceEquiv σ.toRingEquiv u = u).card := by
  have H : ((Finset.univ.filter fun σ : L ≃ₐ[K] L =>
      finitePlaceEquiv σ.toRingEquiv u ∈ S : Finset (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)).MapsTo
      (fun σ : L ≃ₐ[K] L => finitePlaceEquiv σ.toRingEquiv u) (S : Set _) :=
    fun σ hσ => (Finset.mem_filter.mp hσ).2
  rw [Finset.card_eq_sum_card_fiberwise H, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun u' hu' => ?_
  have : u'.asIdeal.LiesOver v.asIdeal := hS u' hu'
  obtain ⟨τ, hτ⟩ := Langlands.ClassFieldTheory.Global.exists_finitePlaceEquiv_eq v u u'
  rw [Finset.filter_filter]
  symm
  refine Finset.card_nbij' (fun s => s * τ) (fun σ => σ * τ⁻¹) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
    rw [finitePlaceEquiv_algEquiv_mul, hs, hτ]
    exact ⟨hu', rfl⟩
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    rw [finitePlaceEquiv_algEquiv_mul, hσ.2, ← hτ, finitePlaceEquiv_algEquiv_inv_apply]
  · intro s _
    simp
  · intro σ _
    simp

/-- The stabilizer of a place `u` above `v` has `e(u|v) f(u|v)` elements. -/
theorem card_stabilizer_finitePlaceEquiv [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] :
    (Finset.univ.filter fun σ : L ≃ₐ[K] L => finitePlaceEquiv σ.toRingEquiv u = u).card =
      u.asIdeal.ramificationIdx (𝓞 K) * u.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  have hall : ∀ q : FinitePlacesAbove L v,
      q.1.asIdeal.ramificationIdx (𝓞 K) * q.1.asIdeal.inertiaDeg (𝓞 K) =
        u.asIdeal.ramificationIdx (𝓞 K) * u.asIdeal.inertiaDeg (𝓞 K) := by
    intro q
    obtain ⟨τ, hτ⟩ := Langlands.ClassFieldTheory.Global.exists_finitePlaceEquiv_eq v u q.1
    rw [← hτ, ramificationIdx_finitePlaceEquiv_algEquiv, inertiaDeg_finitePlaceEquiv_algEquiv]
  have hdeg := card_mul_eq_finrank_of_forall (L := L) v _ hall
  have hcount := card_filter_finitePlaceEquiv_mem v u (placesAbove L v)
    (fun u' hu' => mem_placesAbove.mp hu')
  have hall' : (Finset.univ.filter fun σ : L ≃ₐ[K] L =>
      finitePlaceEquiv σ.toRingEquiv u ∈ placesAbove L v) = Finset.univ := by
    refine Finset.filter_true_of_mem fun σ _ => mem_placesAbove.mpr ?_
    exact Langlands.ClassFieldTheory.Global.liesOver_finitePlaceEquiv v u σ
  rw [hall', Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
    ← hdeg] at hcount
  have hpos : 0 < (placesAbove L v).card :=
    Finset.card_pos.mpr ⟨u, mem_placesAbove.mpr inferInstance⟩
  exact (Nat.eq_of_mul_eq_mul_left hpos hcount).symm

/-- For an intermediate field `M`, exactly `[L : M] e(w|v) f(w|v)` Galois elements move a place
`u` above `v` to a place above the place `w` of `M` over `v`. -/
theorem card_filter_finitePlaceEquiv_liesOver {M : Type u} [Field M] [NumberField M]
    [Algebra K M] [Algebra M L] [IsScalarTower K M L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] :
    (Finset.univ.filter fun σ : L ≃ₐ[K] L =>
        (finitePlaceEquiv σ.toRingEquiv u).asIdeal.LiesOver w.asIdeal).card =
      Module.finrank M L * (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  have hfilter : (Finset.univ.filter fun σ : L ≃ₐ[K] L =>
      (finitePlaceEquiv σ.toRingEquiv u).asIdeal.LiesOver w.asIdeal) =
      Finset.univ.filter fun σ : L ≃ₐ[K] L => finitePlaceEquiv σ.toRingEquiv u ∈ placesAbove L w := by
    exact Finset.filter_congr fun σ _ => mem_placesAbove.symm
  rw [hfilter, card_filter_finitePlaceEquiv_mem v u (placesAbove L w) (fun u' hu' => by
      have := mem_placesAbove.mp hu'
      exact Ideal.LiesOver.trans u'.asIdeal w.asIdeal v.asIdeal),
    card_stabilizer_finitePlaceEquiv v u]
  obtain ⟨u'⟩ := nonempty_finitePlacesAbove (L := L) w
  have : u'.1.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans u'.1.asIdeal w.asIdeal v.asIdeal
  obtain ⟨τ, hτ⟩ := Langlands.ClassFieldTheory.Global.exists_finitePlaceEquiv_eq v u u'.1
  have he : u.asIdeal.ramificationIdx (𝓞 K) = u'.1.asIdeal.ramificationIdx (𝓞 K) := by
    rw [← hτ, ramificationIdx_finitePlaceEquiv_algEquiv]
  have hf : u.asIdeal.inertiaDeg (𝓞 K) = u'.1.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← hτ, inertiaDeg_finitePlaceEquiv_algEquiv]
  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have hdeg := card_mul_eq_finrank_of_forall (K := M) (L := L) w
    (u'.1.asIdeal.ramificationIdx (𝓞 M) * u'.1.asIdeal.inertiaDeg (𝓞 M)) (fun q => by
      obtain ⟨τ', hτ'⟩ := Langlands.ClassFieldTheory.Global.exists_finitePlaceEquiv_eq w u'.1 q.1
      rw [← hτ', ramificationIdx_finitePlaceEquiv_algEquiv, inertiaDeg_finitePlaceEquiv_algEquiv])
  rw [he, hf, Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal u'.1.asIdeal,
    Ideal.inertiaDeg_tower (R := 𝓞 K) w.asIdeal u'.1.asIdeal, ← hdeg]
  ring

/-- A family `ρ i` of elements of `Gal(L/K)` meeting every right coset of `Gal(L/M)` exactly
once: for every `σ` there is exactly one `i` with `σ (ρ i)⁻¹ ∈ Gal(L/M)`. -/
def IsRightCosetFamily (M : Type u) [Field M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
    {ι : Type*} (ρ : ι → L ≃ₐ[K] L) : Prop :=
  ∀ σ : L ≃ₐ[K] L, ∃! i, σ * (ρ i)⁻¹ ∈
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range

/-- Right coset representatives exist: for `n = [M : K]` some family `ρ : Fin n → Gal(L/K)`
meets every right coset of `Gal(L/M)` exactly once. -/
theorem exists_isRightCosetFamily {M : Type u} [Field M] [NumberField M]
    [Algebra K M] [Algebra M L] [IsScalarTower K M L] [IsGalois K L]
    (n : ℕ) (hn : n = Module.finrank K M) :
    ∃ ρ : Fin n → L ≃ₐ[K] L, IsRightCosetFamily M ρ := by
  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  let f : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L) := AlgEquiv.restrictScalarsHom K
  have hf : Function.Injective f := AlgEquiv.restrictScalarsHom_injective K
  have hH : Nat.card f.range = Module.finrank M L := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, IsGalois.card_aut_eq_finrank]
  have hcard : Nat.card ((L ≃ₐ[K] L) ⧸ f.range) = n := by
    have h1 := f.range.index_mul_card
    rw [hH, IsGalois.card_aut_eq_finrank, ← Module.finrank_mul_finrank K M L] at h1
    rw [← Subgroup.index_eq_card, hn]
    exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1
  have : Finite ((L ≃ₐ[K] L) ⧸ f.range) := inferInstance
  let e : Fin n ≃ (L ≃ₐ[K] L) ⧸ f.range :=
    (finCongr hcard.symm).trans (Finite.equivFin _).symm
  refine ⟨fun i => (e i).out⁻¹, fun σ => ⟨e.symm (σ⁻¹ : L ≃ₐ[K] L), ?_, ?_⟩⟩
  · have h : ((σ⁻¹ : L ≃ₐ[K] L) : (L ≃ₐ[K] L) ⧸ f.range) =
        ((e (e.symm (σ⁻¹ : L ≃ₐ[K] L))).out : (L ≃ₐ[K] L) ⧸ f.range) := by
      rw [QuotientGroup.out_eq', Equiv.apply_symm_apply]
    rw [QuotientGroup.eq, inv_inv] at h
    simp only [inv_inv]
    exact h
  · intro j hj
    apply e.injective
    rw [Equiv.apply_symm_apply, ← QuotientGroup.out_eq' (e j)]
    simp only [inv_inv] at hj
    exact (QuotientGroup.eq.mpr (by rw [inv_inv]; exact hj)).symm

/-- For representatives `ρ i` of the right cosets of `Gal(L/M)`, exactly `e(w|v) f(w|v)` of the
places `(ρ i)⁻¹ u` lie above the place `w` of `M`. -/
theorem card_filter_rightCosetFamily_liesOver {M : Type u} [Field M] [NumberField M]
    [Algebra K M] [Algebra M L] [IsScalarTower K M L] [IsGalois K L]
    {ι : Type*} [Fintype ι] (ρ : ι → L ≃ₐ[K] L) (hρ : IsRightCosetFamily M ρ)
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] :
    (Finset.univ.filter fun i =>
        (finitePlaceEquiv (ρ i)⁻¹.toRingEquiv u).asIdeal.LiesOver w.asIdeal).card =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  let P : (L ≃ₐ[K] L) → Prop := fun τ =>
    (finitePlaceEquiv τ.toRingEquiv u).asIdeal.LiesOver w.asIdeal
  -- Moving by an element of `Gal(L/M)` does not change the place below in `M`.
  have hP (h : L ≃ₐ[M] L) (τ : L ≃ₐ[K] L) : P (τ * (h.restrictScalars K)) ↔ P τ := by
    simp only [P]
    rw [finitePlaceEquiv_algEquiv_mul]
    constructor
    · intro hτ
      have : (finitePlaceEquiv h.toRingEquiv
          (finitePlaceEquiv τ.toRingEquiv u)).asIdeal.LiesOver w.asIdeal := hτ
      have h1 := finitePlaceEquiv_algEquiv_inv_apply h (finitePlaceEquiv τ.toRingEquiv u)
      have h2 := Langlands.ClassFieldTheory.Global.liesOver_finitePlaceEquiv w
        (finitePlaceEquiv h.toRingEquiv (finitePlaceEquiv τ.toRingEquiv u)) h⁻¹
      rwa [h1] at h2
    · intro hτ
      have := hτ
      exact Langlands.ClassFieldTheory.Global.liesOver_finitePlaceEquiv w
        (finitePlaceEquiv τ.toRingEquiv u) h
  have hcount := card_filter_finitePlaceEquiv_liesOver (M := M) v u w
  -- Reindex by inversion.
  have hinv : (Finset.univ.filter fun σ : L ≃ₐ[K] L => P σ⁻¹).card =
      (Finset.univ.filter fun σ : L ≃ₐ[K] L => P σ).card := by
    refine Finset.card_nbij' (fun σ => σ⁻¹) (fun σ => σ⁻¹) ?_ ?_ ?_ ?_
    · intro σ hσ
      simpa using hσ
    · intro σ hσ
      simpa using hσ
    · intro σ _
      simp
    · intro σ _
      simp
  -- Reindex `Gal(L/K)` by `ι × Gal(L/M)`.
  have hprod : ((Finset.univ.filter fun i => P (ρ i)⁻¹) ×ˢ
      (Finset.univ : Finset (L ≃ₐ[M] L))).card =
      (Finset.univ.filter fun σ : L ≃ₐ[K] L => P σ⁻¹).card := by
    refine Finset.card_bij (fun x _ => x.2.restrictScalars K * ρ x.1) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
        and_true] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_inv_rev]
      have hh : (x.2.restrictScalars K)⁻¹ = (x.2⁻¹).restrictScalars K := rfl
      rw [hh]
      exact (hP _ _).mpr hx
    · intro x _ y _ hxy
      have hx : (x.2.restrictScalars K * ρ x.1) * (ρ x.1)⁻¹ ∈
          (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range :=
        ⟨x.2, by rw [mul_inv_cancel_right]; rfl⟩
      have hy : (x.2.restrictScalars K * ρ x.1) * (ρ y.1)⁻¹ ∈
          (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range := by
        rw [hxy]
        exact ⟨y.2, by rw [mul_inv_cancel_right]; rfl⟩
      have h1 : x.1 = y.1 := (hρ _).unique hx hy
      have h2 : x.2 = y.2 := by
        rw [h1] at hxy
        exact AlgEquiv.restrictScalarsHom_injective K (mul_right_cancel hxy)
      exact Prod.ext h1 h2
    · intro σ hσ
      obtain ⟨i, ⟨h, hh⟩, -⟩ := hρ σ
      refine ⟨(i, h), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
          and_true]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        have hσ' : σ = h.restrictScalars K * ρ i := by
          rw [show h.restrictScalars K = AlgEquiv.restrictScalarsHom K h from rfl, hh]
          simp
        rw [hσ', mul_inv_rev] at hσ
        exact (hP h⁻¹ _).mp hσ
      · change AlgEquiv.restrictScalarsHom K h * ρ i = σ
        rw [hh]
        simp
  rw [Finset.card_product, Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank, hinv] at hprod
  have hpos : 0 < Module.finrank M L := Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [mul_comm, hprod]
  exact hcount

end Count

end Langlands.Global.AdelicFunctoriality
