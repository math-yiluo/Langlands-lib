import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.InducedPlaces
import Langlands.Cohomology.Profinite.ClassFormation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Shapiro's lemma for the Euler characteristic ratio

Let `K` be a number field, `Ω` a Galois extension, `S` a set of finite places of `K`, `G_S` the Galois
group of `K_S ⊆ Ω`, `ι : PlaceEmbeddings K Ω`, and `L` a number field with `K → L → Ω` and `L ⊆ K_S`;
let `U ⊆ G_S` be the open subgroup fixing `L`, identified with `G_{S_L}(L)` for the places `S_L` of
`L` above `S` (`fixingOpenSubgroupEquiv`). For a finite smooth `U`-module `B`, viewed as a
`G_{S_L}(L)`-module (`resFixedField`), and any `ιL : PlaceEmbeddings L Ω`,

`globalEulerRatio ι (Ind_U^{G_S} B) = globalEulerRatio ιL B` (`globalEulerRatio_coind`).

The Euler characteristics agree by Shapiro's lemma (`eulerCharacteristic_coind`) and the
identification `U ≅ G_{S_L}(L)`. At a real place `v` of `K`, Mackey's formula
(`mackeyCohomologyEquiv`) splits `H⁰(K_v, Ind B)` over the double cosets `U \ G_S / G_v`, which are the
infinite places of `L` above `v` (`Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.InducedPlaces`);
the factor of a double coset is `#H⁰(L_w, B)` (`card_cohomology_zero_mackeyRep`). So
`∏_{v real} #H⁰(K_v, Ind B) = ∏_{w real} #H⁰(L_w, B) · #B^c` with `c` the number of complex places of
`L` above real places of `K`, and `#∞_L + c = [L:K] · #∞_K`
(`card_infinitePlace_add_card_complex_over_real`) accounts for `#Ind B = #B^{[L:K]}`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  GaloisGroupUnramifiedOutside

universe u

noncomputable section

section Index

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)

/-- The index of the subgroup of `G_S` fixing `L` is `[L : K]`. -/
theorem index_fixingOpenSubgroup :
    (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index =
      Module.finrank K L := by
  rw [coe_fixingOpenSubgroup]
  change (embeddingMaximalUnramifiedOutside hL).fieldRange.fixingSubgroup.index = _
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact (embeddingMaximalUnramifiedOutside hL).equivFieldRange.toLinearEquiv.finrank_eq.symm

instance finiteIndex_fixingOpenSubgroup :
    (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).FiniteIndex :=
  ⟨by rw [index_fixingOpenSubgroup]; exact Module.finrank_pos.ne'⟩

/-- `#Ind_U^{G_S} B = #B^{[L:K]}`. -/
theorem card_coind_fixingOpenSubgroup {k : Type u} [CommRing k]
    (B : Rep.{u} k (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    [Finite B] :
    Nat.card (Rep.coind (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype B) =
      Nat.card B ^ Module.finrank K L := by
  have : Finite (GaloisGroupUnramifiedOutside K Ω S ⧸
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) :=
    Subgroup.finite_quotient_of_finiteIndex
  rw [card_coind, index_fixingOpenSubgroup]

end Index

section Count

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem liesOver_of_comap_eq {w : InfinitePlace L} {v : InfinitePlace K}
    (h : w.comap (algebraMap K L) = v) : w.LiesOver v :=
  ⟨by rw [← h]; rfl⟩

open scoped Classical in
/-- For every infinite place `v` of `K`: the number of places of `L` above `v`, plus the number of
complex places of `L` above `v` when `v` is real, is `[L : K]`. -/
theorem card_fiber_add_card_complex_eq_finrank (v : InfinitePlace K) :
    (Finset.univ.filter fun w : InfinitePlace L => w.comap (algebraMap K L) = v).card +
      (Finset.univ.filter fun w : InfinitePlace L =>
        w.comap (algebraMap K L) = v ∧ w.IsComplex ∧ v.IsReal).card = Module.finrank K L := by
  have h := InfinitePlace.unramifiedPlacesOver_ncard_add_eq_finrank L v
  have hU : InfinitePlace.unramifiedPlacesOver L v =
      ((Finset.univ.filter fun w : InfinitePlace L =>
        w.comap (algebraMap K L) = v ∧ ¬ (w.IsComplex ∧ v.IsReal)) : Set (InfinitePlace L)) := by
    ext w
    simp only [InfinitePlace.unramifiedPlacesOver, Set.mem_ofPred_eq, Finset.coe_filter,
      Finset.mem_univ, true_and, InfinitePlace.isUnramified_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hc := InfinitePlace.LiesOver.comap_eq w v
      refine ⟨hc, fun ⟨hw, hv⟩ => ?_⟩
      rcases h2 with h2 | h2
      · exact InfinitePlace.not_isReal_iff_isComplex.2 hw h2
      · rw [hc] at h2
        exact InfinitePlace.not_isReal_iff_isComplex.2 h2 hv
    · rintro ⟨h1, h2⟩
      refine ⟨liesOver_of_comap_eq K L h1, ?_⟩
      by_cases hw : w.IsReal
      · exact Or.inl hw
      · right
        rw [h1]
        by_contra hv
        exact h2 ⟨InfinitePlace.not_isReal_iff_isComplex.1 hw,
          InfinitePlace.not_isComplex_iff_isReal.1 hv⟩
  have hR : InfinitePlace.ramifiedPlacesOver L v =
      ((Finset.univ.filter fun w : InfinitePlace L =>
        w.comap (algebraMap K L) = v ∧ w.IsComplex ∧ v.IsReal) : Set (InfinitePlace L)) := by
    ext w
    simp only [InfinitePlace.ramifiedPlacesOver, Set.mem_ofPred_eq, Finset.coe_filter,
      Finset.mem_univ, true_and, InfinitePlace.IsRamified, InfinitePlace.isUnramified_iff, not_or]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hc := InfinitePlace.LiesOver.comap_eq w v
      refine ⟨hc, InfinitePlace.not_isReal_iff_isComplex.1 h2, ?_⟩
      rw [← hc]
      exact InfinitePlace.not_isComplex_iff_isReal.1 h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨liesOver_of_comap_eq K L h1, InfinitePlace.not_isReal_iff_isComplex.2 h2, ?_⟩
      rw [h1]
      exact InfinitePlace.not_isComplex_iff_isReal.2 h3
  rw [hU, hR, Set.ncard_coe_finset, Set.ncard_coe_finset] at h
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun w : InfinitePlace L => w.comap (algebraMap K L) = v)
    (fun w : InfinitePlace L => w.IsComplex ∧ v.IsReal)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  omega

open scoped Classical in
/-- `#∞_L + c = [L : K] · #∞_K`, where `c` is the number of complex places of `L` above real places
of `K`. -/
theorem card_infinitePlace_add_card_complex_over_real :
    Fintype.card (InfinitePlace L) +
        (Finset.univ.filter fun w : InfinitePlace L =>
          w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal).card =
      Module.finrank K L * Fintype.card (InfinitePlace K) := by
  have h1 : Fintype.card (InfinitePlace L) = ∑ v : InfinitePlace K,
      (Finset.univ.filter fun w : InfinitePlace L => w.comap (algebraMap K L) = v).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun w _ => Finset.mem_univ _)
  have h2 : (Finset.univ.filter fun w : InfinitePlace L =>
      w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal).card = ∑ v : InfinitePlace K,
      (Finset.univ.filter fun w : InfinitePlace L =>
        w.comap (algebraMap K L) = v ∧ w.IsComplex ∧ v.IsReal).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun w : InfinitePlace L => w.comap (algebraMap K L))
      (t := Finset.univ) (fun w _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun v _ => congrArg Finset.card ?_
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hw, hv⟩, rfl⟩
      exact ⟨rfl, hw, hv⟩
    · rintro ⟨rfl, hw, hv⟩
      exact ⟨⟨hw, hv⟩, rfl⟩
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun v _ =>
    card_fiber_add_card_complex_eq_finrank K L v, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm]

end Count

section Transport

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)

/-- `G_{S_L}(L) → U ⊆ G_S`, the inverse of `fixingOpenSubgroupEquiv`. -/
def fixingOpenSubgroupInvHom :
    GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) →ₜ*
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :=
  ⟨(fixingOpenSubgroupEquiv S hL).symm.toMulEquiv.toMonoidHom,
    (fixingOpenSubgroupEquiv S hL).symm.continuous⟩

theorem fixingOpenSubgroupInvHom_apply (τ : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) :
    fixingOpenSubgroupInvHom hL τ = (fixingOpenSubgroupEquiv S hL).symm τ :=
  rfl

/-- A module of the subgroup of `G_S` fixing `L`, as a module of `G_{S_L}(L)`. -/
abbrev resFixedField {k : Type u} [CommRing k]
    (B : Rep.{u} k (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) :
    Rep.{u} k (GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) :=
  Rep.res (fixingOpenSubgroupInvHom hL : _ →* _) B

instance isSmoothRep_resFixedField {k : Type u} [CommRing k]
    (B : Rep.{u} k (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    [IsSmoothRep B] : IsSmoothRep (resFixedField hL B) :=
  isSmoothRep_res _ B

theorem card_cohomology_resFixedField {k : Type u} [CommRing k]
    (B : Rep.{u} k (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    [IsSmoothRep B] (n : ℕ) :
    Nat.card (cohomology (resFixedField hL B) n) = Nat.card (cohomology B n) := by
  set e := fixingOpenSubgroupEquiv S hL
  have hiso := isIso_map_of_mulEquiv e.symm.toMulEquiv e.symm.continuous e.continuous
    (𝟙 (resFixedField hL B)) Function.bijective_id n
  exact (Nat.card_congr (asIso (map ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩
    (𝟙 (resFixedField hL B)) n)).toLinearEquiv.toEquiv).symm

theorem eulerCharacteristic_resFixedField {k : Type u} [CommRing k]
    (B : Rep.{u} k (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    [IsSmoothRep B] : eulerCharacteristic (resFixedField hL B) = eulerCharacteristic B := by
  simp only [eulerCharacteristic, card_cohomology_resFixedField]

end Transport

section Real

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω] [IsGalois L Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)
  (ιL : PlaceEmbeddings L Ω)
  (B : Rep.{u} (ULift.{u} ℤ) (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
  [IsSmoothRep B]

/-- The `H⁰` of a module is its submodule of invariants. -/
theorem card_cohomology_zero_eq_card_invariants {k G : Type u} [CommRing k] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{u} k G) [IsSmoothRep A] :
    Nat.card (cohomology A 0) = Nat.card A.ρ.invariants :=
  Nat.card_congr (zeroIso A).toLinearEquiv.toEquiv

omit [IsSmoothRep B] in
/-- The `H⁰` factor of Mackey's formula at a real place is `H⁰(L_w, B)` for the place `w` of `L`
attached to the double coset. -/
theorem card_cohomology_zero_mackeyRep (v : {v : InfinitePlace K // v.IsReal})
    (d : MackeyDoubleCoset (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom)
    [IsSmoothRep (mackeyRep (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom B d.out)] :
    Nat.card (cohomology (mackeyRep (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom B d.out) 0) =
      Nat.card (cohomology (realLocalModule ιL (resFixedField hL B)
        (mackeyInfinitePlace S hL ι v d)) 0) := by
  have hmk : mackeyInfinitePlace S hL ι v d = InfinitePlace.mk (complexEmbeddingAt hL ι v.1 d.out) :=
    rfl
  rw [card_cohomology_zero_eq_card_invariants, card_cohomology_zero_eq_card_invariants, hmk]
  generalize d.out = x
  by_cases htop : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S v.1).toMonoidHom x = ⊤
  · -- the place is real: the two invariant subgroups are conjugate
    have hw : (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)).IsReal :=
      (mackeySubgroup_eq_top_iff_isReal hL ι v x).1 htop
    have hc : x * realLocalizationHom ι S v.1 (closureConj v.1 v.2) * x⁻¹ ∈ fixingOpenSubgroup S hL := by
      have : closureConj v.1 v.2 ∈ mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S v.1).toMonoidHom x :=
        htop ▸ Subgroup.mem_top _
      exact this
    obtain ⟨g, hg⟩ := exists_conj_realLocalizationHom_closureConj hL ι ιL v x hw hc
    set c₁ : (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) := ⟨_, hc⟩
    set g' : (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) := (fixingOpenSubgroupEquiv S hL).symm g
    -- invariants on the left: fixed points of `c₁`
    have hleft : ∀ b : B, b ∈ (mackeyRep (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S v.1).toMonoidHom B x).ρ.invariants ↔
        B.ρ c₁ b = b := fun b => by
      rw [Representation.mem_invariants]
      constructor
      · intro h
        exact h ⟨closureConj v.1 v.2, htop ▸ Subgroup.mem_top _⟩
      · intro h σ
        rcases eq_one_or_eq_closureConj v.1 v.2 σ.1 with h1 | h1
        · have : σ = 1 := Subtype.ext h1
          rw [this, map_one, Module.End.one_apply]
        · change B.ρ (mackeyConj (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) _ x σ) b = b
          have : mackeyConj (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S v.1).toMonoidHom x σ = c₁ :=
            Subtype.ext (by rw [mackeyConj_apply_coe, h1]; rfl)
          rw [this]
          exact h
    -- invariants on the right: fixed points of `g'⁻¹ c₁ g'`
    have hright : ∀ b : B, b ∈ (realLocalModule ιL (resFixedField hL B)
        (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x))).ρ.invariants ↔ B.ρ (g'⁻¹ * c₁ * g') b = b := fun b => by
      rw [Representation.mem_invariants]
      have key : (fixingOpenSubgroupInvHom hL) (realLocalizationHom ιL (finitePlacesAbove L S)
          (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)) (closureConj _ hw)) = g'⁻¹ * c₁ * g' := by
        change (fixingOpenSubgroupEquiv S hL).symm (realLocalizationHom ιL (finitePlacesAbove L S)
          (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)) (closureConj _ hw)) = _
        rw [hg, map_mul, map_mul, map_inv, ContinuousMulEquiv.symm_apply_apply]
      constructor
      · intro h
        have := h (closureConj _ hw)
        change B.ρ (fixingOpenSubgroupInvHom hL (realLocalizationHom ιL (finitePlacesAbove L S)
          (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)) (closureConj _ hw))) b = b at this
        rwa [key] at this
      · intro h σ
        rcases eq_one_or_eq_closureConj _ hw σ with h1 | h1
        · rw [h1, map_one, Module.End.one_apply]
        · rw [h1]
          change B.ρ (fixingOpenSubgroupInvHom hL (realLocalizationHom ιL (finitePlacesAbove L S)
            (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)) (closureConj _ hw))) b = b
          rw [key]
          exact h
    have hinv : ∀ z : B, B.ρ g' (B.ρ g'⁻¹ z) = z := fun z => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have hinv' : ∀ z : B, B.ρ g'⁻¹ (B.ρ g' z) = z := fun z => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hρ : ∀ z : B, B.ρ (g'⁻¹ * c₁ * g') z = B.ρ g'⁻¹ (B.ρ c₁ (B.ρ g' z)) := fun z => by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    let E : {b : B // B.ρ c₁ b = b} ≃ {b : B // B.ρ (g'⁻¹ * c₁ * g') b = b} :=
      { toFun := fun b => ⟨B.ρ g'⁻¹ b.1, by rw [hρ, hinv, b.2]⟩
        invFun := fun b => ⟨B.ρ g' b.1, by
          have h := congrArg (B.ρ g') b.2
          rw [hρ, hinv] at h
          exact h⟩
        left_inv := fun b => Subtype.ext (hinv b.1)
        right_inv := fun b => Subtype.ext (hinv' b.1) }
    exact Nat.card_congr ((Equiv.subtypeEquivRight hleft).trans
      (E.trans (Equiv.subtypeEquivRight hright).symm))
  · -- the place is complex: both groups act trivially
    have hbot := mackeySubgroup_eq_bot_of_ne_top hL ι v x htop
    have hw : ¬ (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)).IsReal := fun h =>
      htop ((mackeySubgroup_eq_top_iff_isReal hL ι v x).2 h)
    have hl : ∀ b : B, b ∈ (mackeyRep (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S v.1).toMonoidHom B x).ρ.invariants :=
      fun b σ => by
        have : σ = 1 := Subtype.ext (by
          have h1 : (σ : Gal(AlgebraicClosure v.1.Completion/v.1.Completion)) ∈
              (⊥ : Subgroup Gal(AlgebraicClosure v.1.Completion/v.1.Completion)) := hbot ▸ σ.2
          exact Subgroup.mem_bot.1 h1)
        rw [this, map_one, Module.End.one_apply]
    have hr : ∀ b : B, b ∈ (realLocalModule ιL (resFixedField hL B)
        (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x))).ρ.invariants := fun b σ => by
      rw [eq_one_of_isComplex _ (InfinitePlace.not_isReal_iff_isComplex.1 hw) σ, map_one,
        Module.End.one_apply]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hl), Nat.card_congr (Equiv.subtypeUnivEquiv hr)]

end Real

section Ratio

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω] [IsGalois L Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)
  (ιL : PlaceEmbeddings L Ω)
  (B : Rep.{u} (ULift.{u} ℤ) (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
  [IsSmoothRep B]

open scoped Classical in
/-- Mackey's formula at a real place `v` of `K`: `#H⁰(K_v, Ind B)` is the product of `#H⁰(L_w, B)` over
the places `w` of `L` above `v`. -/
theorem card_cohomology_zero_realLocalModule_coind (v : {v : InfinitePlace K // v.IsReal}) :
    Nat.card (cohomology (realLocalModule ι (Rep.coind (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype B) v.1) 0) =
      ∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v.1},
        Nat.card (cohomology (realLocalModule ιL (resFixedField hL B) w.1) 0) := by
  have : Finite (MackeyDoubleCoset (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S v.1).toMonoidHom) :=
    finite_mackeyDoubleCoset _ _
  have : Fintype (MackeyDoubleCoset (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S v.1).toMonoidHom) :=
    Fintype.ofFinite _
  have hsm : ∀ x, IsSmoothRep (mackeyRep (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S v.1).toMonoidHom B x) :=
    fun x => isSmoothRep_mackeyRep _ (realLocalizationHom ι S v.1).continuous_toFun B x
  have h1 := Nat.card_congr (mackeyCohomologyEquiv (fixingOpenSubgroup S hL)
    (realLocalizationHom ι S v.1) B 0).toEquiv
  rw [Nat.card_pi] at h1
  refine h1.trans ?_
  -- the double cosets are the places above `v`
  let e : MackeyDoubleCoset (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom ≃
        {w : InfinitePlace L // w.comap (algebraMap K L) = v.1} :=
    Equiv.ofBijective (fun d => ⟨mackeyInfinitePlace S hL ι v d, comap_mackeyInfinitePlace hL ι v d⟩)
      ⟨fun d d' h => mackeyInfinitePlace_injective hL ι v (congrArg Subtype.val h),
        fun w => by
          obtain ⟨d, hd⟩ := exists_mackeyInfinitePlace_eq hL ι v w.1 w.2
          exact ⟨d, Subtype.ext hd⟩⟩
  refine Fintype.prod_equiv e _ _ fun d => ?_
  exact card_cohomology_zero_mackeyRep hL ι ιL B v d

open scoped Classical in
/-- **Regrouping a product over the infinite places.** For `f` on the infinite places of `L` with value
`c` at the complex places, the product of `f` over the places above the real places of `K` is the
product over the real places of `L` times `c` to the number of complex places of `L` above real places
of `K`. -/
theorem prod_prod_fiber_eq (f : InfinitePlace L → ℕ) (c : ℕ) (hf : ∀ w, w.IsComplex → f w = c) :
    ∏ v : {v : InfinitePlace K // v.IsReal},
        ∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v.1}, f w.1 =
      (∏ w : {w : InfinitePlace L // w.IsReal}, f w.1) *
        c ^ (Finset.univ.filter fun w : InfinitePlace L =>
          w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal).card := by
  let σ : (Σ v : {v : InfinitePlace K // v.IsReal},
      {w : InfinitePlace L // w.comap (algebraMap K L) = v.1}) ≃
        {w : InfinitePlace L // (w.comap (algebraMap K L)).IsReal} :=
    { toFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
      invFun := fun w => ⟨⟨_, w.2⟩, ⟨w.1, rfl⟩⟩
      left_inv := fun p => by
        obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := p
        change w.comap (algebraMap K L) = v at hw
        subst hw
        rfl
      right_inv := fun w => rfl }
  have h1 : ∏ v : {v : InfinitePlace K // v.IsReal},
      ∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v.1}, f w.1 =
        ∏ w : {w : InfinitePlace L // (w.comap (algebraMap K L)).IsReal}, f w.1 := by
    rw [← Fintype.prod_equiv σ (fun p => f p.2.1) (fun w => f w.1) (fun p => rfl)]
    exact (Fintype.prod_sigma (fun p : (Σ v : {v : InfinitePlace K // v.IsReal},
      {w : InfinitePlace L // w.comap (algebraMap K L) = v.1}) => f p.2.1)).symm
  rw [h1, ← Fintype.prod_subtype_mul_prod_subtype (fun w : {w : InfinitePlace L //
    (w.comap (algebraMap K L)).IsReal} => w.1.IsReal)]
  congr 1
  · exact Fintype.prod_equiv
      { toFun := fun w => ⟨w.1.1, w.2⟩
        invFun := fun w => ⟨⟨w.1, InfinitePlace.IsReal.comap _ w.2⟩, w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ fun w => rfl
  · rw [Finset.prod_congr rfl fun w _ => hf w.1.1 (InfinitePlace.not_isReal_iff_isComplex.1 w.2),
      Finset.prod_const, Finset.card_univ]
    congr 1
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun w => ⟨w.1.1, Finset.mem_filter.2 ⟨Finset.mem_univ _,
          InfinitePlace.not_isReal_iff_isComplex.1 w.2, w.1.2⟩⟩
        invFun := fun w => ⟨⟨w.1, (Finset.mem_filter.1 w.2).2.2⟩,
          InfinitePlace.not_isReal_iff_isComplex.2 (Finset.mem_filter.1 w.2).2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

open scoped Classical in
/-- The product over the real places of `K` of `#H⁰(K_v, Ind B)` is the product over the real places
of `L` of `#H⁰(L_w, B)`, times `#B` for each complex place of `L` above a real place of `K`. -/
theorem prod_card_cohomology_zero_coind [Finite B] :
    ∏ v : {v : InfinitePlace K // v.IsReal}, Nat.card (cohomology (realLocalModule ι
        (Rep.coind (fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype B) v.1) 0) =
      (∏ w : {w : InfinitePlace L // w.IsReal},
          Nat.card (cohomology (realLocalModule ιL (resFixedField hL B) w.1) 0)) *
        Nat.card B ^ (Finset.univ.filter fun w : InfinitePlace L =>
          w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal).card := by
  rw [Finset.prod_congr rfl fun v _ => card_cohomology_zero_realLocalModule_coind hL ι ιL B v]
  refine prod_prod_fiber_eq (fun w => Nat.card (cohomology (realLocalModule ιL (resFixedField hL B) w) 0))
    _ fun w hw => ?_
  exact card_cohomology_zero_of_forall_eq_one _ fun g => by
    rw [eq_one_of_isComplex _ hw g, map_one]

/-- **Shapiro's lemma for the Euler characteristic ratio.** For a finite smooth module `B` of the
subgroup `U ⊆ G_S` fixing `L`, the ratio of `Ind_U^{G_S} B` for `K` is the ratio of `B` for `L`. -/
theorem globalEulerRatio_coind [Finite B] :
    globalEulerRatio ι (Rep.coind (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype B) =
      globalEulerRatio ιL (resFixedField hL B) := by
  classical
  have hP := prod_card_cohomology_zero_coind hL ι ιL B
  have hN := card_infinitePlace_add_card_complex_over_real K L
  set c := (Finset.univ.filter fun w : InfinitePlace L =>
    w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal).card with hc
  have hB : (Nat.card B : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  unfold globalEulerRatio
  rw [eulerCharacteristic_coind, card_coind_fixingOpenSubgroup, eulerCharacteristic_resFixedField]
  have hPq : (∏ v : {v : InfinitePlace K // v.IsReal}, (Nat.card (cohomology (realLocalModule ι
        (Rep.coind (fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype B) v.1) 0) : ℚ)) =
      (∏ w : {w : InfinitePlace L // w.IsReal},
          (Nat.card (cohomology (realLocalModule ιL (resFixedField hL B) w.1) 0) : ℚ)) *
        (Nat.card B : ℚ) ^ c := by
    exact_mod_cast hP
  rw [hPq]
  have hcard : Nat.card (resFixedField hL B) = Nat.card B := rfl
  rw [hcard, Nat.cast_pow, ← pow_mul, ← hN, pow_add, ← mul_assoc,
    mul_div_mul_right _ _ (pow_ne_zero _ hB)]

end Ratio

section ResToFixedField

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)

/-- A module of `G_S`, restricted to the subgroup fixing `L` and viewed as a module of
`G_{S_L}(L)`. -/
def resToFixedField {k : Type u} [CommRing k]
    (M : Rep.{u} k (GaloisGroupUnramifiedOutside K Ω S)) :
    Rep.{u} k (GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) :=
  resFixedField hL (Rep.res (fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)

theorem resToFixedField_ρ_apply {k : Type u} [CommRing k]
    (M : Rep.{u} k (GaloisGroupUnramifiedOutside K Ω S))
    (τ : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) (m : M) :
    (resToFixedField hL M).ρ τ m =
      M.ρ (((fixingOpenSubgroupEquiv S hL).symm τ : (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S))) : GaloisGroupUnramifiedOutside K Ω S) m :=
  rfl

instance isSmoothRep_resToFixedField {k : Type u} [CommRing k]
    (M : Rep.{u} k (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] :
    IsSmoothRep (resToFixedField hL M) :=
  have : IsSmoothRep (Rep.res (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) := isSmoothRep_res_subtype M _
  isSmoothRep_resFixedField hL _

instance finite_resToFixedField {k : Type u} [CommRing k]
    (M : Rep.{u} k (GaloisGroupUnramifiedOutside K Ω S)) [Finite M] :
    Finite (resToFixedField hL M) :=
  inferInstanceAs (Finite M)

theorem card_resToFixedField {k : Type u} [CommRing k]
    (M : Rep.{u} k (GaloisGroupUnramifiedOutside K Ω S)) :
    Nat.card (resToFixedField hL M) = Nat.card M :=
  rfl

variable [IsGalois L Ω] (ι : PlaceEmbeddings K Ω) (ιL : PlaceEmbeddings L Ω)

/-- **Shapiro's lemma for the ratio**, for a module of `G_S`: the ratio of `Ind_U^{G_S} Res_U M` for `K`
is the ratio of `M` as a `G_{S_L}(L)`-module. -/
theorem globalEulerRatio_coind_res (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
    [IsSmoothRep M] [Finite M] :
    globalEulerRatio ι (Rep.coind (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.res (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) =
      globalEulerRatio ιL (resToFixedField hL M) := by
  have : IsSmoothRep (Rep.res (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) := isSmoothRep_res_subtype M _
  have : Finite (Rep.res (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) := inferInstanceAs (Finite M)
  exact globalEulerRatio_coind hL ι ιL _

end ResToFixedField

end

end Langlands.GaloisCohomology
