import Langlands.GaloisCohomology.Global.PoitouTate.Trace
import Langlands.GaloisCohomology.Global.RealPlaces.HighDegree
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Coinduced

/-!
# The Euler characteristic ratio of `G_S`

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K`, `G_S` the
Galois group of the maximal extension of `K` in `Ω` unramified outside `S`, and
`ι : PlaceEmbeddings K Ω`. For a finite smooth `G_S`-module `M`, Tate's global Euler characteristic
formula says

`#H⁰(G_S, M) · #H²(G_S, M) / #H¹(G_S, M) = ∏_{w real} #H⁰(K_w, M) / (#M)^{[K:ℚ]_∞}`

where `[K:ℚ]_∞` is the number of infinite places of `K`. This file defines the ratio of the two sides,

`globalEulerRatio ι M = χ(G_S, M) · (#M)^{#∞} / ∏_{w real} #H⁰(K_w, M)`,

so that the formula for `M` is `globalEulerRatio ι M = 1` (`globalEulerRatio_eq_one_iff`), and proves
its elementary properties: invariance under isomorphisms, value `1` on the zero module, positivity
when the places above `#M` lie in `S`.

It also computes the Euler characteristic of a group of order two (the Galois group of a real place):
for a finite module, `#H¹ = #H²` (`OrderTwo.card_cohomology_one_eq_card_cohomology_two`), so that
`χ = #H⁰` (`OrderTwo.eulerCharacteristic_eq_card_cohomology_zero`); at a real place `w` of `K` this is
`eulerCharacteristic_realLocalModule`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Involution

namespace Involution

variable {M : Type*} [AddCommGroup M] {σ : M →+ M}

theorem ker_id_add_eq_fixedSub_neg : (AddMonoidHom.id M + σ).ker = fixedSub (-σ) := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_fixedSub, AddMonoidHom.add_apply, AddMonoidHom.id_apply,
    AddMonoidHom.neg_apply, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm]

/-- For an involution `σ` of a finite group `M`: `#(M^σ / (1 + σ)M) · #M = #M^σ · #M^{-σ}`. -/
theorem card_tateQuot_mul_card (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (tateQuot σ) * Nat.card M = Nat.card (fixedSub σ) * Nat.card (fixedSub (-σ)) := by
  have h1 : Nat.card (fixedSub σ) = Nat.card (tateQuot σ) * Nat.card (traceSub σ) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      ((traceSub σ).addSubgroupOf (fixedSub σ)),
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (traceSub_le_fixedSub hσ)).toEquiv]
  have h2 : Nat.card (traceSub σ) * Nat.card (fixedSub (-σ)) = Nat.card M := by
    rw [← ker_id_add_eq_fixedSub_neg, traceSub, ← AddSubgroup.index_ker, mul_comm,
      AddSubgroup.card_mul_index]
  rw [h1, mul_assoc, h2]

/-- For an involution `σ` of a finite group, `M^σ/(1 + σ)M` and `M^{-σ}/(1 - σ)M` have the same
order (the Herbrand quotient of a finite module is `1`). -/
theorem card_tateQuot_neg [Finite M] (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (tateQuot (-σ)) = Nat.card (tateQuot σ) := by
  have hσ' : ∀ x, (-σ) ((-σ) x) = x := fun x => by
    rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, map_neg, neg_neg, hσ]
  have e1 := card_tateQuot_mul_card hσ
  have e2 := card_tateQuot_mul_card hσ'
  rw [neg_neg, mul_comm (Nat.card (fixedSub (-σ)))] at e2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (e2.trans e1.symm)

end Involution

end Involution

section OrderTwoCard

namespace OrderTwo

open Involution

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{u} k G) [IsSmoothRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

include hG hc in
omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsSmoothRep A] in
theorem act_act (x : A) : act A c (act A c x) = x := by
  change A.ρ c (A.ρ c x) = x
  rw [← Module.End.mul_apply, ← map_mul, mul_self_eq_one hG hc, map_one, Module.End.one_apply]

variable [Finite A]

include hG hc in
theorem finite_cohomology_one : Finite (cohomology A 1) :=
  Finite.of_equiv _ (h1EquivOfOrderTwo A hG hc).toEquiv

include hG hc in
theorem finite_cohomology_two : Finite (cohomology A 2) :=
  Finite.of_equiv _ (h2EquivOfOrderTwo A hG hc).toEquiv

include hG hc in
/-- For a group of order two and a finite module, `#H¹ = #H²`. -/
theorem card_cohomology_one_eq_card_cohomology_two :
    Nat.card (cohomology A 1) = Nat.card (cohomology A 2) := by
  rw [← Nat.card_congr (h1EquivOfOrderTwo A hG hc).toEquiv,
    ← Nat.card_congr (h2EquivOfOrderTwo A hG hc).toEquiv]
  exact card_tateQuot_neg (act_act A hG hc)

include hG hc in
/-- For a group of order two and a finite module, the Euler characteristic is `#H⁰`. -/
theorem eulerCharacteristic_eq_card_cohomology_zero :
    eulerCharacteristic A = Nat.card (cohomology A 0) := by
  have := finite_cohomology_one A hG hc
  have h1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := cohomology A 1)).ne'
  rw [eulerCharacteristic_eq, ← card_cohomology_one_eq_card_cohomology_two A hG hc]
  field_simp

end OrderTwo

end OrderTwoCard

section RealPlace

variable {K : Type u} [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
  (A : Rep.{u} (ULift.{u} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion)) [IsSmoothRep A]
  [Finite A]

include hw in
/-- At a real place `w`, `#H¹(K_w, A) = #H²(K_w, A)` for a finite module `A`. -/
theorem card_cohomology_one_eq_card_cohomology_two_of_isReal :
    Nat.card (cohomology A 1) = Nat.card (cohomology A 2) :=
  OrderTwo.card_cohomology_one_eq_card_cohomology_two A (eq_one_or_eq_closureConj w hw)
    (closureConj_ne_one w hw)

include hw in
/-- At a real place `w`, the Euler characteristic of a finite module `A` is `#H⁰(K_w, A)`. -/
theorem eulerCharacteristic_eq_card_cohomology_zero_of_isReal :
    eulerCharacteristic A = Nat.card (cohomology A 0) :=
  OrderTwo.eulerCharacteristic_eq_card_cohomology_zero A (eq_one_or_eq_closureConj w hw)
    (closureConj_ne_one w hw)

include hw in
/-- At a real place `w`, the cohomology of a finite module is finite in degrees `≤ 2`. -/
theorem finite_cohomology_of_isReal (n : ℕ) (hn : n ≤ 2) : Finite (cohomology A n) := by
  interval_cases n
  · exact Finite.of_equiv _ (zeroIso A).toLinearEquiv.toEquiv.symm
  · exact OrderTwo.finite_cohomology_one A (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw)
  · exact OrderTwo.finite_cohomology_two A (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw)

end RealPlace

section Cardinalities

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem card_cohomology_eq_of_iso {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (e : A ≅ B) (q : ℕ) : Nat.card (cohomology A q) = Nat.card (cohomology B q) := by
  let i : cohomology A q ≅ cohomology B q :=
    { hom := coeffMap e.hom q
      inv := coeffMap e.inv q
      hom_inv_id := by rw [← coeffMap_comp, e.hom_inv_id, coeffMap_id]
      inv_hom_id := by rw [← coeffMap_comp, e.inv_hom_id, coeffMap_id] }
  exact Nat.card_congr i.toLinearEquiv.toEquiv

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem card_eq_of_iso {A B : Rep.{u} k G} (e : A ≅ B) : Nat.card A = Nat.card B :=
  Nat.card_congr ((forget (Rep.{u} k G)).mapIso e).toEquiv

theorem card_cohomology_zero_of_subsingleton (A : Rep.{u} k G) [IsSmoothRep A] [Subsingleton A] :
    Nat.card (cohomology A 0) = 1 := by
  rw [Nat.card_congr (zeroIso A).toLinearEquiv.toEquiv]
  exact Nat.card_unique

theorem card_cohomology_zero_of_forall_eq_one (A : Rep.{u} k G) [IsSmoothRep A]
    (h : ∀ g, A.ρ g = 1) : Nat.card (cohomology A 0) = Nat.card A := by
  rw [Nat.card_congr (zeroIso A).toLinearEquiv.toEquiv]
  have hmem : ∀ x : A, x ∈ A.ρ.invariants := fun x g => by rw [h g]; rfl
  exact Nat.card_congr (Equiv.subtypeUnivEquiv hmem)

end Cardinalities

section Ratio

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]

/-- The ratio of the two sides of Tate's global Euler characteristic formula:
`χ(G_S, M) · (#M)^{#∞} / ∏_{w real} #H⁰(K_w, M)`, where `#∞` is the number of infinite places of
`K`. The formula for `M` is `globalEulerRatio ι M = 1`. -/
def globalEulerRatio : ℚ :=
  eulerCharacteristic M * (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K) /
    ∏ w : {w : InfinitePlace K // w.IsReal}, (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)

/-- A finite module of `G_S` is finite as a module of a real place. -/
instance finite_realLocalModule' [Finite M] (w : InfinitePlace K) :
    Finite (realLocalModule ι M w) :=
  inferInstanceAs (Finite M)

theorem card_cohomology_zero_realLocalModule_pos [Finite M] (w : InfinitePlace K) :
    0 < Nat.card (cohomology (realLocalModule ι M w) 0) := by
  have := finite_cohomology_zero (realLocalModule ι M w)
  exact Nat.card_pos

/-- At a real place, the Euler characteristic of a finite module is `#H⁰(K_w, M)`. -/
theorem eulerCharacteristic_realLocalModule [Finite M] (w : {w : InfinitePlace K // w.IsReal}) :
    eulerCharacteristic (realLocalModule ι M w.1) =
      Nat.card (cohomology (realLocalModule ι M w.1) 0) :=
  eulerCharacteristic_eq_card_cohomology_zero_of_isReal w.1 w.2 _

theorem prod_card_cohomology_zero_realLocalModule_ne_zero [Finite M] :
    (∏ w : {w : InfinitePlace K // w.IsReal},
      (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => by
    exact_mod_cast (card_cohomology_zero_realLocalModule_pos ι M w.1).ne'

theorem globalEulerRatio_eq_of_iso {N : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)}
    [IsSmoothRep N] (e : M ≅ N) : globalEulerRatio ι M = globalEulerRatio ι N := by
  have hw : ∀ w : {w : InfinitePlace K // w.IsReal},
      Nat.card (cohomology (realLocalModule ι M w.1) 0) =
        Nat.card (cohomology (realLocalModule ι N w.1) 0) := fun w => by
    let e' : realLocalModule ι M w.1 ≅ realLocalModule ι N w.1 :=
      (Rep.resFunctor (realLocalizationHom ι S w.1 :
        Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →*
          GaloisGroupUnramifiedOutside K Ω S)).mapIso e
    exact card_cohomology_eq_of_iso e' 0
  simp only [globalEulerRatio, eulerCharacteristic_eq_of_iso e, card_eq_of_iso e, hw]

theorem globalEulerRatio_eq_one_of_subsingleton [Subsingleton M] : globalEulerRatio ι M = 1 := by
  have hw : ∀ w : {w : InfinitePlace K // w.IsReal},
      Nat.card (cohomology (realLocalModule ι M w.1) 0) = 1 := fun w => by
    have : Subsingleton (realLocalModule ι M w.1) := inferInstanceAs (Subsingleton M)
    exact card_cohomology_zero_of_subsingleton _
  simp [globalEulerRatio, eulerCharacteristic_eq_one_of_subsingleton, hw]

theorem globalEulerRatio_eq_one_iff [Finite M] :
    globalEulerRatio ι M = 1 ↔
      eulerCharacteristic M = (∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)) /
          (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K) := by
  have h2 : (0 : ℚ) < Nat.card M := by exact_mod_cast Nat.card_pos
  have hn : (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K) ≠ 0 := (pow_pos h2 _).ne'
  unfold globalEulerRatio
  rw [div_eq_one_iff_eq (prod_card_cohomology_zero_realLocalModule_ne_zero ι M), eq_div_iff hn]

end Ratio

section Positivity

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- The Euler characteristic of a finite module of `G_S` with the places above `#M` in `S` is
positive. -/
theorem eulerCharacteristic_pos_of_mem
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    0 < eulerCharacteristic M := by
  have h0 := finite_cohomology_of_le_two M hS 0 (by norm_num)
  have h1 := finite_cohomology_of_le_two M hS 1 (by norm_num)
  have h2 := finite_cohomology_of_le_two M hS 2 (by norm_num)
  rw [eulerCharacteristic_eq]
  have p0 : (0 : ℚ) < Nat.card (cohomology M 0) := by exact_mod_cast Nat.card_pos
  have p1 : (0 : ℚ) < Nat.card (cohomology M 1) := by exact_mod_cast Nat.card_pos
  have p2 : (0 : ℚ) < Nat.card (cohomology M 2) := by exact_mod_cast Nat.card_pos
  positivity

theorem globalEulerRatio_pos
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    0 < globalEulerRatio ι M := by
  have h1 := eulerCharacteristic_pos_of_mem M hS
  have h2 : (0 : ℚ) < Nat.card M := by exact_mod_cast Nat.card_pos
  have h3 : (0 : ℚ) < ∏ w : {w : InfinitePlace K // w.IsReal},
      (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ) :=
    Finset.prod_pos fun w _ => by exact_mod_cast card_cohomology_zero_realLocalModule_pos ι M w.1
  unfold globalEulerRatio
  positivity

end Positivity

end

end Langlands.GaloisCohomology
