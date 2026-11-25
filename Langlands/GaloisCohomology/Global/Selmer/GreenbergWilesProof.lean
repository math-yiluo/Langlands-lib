import Langlands.GaloisCohomology.Global.Selmer.GreenbergWilesStatement
import Langlands.GaloisCohomology.Global.Selmer.ExactSequence
import Langlands.GaloisCohomology.Global.Selmer.LocalCount
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Proof

/-!
# The formula of Greenberg and Wiles: proof

This file proves `GreenbergWilesStatement` (`greenbergWilesStatement`), the way of
Neukirch–Schmidt–Wingberg (8.7.9) with the end of the nine-term sequence of Poitou–Tate in place of
its beginning:

* the exact sequence `0 → Sel_L(M) → H¹(G_S, M) → P¹(M)/L → Sel_{L^⊥}(M')^∨ → H²(G_S, M) → P²(M)
  → H⁰(G_S, M')^∨ → 0` of `Langlands.GaloisCohomology.Global.Selmer.ExactSequence` (from the
  nine-term sequence, `poitouTateNineTermStatement`, and local duality) gives
  `#Sel_L(M) · #P¹(M) · #H²(G_S, M) · #H⁰(G_S, M') = #H¹(G_S, M) · #Sel_{L^⊥}(M') · #P²(M) · #L`;
* the global Euler characteristic formula (`card_cohomology_one_mul_prod`) gives `#H¹(G_S, M) · ∏_{w real} #H⁰(K_w, M) = #H⁰(G_S, M) · #H²(G_S, M) · (#M)^{r₁ + r₂}`;
* the local Euler characteristic at the places of `S` with the product formula gives
  `∏_{v ∈ S} #H¹(K_v, M) = ∏_{v ∈ S} #H⁰(K_v, M) · #H²(K_v, M) · (#M)^{r₁ + 2r₂}`
  (`prod_card_cohomology_one_localModule`), and the Herbrand quotient at the real places
  `#H¹(K_w, M) = #H²(K_w, M)`.

Combining, `#Sel_L(M) · #H⁰(G_S, M') · ∏_{v ∈ S} #H⁰(K_v, M) · ∏_{w real} #H⁰(K_w, M) · (#M)^{r₂} =
#Sel_{L^⊥}(M') · #H⁰(G_S, M) · ∏_{v ∈ S} #L_v · ∏_{w real} #L_w`
(`LocalConditions.card_selmerGroup_mul_eq_card_selmerGroup_dual_mul`), which is the formula
(`LocalConditions.card_selmerGroup_div_card_selmerGroup_dual`, `greenbergWilesStatement`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

section Counts

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

attribute [local instance 2000] IsSepClosure.isGalois

omit [Finite M] in
/-- `#Pⁿ(M) = ∏_{v ∈ S} #Hⁿ(K_v, M) · ∏_{w real} #Hⁿ(K_w, M)`. -/
theorem card_localTerm (n : ℕ) :
    Nat.card (LocalTerm ι M n) = letI : Fintype S := Fintype.ofFinite S
      (∏ v : S, Nat.card (cohomology (localModule ι M v) n)) *
        ∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (cohomology (realLocalModule ι M w.1) n) := by
  let _ : Fintype S := Fintype.ofFinite S
  rw [Nat.card_prod, Nat.card_pi, Nat.card_pi]

/-- The local Euler characteristic over the places of `S`, with the product formula:
`∏_{v ∈ S} #H¹(K_v, M) = ∏_{v ∈ S} #H⁰(K_v, M) · ∏_{v ∈ S} #H²(K_v, M) · (#M)^{[K : ℚ]}` when `S`
contains the places above `#M`. -/
theorem prod_card_cohomology_one_localModule
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    letI : Fintype S := Fintype.ofFinite S
    ∏ v : S, Nat.card (cohomology (localModule ι M v) 1) =
      (∏ v : S, Nat.card (cohomology (localModule ι M v) 0)) *
        (∏ v : S, Nat.card (cohomology (localModule ι M v) 2)) *
          Nat.card M ^ Module.finrank ℚ K := by
  let _ : Fintype S := Fintype.ofFinite S
  rw [Finset.prod_congr rfl fun (v : S) _ =>
      card_cohomology_one_localModule ι M (v : HeightOneSpectrum (𝓞 K)),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ClassFieldTheory.Global.prod_card_quotient_natCast_eq Nat.card_pos.ne' hS]

omit [Finite S] in
/-- The Herbrand quotient at the real places: `∏_{w real} #H¹(K_w, M) = ∏_{w real} #H²(K_w, M)`. -/
theorem prod_card_cohomology_one_realLocalModule :
    ∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (cohomology (realLocalModule ι M w.1) 1) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (cohomology (realLocalModule ι M w.1) 2) :=
  Finset.prod_congr rfl fun w _ =>
    card_cohomology_one_eq_card_cohomology_two_of_isReal w.1 w.2 (realLocalModule ι M w.1)

end Counts

section GreenbergWiles

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ι : PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M] [Finite M]

attribute [local instance 2000] IsSepClosure.isGalois

namespace LocalConditions

/-- **The formula of Greenberg and Wiles**, multiplied out:
`#Sel_L(M) · #H⁰(G_S, M') · ∏_{v ∈ S} #H⁰(K_v, M) · ∏_{w real} #H⁰(K_w, M) · (#M)^{r₂} =
#Sel_{L^⊥}(M') · #H⁰(G_S, M) · ∏_{v ∈ S} #L_v · ∏_{w real} #L_w`. -/
theorem card_selmerGroup_mul_eq_card_selmerGroup_dual_mul
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (L : LocalConditions ι M) :
    letI : Fintype S := Fintype.ofFinite S
    Nat.card L.selmerGroup * Nat.card (cohomology (PoitouTate.dual N M) 0) *
        (∏ v : S, Nat.card (cohomology (localModule ι M v) 0)) *
        (∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (cohomology (realLocalModule ι M w.1) 0)) *
        Nat.card M ^ InfinitePlace.nrComplexPlaces K =
      Nat.card (L.dual N).selmerGroup * Nat.card (cohomology M 0) *
        (∏ v : S, Nat.card (L.finite v)) *
        ∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (L.real w) := by
  let _ : Fintype S := Fintype.ofFinite S
  have hSM := mem_of_natCard_mem_of_nsmul_eq_zero hS hM
  have hA := L.card_selmerGroup_mul_eq hS hM
  have hB := card_cohomology_one_mul_prod ι M hSM
  rw [card_localTerm, card_localTerm, card_toLocalTerm, prod_card_cohomology_one_localModule ι M hSM,
    prod_card_cohomology_one_realLocalModule] at hA
  rw [← InfinitePlace.card_add_two_mul_card_eq_rank] at hA
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces] at hB
  -- the factor to cancel is positive
  have := finite_cohomology_of_le_two M hSM 2 (by norm_num)
  have := fun v : S => finite_cohomology_localModule ι M v 2
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι M w 2 (by norm_num)
  have hc : 0 < (∏ v : S, Nat.card (cohomology (localModule ι M v) 2)) *
      (∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (cohomology (realLocalModule ι M w.1) 2)) *
        Nat.card (cohomology M 2) *
          Nat.card M ^ (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Finset.prod_pos fun v _ => Nat.card_pos)
      (Finset.prod_pos fun w _ => Nat.card_pos)) Nat.card_pos) (pow_pos Nat.card_pos _)
  refine Nat.eq_of_mul_eq_mul_right hc ?_
  zify at hA hB ⊢
  linear_combination
    (∏ w : {w : InfinitePlace K // w.IsReal},
      (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℤ)) * hA +
    ((Nat.card (L.dual N).selmerGroup : ℤ) *
      (∏ v : S, (Nat.card (cohomology (localModule ι M v) 2) : ℤ)) *
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι M w.1) 2) : ℤ)) *
      ((∏ v : S, (Nat.card (L.finite v) : ℤ)) *
        ∏ w : {w : InfinitePlace K // w.IsReal}, (Nat.card (L.real w) : ℤ))) * hB

/-- **The formula of Greenberg and Wiles**:
`#Sel_L(M) / #Sel_{L^⊥}(M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ S} #L_v / #H⁰(K_v, M)
· ∏_{w real} #L_w / #H⁰(K_w, M) / (#M)^{r₂}`. -/
theorem card_selmerGroup_div_card_selmerGroup_dual
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (L : LocalConditions ι M) :
    letI : Fintype S := Fintype.ofFinite S
    (Nat.card L.selmerGroup : ℚ) / Nat.card (L.dual N).selmerGroup =
      (Nat.card (cohomology M 0) : ℚ) / Nat.card (cohomology (PoitouTate.dual N M) 0) *
        (∏ v : S, (Nat.card (L.finite v) : ℚ) / Nat.card (cohomology (localModule ι M v) 0)) *
        (∏ w : {w : InfinitePlace K // w.IsReal},
          (Nat.card (L.real w) : ℚ) / Nat.card (cohomology (realLocalModule ι M w.1) 0)) /
        (Nat.card M : ℚ) ^ InfinitePlace.nrComplexPlaces K := by
  let _ : Fintype S := Fintype.ofFinite S
  have key := L.card_selmerGroup_mul_eq_card_selmerGroup_dual_mul hS hM
  have hSM' := mem_of_natCard_mem_of_nsmul_eq_zero hS
    (nsmul_dualRep_eq_zero (nsmul_dualizingModule S N) (M := M))
  have := finite_cohomology_of_le_two (PoitouTate.dual N M) hSM' 1 (by norm_num)
  have : Finite (cohomology (PoitouTate.dual N M) 0) := finite_cohomology_zero _
  have := fun v : S => finite_cohomology_localModule ι M v 0
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι M w 0 (by norm_num)
  have hY : (Nat.card (L.dual N).selmerGroup : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have ha' : (Nat.card (cohomology (PoitouTate.dual N M) 0) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : ∀ v : S, (Nat.card (cohomology (localModule ι M v) 0) : ℚ) ≠ 0 := fun v =>
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hR : ∀ w : {w : InfinitePlace K // w.IsReal},
      (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ) ≠ 0 := fun w =>
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF0 : (∏ v : S, (Nat.card (cohomology (localModule ι M v) 0) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => hF v
  have hR0 : (∏ w : {w : InfinitePlace K // w.IsReal},
      (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => hR w
  have hm : (Nat.card M : ℚ) ^ InfinitePlace.nrComplexPlaces K ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have key' : (Nat.card L.selmerGroup : ℚ) * Nat.card (cohomology (PoitouTate.dual N M) 0) *
      (∏ v : S, (Nat.card (cohomology (localModule ι M v) 0) : ℚ)) *
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)) *
      (Nat.card M : ℚ) ^ InfinitePlace.nrComplexPlaces K =
    Nat.card (L.dual N).selmerGroup * Nat.card (cohomology M 0) *
      (∏ v : S, (Nat.card (L.finite v) : ℚ)) *
      ∏ w : {w : InfinitePlace K // w.IsReal}, (Nat.card (L.real w) : ℚ) := by
    exact_mod_cast key
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, div_eq_iff hY]
  field_simp
  linear_combination key'

end LocalConditions

/-- **The formula of Greenberg and Wiles.** -/
theorem greenbergWilesStatement : GreenbergWilesStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι N _ hS M _ _ hM L
  exact L.card_selmerGroup_div_card_selmerGroup_dual hS hM

end GreenbergWiles

end

end Langlands.GaloisCohomology
