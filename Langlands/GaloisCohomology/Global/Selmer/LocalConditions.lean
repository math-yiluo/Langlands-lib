import Langlands.GaloisCohomology.Global.Selmer.LocalPairing

/-!
# Local conditions and their orthogonal complements

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)` and `M` a finite smooth `G_S`-module. A family of local conditions for `M`
(`LocalConditions ι M`) is a subgroup `L_v ⊆ H¹(K_v, M)` for every `v ∈ S` and a subgroup
`L_w ⊆ H¹(K_w, M)` for every real place `w`; their product is a subgroup `L.toLocalTerm` of
`P¹(M) = ∏_{v ∈ S} H¹(K_v, M) × ∏_{w real} H¹(K_w, M)` (`PoitouTate.LocalTerm`).

For `N ≥ 1` and `M' = Hom(M, μ_N)` (`PoitouTate.dual`), the dual family `L.dual N` of conditions for
`M'` is the family of orthogonal complements `L_v^⊥`, `L_w^⊥` under the local pairings
`localPairing`, `realLocalPairing` of `PoitouTate.locDual` in degrees `1 + 1`; its product is the
orthogonal complement of `L.toLocalTerm` under the sum of the local pairings
(`toLocalTerm_dual`). In the other direction `L'.predual N` is the family of left orthogonal
complements of a family `L'` for `M'`.

When `S` contains the places above `N` and `N` kills `M`, the local pairings are perfect, and:

* `(L^⊥)^⊥ = L`: `(L.dual N).predual N = L` and `(L'.predual N).dual N = L'`
  (`predual_dual`, `dual_predual`);
* `#L_v · #L_v^⊥ = #H¹(K_v, M)` and `#L_w · #L_w^⊥ = #H¹(K_w, M)`
  (`card_finite_mul_card_dual_finite`, `card_real_mul_card_dual_real`);
* the zero family and the full family are dual to each other (`dual_bot`, `dual_top`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)

/-- A family of local conditions for a smooth `G_S`-module `M`: a subgroup `L_v ⊆ H¹(K_v, M)` at
every place `v ∈ S` and a subgroup `L_w ⊆ H¹(K_w, M)` at every real place `w`. -/
@[ext]
structure LocalConditions (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
    [IsSmoothRep M] where
  /-- The condition `L_v ⊆ H¹(K_v, M)` at a place `v ∈ S`. -/
  finite : ∀ v : S, AddSubgroup (cohomology (localModule ι M v) 1)
  /-- The condition `L_w ⊆ H¹(K_w, M)` at a real place `w`. -/
  real : ∀ w : {w : InfinitePlace K // w.IsReal}, AddSubgroup (cohomology (realLocalModule ι M w.1) 1)

namespace LocalConditions

section Order

variable {ι} {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M]

/-- The families of local conditions are ordered place by place. -/
instance : PartialOrder (LocalConditions ι M) :=
  PartialOrder.lift (fun L => (L.finite, L.real)) fun L L' h => by
    cases L
    cases L'
    cases h
    rfl

theorem le_def {L L' : LocalConditions ι M} :
    L ≤ L' ↔ (∀ v, L.finite v ≤ L'.finite v) ∧ ∀ w, L.real w ≤ L'.real w :=
  Iff.rfl

/-- The family of zero conditions. -/
instance : Bot (LocalConditions ι M) :=
  ⟨⟨fun _ => ⊥, fun _ => ⊥⟩⟩

/-- The family of conditions imposing nothing. -/
instance : Top (LocalConditions ι M) :=
  ⟨⟨fun _ => ⊤, fun _ => ⊤⟩⟩

@[simp]
theorem bot_finite (v : S) : (⊥ : LocalConditions ι M).finite v = ⊥ :=
  rfl

@[simp]
theorem bot_real (w : {w : InfinitePlace K // w.IsReal}) : (⊥ : LocalConditions ι M).real w = ⊥ :=
  rfl

@[simp]
theorem top_finite (v : S) : (⊤ : LocalConditions ι M).finite v = ⊤ :=
  rfl

@[simp]
theorem top_real (w : {w : InfinitePlace K // w.IsReal}) : (⊤ : LocalConditions ι M).real w = ⊤ :=
  rfl

theorem bot_le (L : LocalConditions ι M) : ⊥ ≤ L :=
  ⟨fun _ => _root_.bot_le, fun _ => _root_.bot_le⟩

theorem le_top (L : LocalConditions ι M) : L ≤ ⊤ :=
  ⟨fun _ => _root_.le_top, fun _ => _root_.le_top⟩

/-- The product `∏_{v ∈ S} L_v × ∏_{w real} L_w ⊆ P¹(M)` of a family of local conditions. -/
def toLocalTerm (L : LocalConditions ι M) : AddSubgroup (LocalTerm ι M 1) :=
  (AddSubgroup.pi Set.univ L.finite).prod (AddSubgroup.pi Set.univ L.real)

theorem mem_toLocalTerm {L : LocalConditions ι M} {ξ : LocalTerm ι M 1} :
    ξ ∈ L.toLocalTerm ↔ (∀ v, ξ.1 v ∈ L.finite v) ∧ ∀ w, ξ.2 w ∈ L.real w := by
  rw [toLocalTerm, AddSubgroup.mem_prod, AddSubgroup.mem_pi, AddSubgroup.mem_pi]
  exact and_congr ⟨fun h v => h v trivial, fun h v _ => h v⟩ ⟨fun h w => h w trivial, fun h w _ => h w⟩

theorem toLocalTerm_mono {L L' : LocalConditions ι M} (h : L ≤ L') : L.toLocalTerm ≤ L'.toLocalTerm :=
  fun _ hξ => mem_toLocalTerm.2 ⟨fun v => (le_def.1 h).1 v ((mem_toLocalTerm.1 hξ).1 v),
    fun w => (le_def.1 h).2 w ((mem_toLocalTerm.1 hξ).2 w)⟩

/-- The product of the conditions is the product of the groups `L_v` and `L_w`. -/
def toLocalTermEquiv (L : LocalConditions ι M) :
    L.toLocalTerm ≃ (∀ v, L.finite v) × ∀ w, L.real w where
  toFun ξ := (fun v => ⟨ξ.1.1 v, (mem_toLocalTerm.1 ξ.2).1 v⟩,
    fun w => ⟨ξ.1.2 w, (mem_toLocalTerm.1 ξ.2).2 w⟩)
  invFun η := ⟨(fun v => η.1 v, fun w => η.2 w),
    mem_toLocalTerm.2 ⟨fun v => (η.1 v).2, fun w => (η.2 w).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `#L = ∏_{v ∈ S} #L_v · ∏_{w real} #L_w`. -/
theorem card_toLocalTerm [Finite S] (L : LocalConditions ι M) :
    Nat.card L.toLocalTerm = letI : Fintype S := Fintype.ofFinite S
      (∏ v : S, Nat.card (L.finite v)) * ∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (L.real w) := by
  let _ : Fintype S := Fintype.ofFinite S
  rw [Nat.card_congr L.toLocalTermEquiv, Nat.card_prod, Nat.card_pi, Nat.card_pi]

@[simp]
theorem toLocalTerm_bot : (⊥ : LocalConditions ι M).toLocalTerm = ⊥ := by
  ext ξ
  rw [mem_toLocalTerm, AddSubgroup.mem_bot, Prod.ext_iff, funext_iff, funext_iff]
  rfl

@[simp]
theorem toLocalTerm_top : (⊤ : LocalConditions ι M).toLocalTerm = ⊤ := by
  ext ξ
  simp only [mem_toLocalTerm, top_finite, top_real, AddSubgroup.mem_top, implies_true, and_self]

end Order

section Dual

variable {ι} (N : ℕ) {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)}
  [IsSmoothRep M] [Finite M]

/-- The dual family `L^⊥` of conditions for `M' = Hom(M, μ_N)`: the orthogonal complements
`L_v^⊥ ⊆ H¹(K_v, M')`, `L_w^⊥ ⊆ H¹(K_w, M')` under the local pairings of `PoitouTate.locDual`. -/
def dual (L : LocalConditions ι M) : LocalConditions ι (PoitouTate.dual N M) where
  finite v := rightOrthogonal (localPairing ι N M v) (L.finite v)
  real w := rightOrthogonal (realLocalPairing ι N M w) (L.real w)

theorem dual_finite (L : LocalConditions ι M) (v : S) :
    (L.dual N).finite v = rightOrthogonal (localPairing ι N M v) (L.finite v) :=
  rfl

theorem dual_real (L : LocalConditions ι M) (w : {w : InfinitePlace K // w.IsReal}) :
    (L.dual N).real w = rightOrthogonal (realLocalPairing ι N M w) (L.real w) :=
  rfl

/-- The family `⊥L'` of conditions for `M` orthogonal to a family `L'` of conditions for
`M' = Hom(M, μ_N)`: the left orthogonal complements under the local pairings. -/
def predual (L' : LocalConditions ι (PoitouTate.dual N M)) : LocalConditions ι M where
  finite v := leftOrthogonal (localPairing ι N M v) (L'.finite v)
  real w := leftOrthogonal (realLocalPairing ι N M w) (L'.real w)

theorem predual_finite (L' : LocalConditions ι (PoitouTate.dual N M)) (v : S) :
    (L'.predual N).finite v = leftOrthogonal (localPairing ι N M v) (L'.finite v) :=
  rfl

theorem predual_real (L' : LocalConditions ι (PoitouTate.dual N M))
    (w : {w : InfinitePlace K // w.IsReal}) :
    (L'.predual N).real w = leftOrthogonal (realLocalPairing ι N M w) (L'.real w) :=
  rfl

theorem dual_anti {L L' : LocalConditions ι M} (h : L ≤ L') : L'.dual N ≤ L.dual N :=
  ⟨fun v => rightOrthogonal_anti _ (h.1 v), fun w => rightOrthogonal_anti _ (h.2 w)⟩

theorem le_predual_dual (L : LocalConditions ι M) : L ≤ (L.dual N).predual N :=
  ⟨fun v => le_leftOrthogonal_rightOrthogonal _ (L.finite v),
    fun w => le_leftOrthogonal_rightOrthogonal _ (L.real w)⟩

/-- The dual of the zero family is the full family. -/
@[simp]
theorem dual_bot : (⊥ : LocalConditions ι M).dual N = ⊤ :=
  LocalConditions.ext (funext fun _ => rightOrthogonal_bot _) (funext fun _ => rightOrthogonal_bot _)

variable [Finite S]

/-- The product of the dual conditions is the orthogonal complement of the product of the
conditions under the sum of the local pairings on `P¹(M) × P¹(M')`. -/
theorem toLocalTerm_dual (L : LocalConditions ι M) :
    (L.dual N).toLocalTerm = rightOrthogonal (localTermPairing ι N M) L.toLocalTerm := by
  let _ : Fintype S := Fintype.ofFinite S
  simp only [localTermPairing, toLocalTerm]
  rw [rightOrthogonal_prodPairing_prod,
    rightOrthogonal_piPairing_pi, rightOrthogonal_piPairing_pi]
  rfl

/-- The product of the left orthogonal conditions is the left orthogonal complement of the
product under the sum of the local pairings. -/
theorem toLocalTerm_predual (L' : LocalConditions ι (PoitouTate.dual N M)) :
    (L'.predual N).toLocalTerm = leftOrthogonal (localTermPairing ι N M) L'.toLocalTerm := by
  let _ : Fintype S := Fintype.ofFinite S
  simp only [localTermPairing, toLocalTerm]
  rw [leftOrthogonal_prodPairing_prod,
    leftOrthogonal_piPairing_pi, leftOrthogonal_piPairing_pi]
  rfl

end Dual

section Perfect

variable {ι} (N : ℕ) [NeZero N] {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)}
  [IsSmoothRep M] [Finite M]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (hM : ∀ m : M, N • m = 0)

attribute [local instance 2000] IsSepClosure.isGalois

include hS hM in
/-- **`(L^⊥)^⊥ = L`**: the family orthogonal to the dual family is the family itself. -/
theorem predual_dual (L : LocalConditions ι M) : (L.dual N).predual N = L := by
  have := fun v : S => finite_cohomology_localModule ι M v 1
  have := fun v : S => finite_cohomology_localModule ι (PoitouTate.dual N M) v 1
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι M w 1 (by norm_num)
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι (PoitouTate.dual N M) w 1 (by norm_num)
  exact LocalConditions.ext
    (funext fun v => leftOrthogonal_rightOrthogonal _ (bijective_localPairing ι N M hS hM v)
      (bijective_localPairing_flip ι N M hS hM v) _)
    (funext fun w => leftOrthogonal_rightOrthogonal _ (bijective_realLocalPairing ι N M hS hM w)
      (bijective_realLocalPairing_flip ι N M hS hM w) _)

include hS hM in
/-- **`(⊥L')^⊥ = L'`** for a family `L'` of conditions for `M'`. -/
theorem dual_predual (L' : LocalConditions ι (PoitouTate.dual N M)) : (L'.predual N).dual N = L' := by
  have := fun v : S => finite_cohomology_localModule ι M v 1
  have := fun v : S => finite_cohomology_localModule ι (PoitouTate.dual N M) v 1
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι M w 1 (by norm_num)
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι (PoitouTate.dual N M) w 1 (by norm_num)
  exact LocalConditions.ext
    (funext fun v => rightOrthogonal_leftOrthogonal _ (bijective_localPairing ι N M hS hM v)
      (bijective_localPairing_flip ι N M hS hM v) _)
    (funext fun w => rightOrthogonal_leftOrthogonal _ (bijective_realLocalPairing ι N M hS hM w)
      (bijective_realLocalPairing_flip ι N M hS hM w) _)

include hS hM in
/-- **`#L_v · #L_v^⊥ = #H¹(K_v, M)`** at a place `v ∈ S`. -/
theorem card_finite_mul_card_dual_finite (L : LocalConditions ι M) (v : S) :
    Nat.card (L.finite v) * Nat.card ((L.dual N).finite v) =
      Nat.card (cohomology (localModule ι M v) 1) := by
  have := finite_cohomology_localModule ι M v 1
  rw [mul_comm]
  exact card_rightOrthogonal_mul_card _ (bijective_localPairing_flip ι N M hS hM v) _

include hS hM in
/-- **`#L_w · #L_w^⊥ = #H¹(K_w, M)`** at a real place `w`. -/
theorem card_real_mul_card_dual_real (L : LocalConditions ι M)
    (w : {w : InfinitePlace K // w.IsReal}) :
    Nat.card (L.real w) * Nat.card ((L.dual N).real w) =
      Nat.card (cohomology (realLocalModule ι M w.1) 1) := by
  have := finite_cohomology_realLocalModule ι M w 1 (by norm_num)
  rw [mul_comm]
  exact card_rightOrthogonal_mul_card _ (bijective_realLocalPairing_flip ι N M hS hM w) _

include hS hM in
/-- The dual of the full family is the zero family. -/
theorem dual_top : (⊤ : LocalConditions ι M).dual N = ⊥ :=
  LocalConditions.ext (funext fun v => rightOrthogonal_top _ (bijective_localPairing_flip ι N M hS hM v).1)
    (funext fun w => rightOrthogonal_top _ (bijective_realLocalPairing_flip ι N M hS hM w).1)

end Perfect

end LocalConditions

end

end Langlands.GaloisCohomology
