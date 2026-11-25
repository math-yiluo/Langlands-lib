import Langlands.GaloisCohomology.Global.Selmer.SelmerGroup
import Langlands.GaloisCohomology.Global.PoitouTate.NineTermStatement
import Langlands.GaloisCohomology.Global.PoitouTate.NineTermProof
import Langlands.GaloisCohomology.Global.PoitouTate.Corollaries

/-!
# The exact sequence of a Selmer group

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places containing the
places above `N ≥ 1`, `M` a finite smooth `G_S`-module killed by `N`, `M' = Hom(M, μ_N)`, `L` a family
of local conditions for `M` and `L^⊥ = L.dual N` the dual family. With `X^∨ = Hom(X, ℚ/ℤ)`, the maps

* `Sel_L(M) → H¹(G_S, M)`, the inclusion;
* `H¹(G_S, M) → P¹(M)/L` (`LocalConditions.toLocalQuotient`), the localization modulo `L`;
* `P¹(M)/L → Sel_{L^⊥}(M')^∨` (`LocalConditions.localQuotientToSelmerDual`), induced by
  `PoitouTate.locDual`: the sum of the local pairings with the localizations of classes of
  `Sel_{L^⊥}(M')`, which vanishes on `L`;
* `Sel_{L^⊥}(M')^∨ → H²(G_S, M)` (`LocalConditions.selmerDualToCohomologyTwo`): a character of
  `Sel_{L^⊥}(M')` is extended to `H¹(G_S, M')` and sent by the connecting map
  `PoitouTate.connecting` of the Poitou–Tate sequence; the result does not depend on the extension
  (`selmerDualToCohomologyTwo_restrictDual`), since a character vanishing on `Sel_{L^⊥}(M')` is the
  sum of the local pairings with a family of local classes (local duality), and the connecting map
  kills those (`connecting_locDual_one` of
  `Langlands.GaloisCohomology.Global.PoitouTate.Corollaries`). Like `PoitouTate.connecting`, the definition takes no
  proof: it is `0` when the extension is not well defined, which does not happen under the
  hypotheses above;
* `H²(G_S, M) → P²(M) → H⁰(G_S, M')^∨`, the maps `PoitouTate.loc` and `PoitouTate.locDual`,

form the exact sequence

`0 → Sel_L(M) → H¹(G_S, M) → P¹(M)/L → Sel_{L^⊥}(M')^∨ → H²(G_S, M) → P²(M) → H⁰(G_S, M')^∨ → 0`

by the nine-term exact sequence of Poitou–Tate (`poitouTateNineTermStatement`): the
exactness at `P¹(M)/L` uses the exactness at `P¹(M)` and local duality (the orthogonal of
`loc(H¹(G_S, M')) ∩ L^⊥` is `loc(H¹(G_S, M)) + L`), that at `Sel_{L^⊥}(M')^∨` and at `H²(G_S, M)`
the exactness at `H¹(G_S, M')^∨` and at `H²(G_S, M)`, and the end is the end of the nine-term
sequence. Counting along it (`card_selmerGroup_mul_eq`):

`#Sel_L(M) · #P¹(M) · #H²(G_S, M) · #H⁰(G_S, M') = #H¹(G_S, M) · #Sel_{L^⊥}(M') · #P²(M) · #L`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

attribute [local instance 2000] IsSepClosure.isGalois

namespace LocalConditions

variable {ι} {N} {M} (L : LocalConditions ι M)

section Maps

/-- The localization modulo the conditions, `H¹(G_S, M) → P¹(M)/L`. -/
def toLocalQuotient : cohomology M 1 →+ LocalTerm ι M 1 ⧸ L.toLocalTerm :=
  (QuotientAddGroup.mk' L.toLocalTerm).comp (loc ι M 1)

omit [Finite S] [Finite M] in
theorem toLocalQuotient_apply (x : cohomology M 1) :
    L.toLocalQuotient x = (loc ι M 1 x : LocalTerm ι M 1 ⧸ L.toLocalTerm) :=
  rfl

omit [Finite S] [Finite M] in
/-- **Exactness at `H¹(G_S, M)`**: the Selmer group is the kernel of `H¹(G_S, M) → P¹(M)/L`. -/
theorem exact_subtype_toLocalQuotient :
    Function.Exact L.selmerGroup.subtype L.toLocalQuotient := by
  intro x
  rw [toLocalQuotient_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

variable (N)

/-- The restriction of characters `H¹(G_S, M')^∨ → Sel_{L^⊥}(M')^∨`. -/
def restrictDual :
    (cohomology (PoitouTate.dual N M) 1 →+ QZ) →+ ((L.dual N).selmerGroup →+ QZ) where
  toFun χ := χ.comp (L.dual N).selmerGroup.subtype
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Finite S] [NeZero N] in
theorem restrictDual_apply (χ : cohomology (PoitouTate.dual N M) 1 →+ QZ)
    (y : (L.dual N).selmerGroup) : L.restrictDual N χ y = χ y :=
  rfl

omit [Finite S] [NeZero N] in
/-- Characters of `Sel_{L^⊥}(M')` extend to `H¹(G_S, M')`. -/
theorem surjective_restrictDual : Function.Surjective (L.restrictDual N) :=
  surjective_restrictCharacter _

omit [NeZero N] in
/-- `locDual` kills the conditions on the Selmer group of the dual conditions. -/
theorem restrictDual_locDual_eq_zero {ξ : LocalTerm ι M 1} (hξ : ξ ∈ L.toLocalTerm) :
    L.restrictDual N (locDual ι N M (show 1 + 1 = 2 from rfl) ξ) = 0 := by
  refine AddMonoidHom.ext fun y => ?_
  rw [restrictDual_apply, AddMonoidHom.zero_apply, locDual_one_apply]
  have hy : loc ι (PoitouTate.dual N M) 1 y ∈ (L.dual N).toLocalTerm := y.2
  rw [toLocalTerm_dual] at hy
  exact hy ξ hξ

/-- The map `P¹(M)/L → Sel_{L^⊥}(M')^∨` induced by the sum of the local pairings. -/
def localQuotientToSelmerDual :
    LocalTerm ι M 1 ⧸ L.toLocalTerm →+ ((L.dual N).selmerGroup →+ QZ) :=
  QuotientAddGroup.lift L.toLocalTerm
    ((L.restrictDual N).comp (locDual ι N M (show 1 + 1 = 2 from rfl)))
    fun _ hξ => L.restrictDual_locDual_eq_zero N hξ

omit [NeZero N] in
theorem localQuotientToSelmerDual_mk (ξ : LocalTerm ι M 1) :
    L.localQuotientToSelmerDual N (ξ : LocalTerm ι M 1 ⧸ L.toLocalTerm) =
      L.restrictDual N (locDual ι N M (show 1 + 1 = 2 from rfl) ξ) :=
  rfl

open Classical in
/-- The map `Sel_{L^⊥}(M')^∨ → H²(G_S, M)`: extension of a character to `H¹(G_S, M')` followed by the
connecting map `PoitouTate.connecting`, when this is well defined, and `0` otherwise. -/
def selmerDualToCohomologyTwo : ((L.dual N).selmerGroup →+ QZ) →+ cohomology M 2 :=
  if h : Function.Surjective (L.restrictDual N) ∧
      ∀ χ, L.restrictDual N χ = 0 → PoitouTate.connecting ι N M (show 2 + 1 = 3 from rfl) χ = 0 then
    descendAddHom (L.restrictDual N) h.1 (PoitouTate.connecting ι N M (show 2 + 1 = 3 from rfl))
      fun χ hχ => h.2 χ hχ
  else 0

end Maps

section Exactness

variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (hM : ∀ m : M, N • m = 0)

variable (N) in
include hS hM in
/-- Under local duality, a character of `H¹(G_S, M')` vanishing on `Ш¹_S(M')` is the sum of the
local pairings with a family of local classes. -/
theorem exists_locDual_eq (χ : cohomology (PoitouTate.dual N M) 1 →+ QZ)
    (hχ : ∀ y ∈ sha ι (PoitouTate.dual N M) 1, χ y = 0) :
    ∃ ξ : LocalTerm ι M 1, locDual ι N M (show 1 + 1 = 2 from rfl) ξ = χ := by
  obtain ⟨ψ, hψ⟩ := QZ.exists_comp_eq_of_ker_le (loc ι (PoitouTate.dual N M) 1) χ fun y hy =>
    hχ y ((mem_sha_iff_loc_eq_zero ι _ y).2 hy)
  obtain ⟨ξ, hξ⟩ := (bijective_localTermPairing ι N M hS hM).2 ψ
  refine ⟨ξ, AddMonoidHom.ext fun y => ?_⟩
  rw [locDual_one_apply, hξ, ← hψ]
  rfl

variable (N) in
include hS hM in
/-- The map `Sel_{L^⊥}(M')^∨ → H²(G_S, M)` is the connecting map on an extension of the character. -/
theorem selmerDualToCohomologyTwo_restrictDual (χ : cohomology (PoitouTate.dual N M) 1 →+ QZ) :
    L.selmerDualToCohomologyTwo N (L.restrictDual N χ) =
      PoitouTate.connecting ι N M (show 2 + 1 = 3 from rfl) χ := by
  have h : Function.Surjective (L.restrictDual N) ∧
      ∀ χ, L.restrictDual N χ = 0 → PoitouTate.connecting ι N M (show 2 + 1 = 3 from rfl) χ = 0 := by
    refine ⟨L.surjective_restrictDual N, fun χ hχ => ?_⟩
    obtain ⟨ξ, rfl⟩ := exists_locDual_eq N hS hM χ fun y hy =>
      DFunLike.congr_fun hχ ⟨y, (L.dual N).sha_le_selmerGroup hy⟩
    exact connecting_locDual_one ι N M ξ
  rw [selmerDualToCohomologyTwo, dite_eq_left h]
  exact descendAddHom_apply _ _ _ _ χ

include hS hM in
/-- A family of local classes orthogonal to the localizations of `Sel_{L^⊥}(M')` is the localization
of a global class plus a family in `L`: the orthogonal of `loc(H¹(G_S, M')) ∩ L^⊥` is
`loc(H¹(G_S, M)) + L`. -/
theorem mem_range_loc_sup_of_locDual_eq_zero {ξ : LocalTerm ι M 1}
    (h : ∀ y ∈ (L.dual N).selmerGroup, locDual ι N M (show 1 + 1 = 2 from rfl) ξ y = 0) :
    ξ ∈ (loc ι M 1).range ⊔ L.toLocalTerm := by
  have := finite_localTerm_one ι M
  have := finite_localTerm_one ι (PoitouTate.dual N M)
  have hΦ := bijective_localTermPairing ι N M hS hM
  have hΦ' := bijective_localTermPairing_flip ι N M hS hM
  have hξ : ξ ∈ leftOrthogonal (localTermPairing ι N M)
      ((loc ι (PoitouTate.dual N M) 1).range ⊓ (L.dual N).toLocalTerm) := by
    rintro η ⟨⟨y, rfl⟩, hy⟩
    have h1 := h y hy
    rw [locDual_one_apply] at h1
    exact h1
  rwa [leftOrthogonal_inf _ hΦ hΦ', toLocalTerm_dual, leftOrthogonal_rightOrthogonal _ hΦ hΦ',
    leftOrthogonal_range_loc ι N M hS hM] at hξ

include hS hM in
/-- A family of local classes orthogonal to the localizations of `Sel_{L^⊥}(M')` is the localization
of a global class modulo `L`. -/
theorem exists_toLocalQuotient_eq {ξ : LocalTerm ι M 1}
    (h : L.restrictDual N (locDual ι N M (show 1 + 1 = 2 from rfl) ξ) = 0) :
    ∃ x, L.toLocalQuotient x = (ξ : LocalTerm ι M 1 ⧸ L.toLocalTerm) := by
  have h' : ∀ y ∈ (L.dual N).selmerGroup,
      locDual ι N M (show 1 + 1 = 2 from rfl) ξ y = 0 := fun y hy => by
    have h1 := DFunLike.congr_fun h ⟨y, hy⟩
    rw [restrictDual_apply, AddMonoidHom.zero_apply] at h1
    exact h1
  obtain ⟨a, ⟨x, hx⟩, l, hl, hal⟩ :=
    AddSubgroup.mem_sup.1 (L.mem_range_loc_sup_of_locDual_eq_zero hS hM h')
  refine ⟨x, ?_⟩
  rw [toLocalQuotient_apply, hx, ← hal]
  exact QuotientAddGroup.eq.2 (by rwa [neg_add_cancel_left])

include hS hM in
/-- The localization of a global class modulo `L` is orthogonal to the localizations of
`Sel_{L^⊥}(M')`. -/
theorem restrictDual_locDual_eq_zero_of_toLocalQuotient_eq {ξ : LocalTerm ι M 1}
    {x : cohomology M 1} (hx : L.toLocalQuotient x = (ξ : LocalTerm ι M 1 ⧸ L.toLocalTerm)) :
    L.restrictDual N (locDual ι N M (show 1 + 1 = 2 from rfl) ξ) = 0 := by
  have hl : -(loc ι M 1 x) + ξ ∈ L.toLocalTerm := QuotientAddGroup.eq.1 hx
  have h0 : locDual ι N M (show 1 + 1 = 2 from rfl) (loc ι M 1 x) = 0 :=
    ((poitouTateNineTermStatement K Ω S ι N hS M hM).exact_loc_locDual_one _).2 ⟨x, rfl⟩
  have h1 := L.restrictDual_locDual_eq_zero N hl
  rwa [map_add, map_neg, h0, neg_zero, zero_add] at h1

include hS hM in
/-- **Exactness at `P¹(M)/L`**: a family of local classes is orthogonal to the localizations of
`Sel_{L^⊥}(M')` exactly when it is the localization of a global class modulo `L`. -/
theorem exact_toLocalQuotient_localQuotientToSelmerDual :
    Function.Exact L.toLocalQuotient (L.localQuotientToSelmerDual N) := fun q =>
  QuotientAddGroup.induction_on q fun _ =>
    ⟨fun h => L.exists_toLocalQuotient_eq hS hM h,
      fun ⟨_, hx⟩ => L.restrictDual_locDual_eq_zero_of_toLocalQuotient_eq hS hM hx⟩

include hS hM in
theorem exists_localQuotientToSelmerDual_eq {χ : cohomology (PoitouTate.dual N M) 1 →+ QZ}
    (h : PoitouTate.connecting ι N M (show 2 + 1 = 3 from rfl) χ = 0) :
    ∃ q, L.localQuotientToSelmerDual N q = L.restrictDual N χ := by
  obtain ⟨ξ, hξ⟩ :=
    ((poitouTateNineTermStatement K Ω S ι N hS M hM).exact_locDual_connecting_one χ).1 h
  refine ⟨ξ, ?_⟩
  rw [localQuotientToSelmerDual_mk, hξ]

include hS hM in
theorem selmerDualToCohomologyTwo_localQuotientToSelmerDual (q : LocalTerm ι M 1 ⧸ L.toLocalTerm) :
    L.selmerDualToCohomologyTwo N (L.localQuotientToSelmerDual N q) = 0 :=
  QuotientAddGroup.induction_on q fun ξ => by
    have e : L.localQuotientToSelmerDual N (ξ : LocalTerm ι M 1 ⧸ L.toLocalTerm) =
        L.restrictDual N (locDual ι N M (show 1 + 1 = 2 from rfl) ξ) :=
      L.localQuotientToSelmerDual_mk N ξ
    rw [e, L.selmerDualToCohomologyTwo_restrictDual N hS hM]
    exact connecting_locDual_one ι N M ξ

include hS hM in
/-- **Exactness at `Sel_{L^⊥}(M')^∨`.** -/
theorem exact_localQuotientToSelmerDual_selmerDualToCohomologyTwo :
    Function.Exact (L.localQuotientToSelmerDual N) (L.selmerDualToCohomologyTwo N) := by
  intro φ
  obtain ⟨χ, rfl⟩ := L.surjective_restrictDual N φ
  constructor
  · intro h
    rw [L.selmerDualToCohomologyTwo_restrictDual N hS hM] at h
    exact L.exists_localQuotientToSelmerDual_eq hS hM h
  · intro h
    obtain ⟨q, hq⟩ := h
    rw [← hq]
    exact L.selmerDualToCohomologyTwo_localQuotientToSelmerDual hS hM q

include hS hM in
/-- **Exactness at `H²(G_S, M)`.** -/
theorem exact_selmerDualToCohomologyTwo_loc :
    Function.Exact (L.selmerDualToCohomologyTwo N) (loc ι M 2) := by
  intro z
  rw [(poitouTateNineTermStatement K Ω S ι N hS M hM).exact_connecting_loc_two z]
  constructor
  · rintro ⟨χ, rfl⟩
    exact ⟨L.restrictDual N χ, L.selmerDualToCohomologyTwo_restrictDual N hS hM χ⟩
  · rintro ⟨φ, rfl⟩
    obtain ⟨χ, rfl⟩ := L.surjective_restrictDual N φ
    exact ⟨χ, (L.selmerDualToCohomologyTwo_restrictDual N hS hM χ).symm⟩

include hS hM in
/-- **The count of the exact sequence**:
`#Sel_L(M) · #P¹(M) · #H²(G_S, M) · #H⁰(G_S, M') = #H¹(G_S, M) · #Sel_{L^⊥}(M') · #P²(M) · #L`. -/
theorem card_selmerGroup_mul_eq :
    Nat.card L.selmerGroup * Nat.card (LocalTerm ι M 1) * Nat.card (cohomology M 2) *
        Nat.card (cohomology (PoitouTate.dual N M) 0) =
      Nat.card (cohomology M 1) * Nat.card (L.dual N).selmerGroup * Nat.card (LocalTerm ι M 2) *
        Nat.card L.toLocalTerm := by
  have hNT := poitouTateNineTermStatement K Ω S ι N hS M hM
  have hSM := mem_of_natCard_mem_of_nsmul_eq_zero hS hM
  have hSM' := mem_of_natCard_mem_of_nsmul_eq_zero hS
    (nsmul_dualRep_eq_zero (nsmul_dualizingModule S N) (M := M))
  have := finite_cohomology_of_le_two (PoitouTate.dual N M) hSM' 1 (by norm_num)
  have : Finite (cohomology (PoitouTate.dual N M) 0) := finite_cohomology_zero _
  have h7 := card_mul_card_eq_of_exact_seven L.selmerGroup.subtype L.toLocalQuotient
    (L.localQuotientToSelmerDual N) (L.selmerDualToCohomologyTwo N) (loc ι M 2)
    (locDual ι N M (show 2 + 0 = 2 from rfl)) L.selmerGroup.subtype_injective
    L.exact_subtype_toLocalQuotient
    (L.exact_toLocalQuotient_localQuotientToSelmerDual hS hM)
    (L.exact_localQuotientToSelmerDual_selmerDualToCohomologyTwo hS hM)
    (L.exact_selmerDualToCohomologyTwo_loc hS hM) hNT.exact_loc_locDual_two
    hNT.surjective_locDual_two
  rw [QZ.card_hom, QZ.card_hom] at h7
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup L.toLocalTerm]
  calc Nat.card L.selmerGroup * (Nat.card (LocalTerm ι M 1 ⧸ L.toLocalTerm) *
          Nat.card L.toLocalTerm) * Nat.card (cohomology M 2) *
          Nat.card (cohomology (PoitouTate.dual N M) 0)
        = Nat.card L.selmerGroup * Nat.card (LocalTerm ι M 1 ⧸ L.toLocalTerm) *
            Nat.card (cohomology M 2) * Nat.card (cohomology (PoitouTate.dual N M) 0) *
              Nat.card L.toLocalTerm := by ring
      _ = _ := by rw [h7]

end Exactness

end LocalConditions

end

end Langlands.GaloisCohomology
