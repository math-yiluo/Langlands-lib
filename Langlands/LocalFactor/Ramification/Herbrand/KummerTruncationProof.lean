import Langlands.LocalFactor.Ramification.Herbrand.KummerTowerStatement
import Langlands.LocalFactor.Ramification.Herbrand.SlopeProof

/-!
# The truncation lemma for the relative inverse Herbrand function

If `G_F^μ` acts transitively on the `F`-embeddings of a finite subextension `E`, that is
`G_E ⊔ G_F^μ = G_F`, then `ψ_{E/F}` is the identity on `[-1, μ]`.

In the Galois closure `M` of `E`, with `G = Gal(M/F)` and `H = Gal(M/E)`, the hypothesis
becomes `H ⊔ G^μ = G`. Every lower group `G_j` with `G_j ⊇ G^μ` is normal and satisfies
`H ⊔ G_j = G`, so `[G_j : H ∩ G_j] = [G : H]`. Hence the lower orders over `E` are those
over `F` divided by the constant `[G : H]` up to the lower index `ψ_{M/F}(μ)`, and the two
Herbrand functions `φ_{M/E}` and `φ_{M/F}` agree there. Therefore
`ψ_{E/F} = φ_{M/E} ∘ ψ_{M/F}` is the identity up to `μ`.
-/

noncomputable section

namespace Langlands.Ramification.Kummer

open _root_.Langlands.Ramification.Herbrand
open _root_.Langlands.Ramification.HerbrandBridge

universe u uK uE uL

section Orders

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (K : Type uK) [Field K] [Algebra (Padic p) K]
  (E : Type uE) [Field E] [Algebra (Padic p) E] {L : PadicField.{uL} p}
  [Algebra K E] [Algebra E L.Carrier] [Algebra K L.Carrier]
  [IsScalarTower K E L.Carrier]
  [IsScalarTower (Padic p) K L.Carrier] [IsScalarTower (Padic p) E L.Carrier]
  (T : L.TopologicalData)

/-- If `Gal(L/E)` and the lower group of real index `u₀` generate `Gal(L/K)`, then every
lower group `G_j` with `j - 1 < u₀` has order `[G : H]` times that of its subgroup over `E`. -/
theorem lowerGroupOrder_subfield_mul_index_of_sup_eq_top {u₀ : ℝ}
    (hH : (AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range ⊔
      Padic.lowerRamificationGroupReal T K u₀ = ⊤)
    {j : ℕ} (hj : (j : ℝ) - 1 < u₀) :
    (Padic.lowerGroupOrder T E j : ℝ) *
        (AlgEquiv.restrictScalarsHom K :
          (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range.index =
      Padic.lowerGroupOrder T K j := by
  set H := (AlgEquiv.restrictScalarsHom K :
    (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range
  have hle : Padic.lowerRamificationGroupReal T K u₀ ≤ Padic.lowerRamificationGroup T K j := by
    rw [← Padic.lowerRamificationGroupReal_nat]
    show Padic.lowerRamificationGroupInt T K ⌈u₀⌉ ≤
      Padic.lowerRamificationGroupInt T K ⌈((j : ℕ) : ℝ)⌉
    apply Padic.lowerRamificationGroupInt_antitone
    rw [Int.ceil_natCast]
    exact Int.le_ceil_iff.mpr (by push_cast; linarith)
  have hsup : H ⊔ Padic.lowerRamificationGroup T K j = ⊤ :=
    top_le_iff.mp (hH ▸ sup_le_sup_left hle H)
  have h := lowerGroupOrder_subfield_mul_relIndex K E T j
  rw [← relIndex_sup_of_normal, hsup, Subgroup.relIndex_top_right] at h
  exact_mod_cast h

/-- If `Gal(L/E)` and the lower group of real index `u₀` generate `Gal(L/K)`, then the
Herbrand functions over `E` and over `K` agree on `[0, u₀]`. -/
theorem herbrandPhi_eq_of_sup_eq_top {u₀ : ℝ}
    (hH : (AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range ⊔
      Padic.lowerRamificationGroupReal T K u₀ = ⊤)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ u₀) :
    Padic.herbrandPhi T E u = Padic.herbrandPhi T K u := by
  set H := (AlgEquiv.restrictScalarsHom K :
    (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range
  set B := max (ramificationCutoff T K) (max (ramificationCutoff T E) ⌈u⌉₊)
  have hBK : ramificationCutoff T K ≤ B := le_max_left _ _
  have hBE : ramificationCutoff T E ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have huB : u ≤ B := (Nat.le_ceil u).trans (by exact_mod_cast
    (le_max_right _ _ : ⌈u⌉₊ ≤ max (ramificationCutoff T E) ⌈u⌉₊).trans (le_max_right _ _))
  have hsum : rampSum (fun i => (Padic.lowerGroupOrder T K i : ℝ)) B u =
      rampSum (fun i => (Padic.lowerGroupOrder T E i : ℝ)) B u * H.index := by
    unfold rampSum
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    by_cases hi : (i : ℝ) < u
    · rw [← lowerGroupOrder_subfield_mul_index_of_sup_eq_top K E T hH
        (j := i + 1) (by push_cast; linarith)]
      ring
    · rw [ramp_eq_zero (not_lt.mp hi)]
      ring
  have h0 := lowerGroupOrder_subfield_mul_index_of_sup_eq_top K E T hH (j := 0)
    (by push_cast; linarith)
  have hg0 : (0 : ℝ) < Padic.lowerGroupOrder T K 0 := by
    exact_mod_cast lowerGroupOrder_pos T K 0
  have hc : (H.index : ℝ) ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at h0
    exact hg0.ne h0
  rw [herbrandPhi_eq_sum T K hBK hu0 huB, herbrandPhi_eq_sum T E hBE hu0 huB, hsum, ← h0,
    mul_div_mul_right _ _ hc]

/-- If `Gal(L/E)` and the upper group of index `v₀` generate `Gal(L/K)`, then
`φ_{L/E} ∘ ψ_{L/K}` is the identity on `(-∞, v₀]`. -/
theorem herbrandPhi_herbrandPsi_eq_self_of_sup_eq_top {v₀ : ℝ}
    (hH : (AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range ⊔
      Padic.upperRamificationGroup T K v₀ = ⊤)
    {x : ℝ} (hx : x ≤ v₀) :
    Padic.herbrandPhi T E (Padic.herbrandPsi T K x) = x := by
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [Padic.herbrandPsi_of_nonpos T K hx0, Padic.herbrandPhi_of_nonpos T E hx0]
  · have hu0 : 0 ≤ Padic.herbrandPsi T K x := (Padic.herbrandPsi_pos T K hx0).le
    rw [herbrandPhi_eq_of_sup_eq_top K E T (u₀ := Padic.herbrandPsi T K v₀) hH hu0
      ((Padic.herbrandPsi_strictMono T K).monotone hx), Padic.herbrandPhi_herbrandPsi]

end Orders

section Relative

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p) {K : PadicField.{uE} p}
  {Ω : Type uL} [Field Ω] [Algebra F.Carrier Ω] [Algebra K.Carrier Ω] [Algebra (Padic p) Ω]
  [Algebra F.Carrier K.Carrier] [IsScalarTower F.Carrier K.Carrier Ω]
  [IsScalarTower (Padic p) F.Carrier Ω] [IsScalarTower (Padic p) K.Carrier Ω]

attribute [local instance] extension_padicScalarTower

variable {M : FiniteGaloisIntermediateField F.Carrier Ω}
  (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField)

/-- If `Gal(M/K)` and the upper group of `M/F` of index `v₀` generate `Gal(M/F)`, the relative
index is the identity on `(-∞, v₀]`. -/
theorem relativeIndex_eq_self_of_sup_eq_top {v₀ : ℝ}
    (hH : relativeSubgroup F h ⊔ Padic.upperRamificationGroup
        (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData
          F.Carrier v₀ = ⊤)
    {x : ℝ} (hx : x ≤ v₀) :
    relativeIndex F M h x = x :=
  herbrandPhi_herbrandPsi_eq_self_of_sup_eq_top F.Carrier K.Carrier _ hH hx

end Relative

section Absolute

open LocalClassField _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {K : PadicField.{uE} p}
  [Algebra K.Carrier (AlgebraicClosure F.Carrier)] [Algebra F.Carrier K.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower (Padic p) K.Carrier (AlgebraicClosure F.Carrier)]

attribute [local instance] extension_padicScalarTower

variable {M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)}
  (h : ∀ x : K.Carrier, algebraMap K.Carrier (AlgebraicClosure F.Carrier) x ∈
    M.toIntermediateField)

/-- The restriction from the absolute Galois group of `F` to `Gal(M/F)` is onto. -/
theorem map_absoluteRelativeRestriction_top :
    (⊤ : Subgroup (Field.absoluteGaloisGroup F.Carrier)).map
      (absoluteRelativeRestriction F h) = ⊤ := by
  have key := map_absoluteRelativeRestriction_upper F h (le_refl (-1 : ℝ))
  rw [absoluteUpperRamificationGroup_neg_one, Padic.upperRamificationGroup_neg_one] at key
  exact key

/-- Generation of the absolute Galois group by the preimage of `Gal(M/K)` and `G_F^v`
descends to generation of `Gal(M/F)` by `Gal(M/K)` and the upper group of `M/F`. -/
theorem relativeSubgroup_sup_upper_eq_top {v : ℝ} (hv : -1 ≤ v)
    (hG : (relativeSubgroup F h).comap (absoluteRelativeRestriction F h) ⊔
      absoluteUpperRamificationGroup F v = ⊤) :
    relativeSubgroup F h ⊔ Padic.upperRamificationGroup
        (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData
          F.Carrier v = ⊤ := by
  apply top_unique
  rw [← map_absoluteRelativeRestriction_top F h, ← hG, Subgroup.map_sup,
    map_absoluteRelativeRestriction_upper F h hv]
  exact sup_le_sup_right (Subgroup.map_comap_le _ _) _

end Absolute

section Intermediate

open LocalClassField _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (E : FiniteIntermediateExtension F.Carrier)

attribute [local instance] asPadicField_isScalarTower

/-- If `G_E ⊔ G_F^μ = G_F` with `μ ≥ -1`, then `ψ_{E/F}(x) = x` for every `x ≤ μ`. -/
theorem relativeHerbrandPsi_eq_self_of_sup_eq_top {μ : ℝ} (hμ : -1 ≤ μ)
    (hG : E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤)
    {x : ℝ} (hx : x ≤ μ) :
    relativeHerbrandPsi E x = x := by
  have hcomap := comap_absoluteRelativeRestriction_galoisClosure E
  refine relativeIndex_eq_self_of_sup_eq_top F (algebraMap_mem_galoisClosure E)
    (relativeSubgroup_sup_upper_eq_top F (algebraMap_mem_galoisClosure E) hμ ?_) hx
  rw [hcomap]
  exact hG

end Intermediate

/-- The truncation lemma (route note, Lemma `lem:trunc`): if `G_F^μ` acts transitively on the
`F`-embeddings of `E`, then `ψ_{E/F}` is the identity on `[-1, μ]`. -/
theorem herbrandPsiTruncation : HerbrandPsiTruncationStatement.{u} := by
  intro p _ F E μ hG x hx1 hxμ
  exact relativeHerbrandPsi_eq_self_of_sup_eq_top E (hx1.trans hxμ) hG hxμ

end Langlands.Ramification.Kummer
