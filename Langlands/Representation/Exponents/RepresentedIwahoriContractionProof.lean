import Langlands.Representation.Exponents.RepresentedIwahoriDecompositionStatements
import Langlands.Representation.Exponents.SplitComponentOppositeContractionProof
import Langlands.Representation.Exponents.LeviJacquetOppositePairingStructure
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter

/-! # Contracting powers for compact open subgroups with an Iwahori decomposition: proof

Proof of `RepresentedIwahoriContractionStatement` (derived from Renard 2026, V.5.2 and the
first step of the proofs of VI.6.1 and VI.9.1). A point of `A^{++}` is the uniformizer value
of the presentation's split-component cocharacter; the contraction fields come from the
proved `splitComponentOppositeContraction` applied to `K ∩ N(F)`, `K ∩ N̄(F)` and points of
`N(F)`, together with the centrality of `A(F)` in `M(F)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

namespace IwahoriContractionPowers

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] (A : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The normalized norm of a character is multiplicative in the point. -/
theorem characterNorm_pow (α : characterLattice A) (t : rationalPoints A.toGrp) (j : ℕ) :
    CocharacterUniformizer.characterNorm k A α (t ^ j) =
      CocharacterUniformizer.characterNorm k A α t ^ j := by
  simp [CocharacterUniformizer.characterNorm, map_pow]

theorem characterNorm_nonneg (α : characterLattice A) (t : rationalPoints A.toGrp) :
    0 ≤ CocharacterUniformizer.characterNorm k A α t :=
  NNReal.coe_nonneg _

/-- If every character of a finite set has norm `< 1` at `t`, then for every `ε > 0` all
sufficiently large powers of `t` have norm `< ε` at every character of the set. -/
theorem exists_pow_characterNorm_lt {Δ : Set (characterLattice A)} (hΔ : Δ.Finite)
    {t : rationalPoints A.toGrp}
    (ht : ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α (t ^ j) < ε := by
  have hev : ∀ α ∈ Δ, ∀ᶠ j in Filter.atTop,
      CocharacterUniformizer.characterNorm k A α (t ^ j) < ε := by
    intro α hα
    simp only [characterNorm_pow]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (characterNorm_nonneg A α t)
      (ht α hα)).eventually (gt_mem_nhds hε)
  obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.1 ((Filter.eventually_all_finite hΔ).2 hev)
  exact ⟨j₀, hj₀⟩

/-- A positive power of a point of `A^{++}` is again in `A^{++}`. -/
theorem characterNorm_pow_lt_one {Δ : Set (characterLattice A)} {t : rationalPoints A.toGrp}
    (ht : ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < 1) {r : ℕ} (hr : r ≠ 0) :
    ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α (t ^ r) < 1 := by
  intro α hα
  rw [characterNorm_pow]
  exact pow_lt_one₀ (characterNorm_nonneg A α t) (ht α hα) hr

end IwahoriContractionPowers

open IwahoriContractionPowers

/-- **Contracting powers for an Iwahori decomposition** (derived from Renard 2026, V.5.2 and
VI.6.1). For a compact open `K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))` and a split component
`A` of `M` with a compatible root presentation, `A^{++}` is nonempty and all large powers of
every `t₀ ∈ A^{++}` satisfy `Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F)`. -/
theorem representedIwahoriContraction : RepresentedIwahoriContractionStatement.{u} := by
  intro k _ _ _ _ _ G hG _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar
    hnbar hmulbar hP hPP K hK hfac A a pres Δ incG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have : Smooth G.X.hom := hG.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have hΔ : Δ.Finite := pres.finite_simpleRoots.sdiff.image _
  refine ⟨⟨CocharacterUniformizer.latticeSection k A
      (Multiplicative.ofAdd pres.splitComponentCocharacter), ?_⟩, ?_⟩
  · rintro _ ⟨β, hβ, rfl⟩
    apply CocharacterUniformizer.characterNorm_latticeSection_lt_one
    rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt]
    exact pres.isStandard_splitComponentCocharacter.2.2 β hβ.1 hβ.2
  intro t₀ ht₀
  -- the two compact pieces `K ∩ N(F)` and `K ∩ N̄(F)`
  have hKN : IsCompact ((K : Set (rationalPoints G)) ∩ (pointImage (n ≫ p) : Set _)) :=
    hK.inter_right (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
  have hKNbar : IsCompact ((K : Set (rationalPoints G)) ∩ (pointImage (nbar ≫ pbar) : Set _)) :=
    hK.inter_right
      (isClosed_pointImage_comp pbar nbar hpbar.isClosedSubgroup hnbar.1.isClosedSubgroup)
  have hcontr := splitComponentOppositeContraction k G hG P Pbar M N Nbar p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP A a pres
  -- images of points of `A` lie in `M(F)`, are central there, and normalize `N(F)`, `N̄(F)`
  have hinc : ∀ s : rationalPoints A.toGrp,
      incG s = rationalPoints.map (m ≫ p) (rationalPoints.map a s) :=
    fun s => pointMap_comp_apply a (m ≫ p) s
  have hgM : ∀ s : rationalPoints A.toGrp, incG s ∈ pointImage (m ≫ p) :=
    fun s => ⟨rationalPoints.map a s, (hinc s).symm⟩
  have hcomm : ∀ s : rationalPoints A.toGrp, ∀ y ∈ pointImage (m ≫ p),
      incG s * y = y * incG s := by
    intro s y hy
    rw [hinc s]
    exact splitComponent_point_comm pres s y hy
  have hMN := pointImage_le_normalizer p m n hn
  have hMNbar : pointImage (m ≫ p) ≤
      Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G)) := by
    rw [← hP]
    exact pointImage_le_normalizer pbar mbar nbar hnbar
  -- one `ε` for `C = K ∩ N(F)`, `C̄ = K ∩ N̄(F)` and the neighbourhood `K`
  obtain ⟨ε, hε, hεK⟩ := hcontr _ hKN Set.inter_subset_right _ hKNbar Set.inter_subset_right
    _ K.mem_nhds_one
  obtain ⟨r₁, hr₁⟩ := exists_pow_characterNorm_lt A hΔ ht₀ hε
  refine ⟨max r₁ 1, fun r hr => ?_⟩
  have hr1 : r ≠ 0 := by
    have := le_of_max_le_right hr
    omega
  have htr := characterNorm_pow_lt_one A ht₀ hr1
  have hsmall := hεK (t₀ ^ r) (hr₁ r (le_of_max_le_left hr))
  refine
    { mem_levi := hgM _
      factor := hfac
      upper := ?_
      levi := ?_
      lower := ?_
      exhaust := ?_
      contract := ?_ }
  · rintro u ⟨huK, huN⟩
    exact ⟨hsmall.1 u ⟨huK, huN⟩, (Subgroup.mem_normalizer_iff.1 (hMN (hgM _)) u).1 huN⟩
  · rintro y ⟨hyK, hyM⟩
    have e : (incG (t₀ ^ r))⁻¹ * y * incG (t₀ ^ r) = y := by
      rw [mul_assoc, ← hcomm _ y hyM, inv_mul_cancel_left]
    rw [e]
    exact ⟨hyK, hyM⟩
  · rintro l ⟨hlK, hlN⟩
    refine ⟨hsmall.2 l ⟨hlK, hlN⟩, ?_⟩
    have h := (Subgroup.mem_normalizer_iff.1 (hMNbar (inv_mem (hgM (t₀ ^ r)))) l).1 hlN
    rwa [inv_inv] at h
  · intro x hx
    obtain ⟨ε', hε', h'⟩ := hcontr {x} isCompact_singleton (Set.singleton_subset_iff.2 hx)
      ∅ isCompact_empty (Set.empty_subset _) _ K.mem_nhds_one
    obtain ⟨s, hs⟩ := exists_pow_characterNorm_lt A hΔ htr hε'
    refine ⟨s, ?_⟩
    rw [← map_pow]
    exact (h' _ (hs s le_rfl)).1 x rfl
  · intro L
    obtain ⟨ε', hε', h'⟩ := hcontr ∅ isCompact_empty (Set.empty_subset _) _ hKNbar
      Set.inter_subset_right _ L.mem_nhds_one
    obtain ⟨s, hs⟩ := exists_pow_characterNorm_lt A hΔ htr hε'
    refine ⟨s, fun l hl => ?_⟩
    rw [← map_pow]
    exact (h' _ (hs s le_rfl)).2 l hl

end Langlands.Aubert.General.RepresentedParabolic
