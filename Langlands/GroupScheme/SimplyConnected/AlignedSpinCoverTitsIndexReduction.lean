import Langlands.GroupScheme.SimplyConnected.AlignedSpinCoverTitsIndexStatement
import Langlands.GroupScheme.SimplyConnected.SpinCoverVectorWeightsStatement
import Langlands.GroupScheme.Quaternionic.ConnectedIsometrySplitRankStatement
import Langlands.GroupScheme.Quaternionic.MaximalSplitTorusWeightsStatement
import Langlands.GroupScheme.Rational.CentralIsogenySplitRank
import Langlands.GroupScheme.CentralSurjection.TorusImage
import Langlands.GroupScheme.Reductive.CentralFiniteQuotientReductive
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.Combinatorics.MultiplicityJumps

/-!
# Index comparisons for an aligned spin cover from the weight statements

This file proves `AlignedSpinCoverTitsIndexStatement` from three prerequisite statements:
`ConnectedIsometrySplitRankStatement`, `IsometryMaximalSplitTorusWeightsStatement` and
`SpinCoverVectorWeightsStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace AlignedSpinCoverTitsIndex

/-- Precomposition with a homomorphism of commutative group schemes whose underlying
morphism of schemes is an epimorphism is injective. -/
theorem comp_injective_of_epi {S : Scheme.{u}} {T T' H : CommGroupScheme S} (f : T ⟶ T')
    [Epi (CommGroupScheme.hom f)] : Function.Injective fun χ : T' ⟶ H => f ≫ χ := by
  intro χ ψ h
  have h' : CommGroupScheme.hom χ = CommGroupScheme.hom ψ := by
    rw [← cancel_epi (CommGroupScheme.hom f)]
    simpa only [CommGroupScheme.hom_comp] using congrArg CommGroupScheme.hom h
  apply CommGroupScheme.hom_ext_points
  intro U x
  have : (CommGroupScheme.groupHom χ).hom.hom = (CommGroupScheme.groupHom ψ).hom.hom :=
    Over.OverMorphism.ext h'
  rw [this]

/-- In a `ℤ`-linearly independent family, `χ k + t • χ l ≠ 0` for `k ≠ l`. -/
theorem add_zsmul_ne_zero {M ι : Type*} [AddCommGroup M] {χ : ι → M}
    (hlin : LinearIndependent ℤ χ) {k l : ι} (hkl : k ≠ l) (t : ℤ) :
    χ k + t • χ l ≠ 0 := by
  classical
  intro h
  have h1 := linearIndependent_iff'.1 hlin {k, l} (fun i => if i = k then 1 else t) (by
    simpa [Finset.sum_pair hkl, hkl.symm] using h)
  have h2 := h1 k (by simp)
  simp at h2

end AlignedSpinCoverTitsIndex

open AlignedSpinCoverTitsIndex Combinatorics.MultiplicityJumps in
/-- **Reduction.** The index comparisons for an aligned spin cover follow from the split
rank and the maximal-split-torus weights of `O(q)⁰` and from the vector weights of the
spin cover. -/
theorem alignedSpinCoverTitsIndex_of_weights
    (h1 : Quaternionic.ConnectedIsometrySplitRankStatement.{u})
    (h2 : Quaternionic.IsometryMaximalSplitTorusWeightsStatement.{u})
    (h3 : SpinCoverVectorWeightsStatement.{u}) :
    AlignedSpinCoverTitsIndexStatement.{u} := by
  classical
  intro K _ G _ _ d n e hn hsc hsimple hcartan _hstar D _ _ _ _ degree m hdeg hD hm σ hσ q hq
    π hπ hv0
  have := hπ.smooth
  obtain ⟨p, hp, hpι⟩ := hπ.exists_centralIsogeny
  have hrank : splitRank G = σ.quadraticWittIndex q := by
    rw [hp.splitRank_eq]
    exact h1 K D degree hD σ hσ (Fin m) q hq
  refine ⟨hrank.symm, ?_⟩
  -- The image of the maximal split torus in `O(q)⁰`.
  have hG : IsConnectedReductive G := d.isSemisimple.isConnectedReductive
  have hG' : IsConnectedReductive (σ.connectedIsometryGroup q) :=
    isConnectedReductive_of_isCentralIsogeny p hG hp
  have : Surjective p.hom.hom.left := hp.surjective
  obtain ⟨S', i', fS, hmax', hsq, hflat, hsurj, -⟩ :=
    exists_maximalSplitTorus_image hG hG' p hp.isCentral_kernelι d.maximalSplit
  have := hflat
  have := hsurj
  have : Epi (CommGroupScheme.hom fS) := Flat.epi_of_flat_of_surjective _
  obtain ⟨χ, hlin, -, hw⟩ := h2 K D degree hD σ hσ (Fin m) q hq S' i' hmax'
  obtain ⟨ε, hroot, hrootfork, -, hcount⟩ :=
    h3 K G d n e hn hsc hsimple hcartan D degree m hdeg hD hm σ hσ q hq π hπ hv0
  -- The pulled-back characters `y k` and the restricted vector characters `x i`.
  let y : Fin (σ.quadraticWittIndex q) → characterLattice d.splitTorus := fun k => fS ≫ χ k
  let x : Fin n → characterLattice d.splitTorus := fun i =>
    (characterLattice.baseChangeEquiv (algebraBaseMap K (SeparableClosure K)) d.splitTorus
        d.maximalSplit.1.1).symm
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map d.torusMap ≫
        ε i)
  have hy_pair : ∀ (k : Fin (σ.quadraticWittIndex q)) (ν : cocharacterLattice d.splitTorus),
      latticePairing S' (χ k) (ν ≫ fS) = latticePairing d.splitTorus (y k) ν := by
    intro k ν
    rw [latticePairing_apply, latticePairing_apply, Category.assoc]
  have hy_ne : ∀ (k l : Fin (σ.quadraticWittIndex q)), k ≠ l → ∀ t : ℤ, y k + t • y l ≠ 0 := by
    intro k l hkl t h
    apply add_zsmul_ne_zero hlin hkl t
    apply comp_injective_of_epi fS
    simp only [Preadditive.comp_add, Preadditive.comp_zsmul, Limits.comp_zero]
    exact h
  have hy0 : ∀ k : Fin (σ.quadraticWittIndex q), y k ≠ 0 := by
    intro k h
    apply hlin.ne_zero k
    apply comp_injective_of_epi fS
    simp only [Limits.comp_zero]
    exact h
  -- The restricted simple roots.
  have hres : ∀ (a : d.Vertex) (i : Fin n) (hi : i.val + 1 < n), e a = i →
      d.rootRestriction a.val = x i - x ⟨i.val + 1, hi⟩ := by
    rintro a i hi rfl
    simp only [TitsIndexData.rootRestriction, absoluteRootRestriction, x]
    rw [hroot a hi, Preadditive.comp_sub, map_sub]
  have hres_fork : ∀ a : d.Vertex, (e a).val + 1 = n →
      d.rootRestriction a.val = x ⟨n - 2, by omega⟩ + x ⟨n - 1, by omega⟩ := by
    intro a ha
    simp only [TitsIndexData.rootRestriction, absoluteRootRestriction, x]
    rw [hrootfork a ha, Preadditive.comp_add, map_add]
  -- The perturbed positive cocharacter.
  let f : characterLattice d.splitTorus → (cocharacterLattice d.splitTorus →+ ℤ) := fun α =>
    (latticePairing d.splitTorus α).toAddMonoidHom
  let pairs : Finset (Fin (σ.quadraticWittIndex q) × Fin (σ.quadraticWittIndex q)) :=
    Finset.univ.filter fun pr => pr.1 ≠ pr.2
  let F : Finset (characterLattice d.splitTorus) :=
    Finset.univ.image y ∪ pairs.image (fun pr => y pr.1 + y pr.2) ∪
      pairs.image (fun pr => y pr.1 - y pr.2)
  have hF0 : ∀ α ∈ (F : Set (characterLattice d.splitTorus)), α ≠ 0 := by
    intro α hα
    simp only [F, pairs, Finset.coe_union, Finset.coe_image, Finset.coe_filter,
      Finset.coe_univ, Set.mem_union, Set.mem_image, Set.mem_univ, true_and,
      Set.mem_ofPred_eq, Finset.mem_univ] at hα
    rcases hα with (⟨k, rfl⟩ | ⟨⟨k, l⟩, hkl, rfl⟩) | ⟨⟨k, l⟩, hkl, rfl⟩
    · exact hy0 k
    · simpa using hy_ne k l hkl 1
    · simpa [sub_eq_add_neg] using hy_ne k l hkl (-1)
  obtain ⟨η, hη⟩ := d.maximalSplit.1.1.exists_regular_on_finite
    (F : Set (characterLattice d.splitTorus)) F.finite_toSet hF0
  let : Fintype d.Vertex := Fintype.ofFinite _
  let sset : Finset (characterLattice d.splitTorus) :=
    F ∪ Finset.univ.image fun a : d.Vertex => d.rootRestriction a.val
  set N := IntegralPerturbation.bound f sset η with hN
  set ν : cocharacterLattice d.splitTorus := N • d.positiveCocharacter + η with hν
  have hsigns : ∀ α ∈ sset,
      (0 < latticePairing d.splitTorus α ν ↔
          0 < latticePairing d.splitTorus α d.positiveCocharacter ∨
            latticePairing d.splitTorus α d.positiveCocharacter = 0 ∧
              0 < latticePairing d.splitTorus α η) ∧
        (latticePairing d.splitTorus α ν = 0 ↔
          latticePairing d.splitTorus α d.positiveCocharacter = 0 ∧
            latticePairing d.splitTorus α η = 0) := by
    intro α hα
    have h := IntegralPerturbation.signs f sset d.positiveCocharacter η (le_refl N) hα
    exact ⟨h.1, h.2.2⟩
  have hFν : ∀ α ∈ F, latticePairing d.splitTorus α ν ≠ 0 := by
    intro α hα h0
    exact hη α (by exact_mod_cast hα)
      ((hsigns α (Finset.mem_union_left _ hα)).2.1 h0).2
  have hb0 : ∀ k : Fin (σ.quadraticWittIndex q), latticePairing d.splitTorus (y k) ν ≠ 0 := by
    intro k
    exact hFν _ (by simp [F])
  have hb : ∀ k l : Fin (σ.quadraticWittIndex q), k ≠ l →
      latticePairing d.splitTorus (y k) ν ≠ latticePairing d.splitTorus (y l) ν ∧
        latticePairing d.splitTorus (y k) ν ≠ -latticePairing d.splitTorus (y l) ν := by
    intro k l hkl
    have hmem : (k, l) ∈ pairs := by simp [pairs, hkl]
    have hsub := hFν (y k - y l) (by
      simp only [F, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨(k, l), hmem, rfl⟩)
    have hadd := hFν (y k + y l) (by
      simp only [F, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨(k, l), hmem, rfl⟩))
    rw [LinearMap.map_sub₂] at hsub
    rw [LinearMap.map_add₂] at hadd
    constructor
    · intro h; apply hsub; rw [h, sub_self]
    · intro h; apply hadd; rw [h, neg_add_cancel]
  -- Positivity of restricted simple roots.
  have hpos : ∀ a : d.Vertex, d.rootRestriction a.val ≠ 0 →
      0 < latticePairing d.splitTorus (d.rootRestriction a.val) ν := by
    intro a ha
    have hlam : 0 < latticePairing d.splitTorus (d.rootRestriction a.val) d.positiveCocharacter :=
      (d.compatible a.val ha).1 (d.pinning.base.isPos_of_mem_support a.property)
    exact (hsigns _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))).1.2
      (Or.inl hlam)
  have hnonneg : ∀ a : d.Vertex, 0 ≤ latticePairing d.splitTorus (d.rootRestriction a.val) ν := by
    intro a
    by_cases ha : d.rootRestriction a.val = 0
    · rw [ha, LinearMap.map_zero₂]
    · exact (hpos a ha).le
  -- The numerical data.
  let c : Fin n → ℤ := fun i => latticePairing d.splitTorus (x i) ν
  let b : Fin (σ.quadraticWittIndex q) → ℤ := fun k => latticePairing d.splitTorus (y k) ν
  have hstep : ∀ (j : ℕ) (h : j + 1 < n), c ⟨j + 1, h⟩ ≤ c ⟨j, by omega⟩ := by
    intro j h
    have h0 := hnonneg (e.symm ⟨j, by omega⟩)
    rw [hres _ ⟨j, by omega⟩ h (e.apply_symm_apply _), LinearMap.map_sub₂] at h0
    simp only [c]
    linarith
  have hfork : 0 ≤ c ⟨n - 2, by omega⟩ + c ⟨n - 1, by omega⟩ := by
    have h0 := hnonneg (e.symm ⟨n - 1, by omega⟩)
    rw [hres_fork _ (by rw [e.apply_symm_apply]; simp only; omega), LinearMap.map_add₂] at h0
    exact h0
  have hcount' : ∀ v : ℤ, 0 < v →
      Nat.card {pr : Fin n × ℤˣ // (pr.2 : ℤ) * c pr.1 = v} =
        degree * Nat.card {pr : Fin (σ.quadraticWittIndex q) × ℤˣ // (pr.2 : ℤ) * b pr.1 = v} := by
    intro v hv
    have hmorph : CommGroupScheme.groupHom ν ≫ d.splitInclusion ≫ π =
        CommGroupScheme.groupHom (ν ≫ fS) ≫ i' ≫ identityComponentι (σ.isometryGroup q) := by
      rw [← hpι, ← Category.assoc d.splitInclusion, hsq,
        show CommGroupScheme.groupHom (ν ≫ fS) =
          CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom fS from rfl]
      simp only [Category.assoc]
    have h3c := hcount ν v
    rw [hmorph, hw (ν ≫ fS) v] at h3c
    simp only [hv.ne', ↓reduceIte, add_zero, hy_pair] at h3c
    exact h3c
  -- Conclusion.
  intro a ha
  have hdist : a ∈ d.distinguishedVertices ↔ c (e a) ≠ c ⟨(e a).val + 1, by omega⟩ := by
    have hres_a := hres a (e a) (by omega) rfl
    change ¬ (d.rootRestriction a.val = 0) ↔ _
    constructor
    · intro hne heq
      have := hpos a hne
      rw [hres_a, LinearMap.map_sub₂] at this
      simp only [c] at heq
      linarith
    · intro hne hzero
      apply hne
      have := congrArg (fun α => latticePairing d.splitTorus α ν) hzero
      simp only [hres_a, LinearMap.map_sub₂, LinearMap.map_zero₂] at this
      simp only [c]
      linarith
  rw [hdist]
  exact chain_ne_succ_iff degree (by omega) c b hstep hfork hb0 hb hcount' (e a).val ha

end Langlands.GroupScheme
