import Langlands.Representation.CompactCoefficient.FiniteQuotientAveraging
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.CompactCoefficient.AmbientProjector
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Cohomology.SupercuspidalRestriction.CompactModCenterProof
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Lifts and retractions on an open normal subgroup

Let `H` be an open normal subgroup of a locally profinite group `G` such that
`H ⊔ center G` has finite index, and let `τ` be an irreducible smooth complex
representation of `G` on which the centre acts by scalars and whose restriction
to `H` has compactly supported smooth-dual coefficients. By Clifford's theorem
the restriction of `τ` to `H` is a finite internal direct sum of irreducible
representations, each of which is admissible with compact coefficients. Hence:

* every intertwiner from `τ` to a smooth representation `ξ` lifts, as an
  `H`-equivariant linear map, along every surjective intertwiner onto `ξ`;
* every injective intertwiner from `τ` to a smooth representation has an
  `H`-equivariant linear retraction.

The two statements are the `H`-level inputs of Renard VI.3.6.
-/

noncomputable section

namespace Langlands.RestrictedSplitting

open MeasureTheory Representation FiniteQuotientAveraging

universe uG uV uW uU

section Decomposition

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Clifford with the centre acting by scalars: the restriction to `H` is the internal
direct sum of finitely many irreducible subrepresentations. -/
theorem exists_independent_irreducible (ρ : Representation ℂ G V) (H : Subgroup G) [H.Normal]
    [(H ⊔ Subgroup.center G).FiniteIndex] (hirr : ρ.IsIrreducible)
    (hscalar : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v : V, ρ z v = c • v) :
    ∃ (m : ℕ) (W : Fin m → _root_.Subrepresentation (ρ.comp H.subtype)),
      (∀ i, (W i).toRepresentation.IsIrreducible) ∧
        iSupIndep (fun i => (W i).toSubmodule) ∧ (⨆ i, (W i).toSubmodule) = ⊤ := by
  classical
  obtain ⟨n, W₀, hW₀, hsup⟩ :=
    FiniteIndexRestriction.exists_finite_atoms ρ (H ⊔ Subgroup.center G) hirr
  let e := FiniteIndexRestriction.supCenterOrderIso ρ H hscalar
  let W₁ : Fin n → _root_.Subrepresentation (ρ.comp H.subtype) := fun i => e (W₀ i)
  have hW₁ : ∀ i, IsAtom (W₁ i) := fun i => (e.isAtom_iff _).mpr (hW₀ i)
  let A : Fin n → Submodule ℂ V := fun i => (W₁ i).toSubmodule
  have hsupA : ∀ s : Finset (Fin n), s.sup A = (⨆ i ∈ s, W₁ i).toSubmodule := by
    intro s
    rw [Finset.sup_eq_iSup, Langlands.Subrepresentation.toSubmodule_iSup]
    simp_rw [Langlands.Subrepresentation.toSubmodule_iSup]
    rfl
  have hA : ∀ i (s : Finset (Fin n)), Disjoint (A i) (s.sup A) ∨ A i ≤ s.sup A := by
    intro i s
    rcases (hW₁ i).le_iff.mp (inf_le_left : W₁ i ⊓ (⨆ j ∈ s, W₁ j) ≤ W₁ i) with h | h
    · left
      rw [hsupA, disjoint_iff, ← _root_.Subrepresentation.toSubmodule_inf, h]
      rfl
    · right
      rw [hsupA]
      exact fun x hx => (inf_eq_left.mp h) hx
  obtain ⟨s, -, hs, hssup⟩ :=
    Cohomology.SupercuspidalRestriction.CompactModCenterProof.exists_supIndep_subset
      A hA Finset.univ
  refine ⟨s.card, fun j => W₁ (s.equivFin.symm j), fun j => ?_, ?_, ?_⟩
  · exact FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom _ (hW₁ _)
  · exact hs.independent.comp s.equivFin.symm.injective
  · have h1 : (⨆ j, A (s.equivFin.symm j)) = s.sup A := by
      rw [Finset.sup_eq_iSup]
      apply le_antisymm
      · exact iSup_le fun j =>
          le_iSup₂_of_le (f := fun i (_ : i ∈ s) => A i) (s.equivFin.symm j).val
            (s.equivFin.symm j).property le_rfl
      · exact iSup₂_le fun i hi => le_iSup_of_le (s.equivFin ⟨i, hi⟩) (by simp)
    have h2 : Finset.univ.sup A = ⊤ := by
      rw [Finset.sup_univ_eq_iSup]
      exact hsup
    exact h1.trans (hssup.trans h2)

end Decomposition

section Projection

variable {H : Type uG} [Group H] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ H V} {m : ℕ} (W : Fin m → _root_.Subrepresentation ρ)
  (hind : iSupIndep fun i => (W i).toSubmodule) (htop : (⨆ i, (W i).toSubmodule) = ⊤)

include hind htop in
theorem isCompl_iSup_ne (k : Fin m) :
    IsCompl (W k).toSubmodule (⨆ j ≠ k, (W j).toSubmodule) := by
  refine ⟨hind k, codisjoint_iff.mpr (top_unique ?_)⟩
  rw [← htop]
  refine iSup_le fun j => ?_
  by_cases h : j = k
  · subst h
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun j (_ : j ≠ k) => (W j).toSubmodule)
      j h le_rfl)

/-- The projection onto the `k`-th summand along the others. -/
def proj (k : Fin m) : V →ₗ[ℂ] (W k).toSubmodule :=
  Submodule.projectionOnto _ _ (isCompl_iSup_ne W hind htop k)

theorem proj_of_mem (k : Fin m) {x : V} (hx : x ∈ (W k).toSubmodule) :
    proj W hind htop k x = ⟨x, hx⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hx

theorem proj_of_mem_ne {j k : Fin m} (hjk : j ≠ k) {x : V} (hx : x ∈ (W j).toSubmodule) :
    proj W hind htop k x = 0 :=
  Submodule.projectionOnto_apply_of_mem_right _
    (le_iSup₂_of_le (f := fun j (_ : j ≠ k) => (W j).toSubmodule) j hjk le_rfl hx)

theorem sum_proj (x : V) : ∑ k, (proj W hind htop k x : V) = x := by
  have hx : x ∈ ⨆ i, (W i).toSubmodule := htop ▸ Submodule.mem_top
  refine Submodule.iSup_induction (fun i => (W i).toSubmodule)
    (motive := fun x => ∑ k, (proj W hind htop k x : V) = x) hx ?_ ?_ ?_
  · intro j y hy
    rw [Finset.sum_eq_single j]
    · rw [proj_of_mem W hind htop j hy]
    · intro k _ hkj
      rw [proj_of_mem_ne W hind htop (Ne.symm hkj) hy]
      rfl
    · simp
  · simp
  · intro y z hy hz
    simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, hy, hz]

theorem proj_apply (k : Fin m) (h : H) (x : V) :
    proj W hind htop k (ρ h x) = (W k).toRepresentation h (proj W hind htop k x) := by
  have hx : x ∈ ⨆ i, (W i).toSubmodule := htop ▸ Submodule.mem_top
  refine Submodule.iSup_induction (fun i => (W i).toSubmodule)
    (motive := fun x => proj W hind htop k (ρ h x) =
      (W k).toRepresentation h (proj W hind htop k x)) hx ?_ ?_ ?_
  · intro j y hy
    have hy' : ρ h y ∈ (W j).toSubmodule := (W j).apply_mem_toSubmodule h hy
    by_cases hjk : j = k
    · subst hjk
      rw [proj_of_mem W hind htop j hy', proj_of_mem W hind htop j hy]
      rfl
    · rw [proj_of_mem_ne W hind htop hjk hy', proj_of_mem_ne W hind htop hjk hy, map_zero]
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz]

end Projection

section Splitting

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [T2Space G] [LocallyCompactSpace G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {U : Type uU} [AddCommGroup U] [Module ℂ U]

/-- Compact open subgroups are cofinal among the open subgroups of an open subgroup. -/
theorem compact_cofinal (H : OpenSubgroup G) (K : OpenSubgroup H.toSubgroup) :
    ∃ L : OpenSubgroup H.toSubgroup, IsCompact (L : Set H.toSubgroup) ∧ L ≤ K := by
  let N := H.toSubgroup
  let : LocallyCompactSpace N := H.isOpen.locallyCompactSpace
  obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance N ∅ K
  exact ⟨L, hL, hLK⟩

/-- Lifting on `H`: an intertwiner from `τ` to `ξ` lifts along a surjective
intertwiner `σ → ξ` to an `H`-equivariant linear map `τ → σ`. -/
theorem exists_restricted_lift (H : OpenSubgroup G) [H.toSubgroup.Normal]
    [(H.toSubgroup ⊔ Subgroup.center G).FiniteIndex]
    (τ : SmoothRep.{0, uG, uV} ℂ G) (hirr : τ.IsIrreducible)
    (hscalar : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v : τ, τ.representation z v = c • v)
    (hc : HasCompactSmoothDualCoefficients
      (SmoothRep.restrictSubgroup H.toSubgroup τ).representation)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) {ξ : Representation ℂ G U}
    (hξ : IsSmooth ξ) (p : σ.IntertwiningMap ξ) (hp : Function.Surjective p)
    (φ : τ.representation.IntertwiningMap ξ) :
    ∃ l : τ →ₗ[ℂ] W, IsEquivariantOn τ.representation σ H.toSubgroup l ∧
      ∀ v, p (l v) = φ v := by
  classical
  let N := H.toSubgroup
  obtain ⟨m, Wf, hW, hind, htop⟩ :=
    exists_independent_irreducible τ.representation N hirr hscalar
  let : LocallyCompactSpace N := H.isOpen.locallyCompactSpace
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let μ : Measure N := Measure.haar
  have hcof := compact_cofinal H
  have hτN : IsSmooth (τ.representation.comp N.subtype) :=
    (SmoothRep.restrictSubgroup N τ).isSmooth
  have hσN : IsSmooth (σ.comp N.subtype) := isSmooth_comp N.subtype continuous_subtype_val hσ
  have hξN : IsSmooth (ξ.comp N.subtype) := isSmooth_comp N.subtype continuous_subtype_val hξ
  let pN : Representation.IntertwiningMap (σ.comp N.subtype) (ξ.comp N.subtype) :=
    { toLinearMap := p.toLinearMap
      isIntertwining' := fun n => p.isIntertwining' n.val }
  have hk : ∀ k, ∃ t : (Wf k).toRepresentation.IntertwiningMap (σ.comp N.subtype),
      ∀ w : (Wf k).toSubmodule, p (t w) = φ w := by
    intro k
    have hWs : IsSmooth (Wf k).toRepresentation :=
      CompactSplitting.isSmooth_subrepresentation hτN (Wf k)
    have hWc : HasCompactSmoothDualCoefficients (Wf k).toRepresentation :=
      hasCompactSmoothDualCoefficients_subrepresentation hcof
        (SmoothRep.restrictSubgroup N τ) hc (Wf k)
    have hWa := CompactSplitting.isAdmissible_of_compactCoefficients μ hcof _ hWs (hW k) hWc
    let φk : (Wf k).toRepresentation.IntertwiningMap (ξ.comp N.subtype) :=
      { toLinearMap := φ.toLinearMap ∘ₗ (Wf k).toSubmodule.subtype
        isIntertwining' := fun n => by
          ext w
          change φ (τ.representation n.val w) = ξ n.val (φ w)
          exact φ.isIntertwining _ _ n.val w }
    obtain ⟨t, ht⟩ :=
      CompactSplitting.exists_lift μ hcof _ hWa (hW k) hWc hσN hξN pN hp φk
    exact ⟨t, fun w => congrArg (fun f => f w) ht⟩
  choose t ht using hk
  refine ⟨∑ k, (t k).toLinearMap ∘ₗ proj Wf hind htop k, ?_, ?_⟩
  · intro n hn v
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := proj_apply Wf hind htop k ⟨n, hn⟩ v
    change (t k) (proj Wf hind htop k ((τ.representation.comp N.subtype) ⟨n, hn⟩ v)) = _
    rw [h1]
    exact (t k).isIntertwining _ _ ⟨n, hn⟩ _
  · intro v
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
      Representation.IntertwiningMap.toLinearMap_apply, ht]
    rw [← map_sum, sum_proj]

/-- Retraction on `H`: an injective intertwiner from `τ` to a smooth
representation has an `H`-equivariant linear retraction. -/
theorem exists_restricted_retraction (H : OpenSubgroup G) [H.toSubgroup.Normal]
    [(H.toSubgroup ⊔ Subgroup.center G).FiniteIndex]
    (τ : SmoothRep.{0, uG, uV} ℂ G) (hirr : τ.IsIrreducible)
    (hscalar : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v : τ, τ.representation z v = c • v)
    (hc : HasCompactSmoothDualCoefficients
      (SmoothRep.restrictSubgroup H.toSubgroup τ).representation)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (j : τ.representation.IntertwiningMap σ) (hj : Function.Injective j) :
    ∃ r : W →ₗ[ℂ] τ, IsEquivariantOn σ τ.representation H.toSubgroup r ∧
      ∀ v, r (j v) = v := by
  classical
  let N := H.toSubgroup
  obtain ⟨_, m, Wf, hW, htop⟩ :=
    FiniteIndexRestriction.finite_irreducible_restriction τ.representation N hirr hscalar
  let : LocallyCompactSpace N := H.isOpen.locallyCompactSpace
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let μ : Measure N := Measure.haar
  have hcof := compact_cofinal H
  have hτN : IsSmooth (τ.representation.comp N.subtype) :=
    (SmoothRep.restrictSubgroup N τ).isSmooth
  have hσN : IsSmooth (σ.comp N.subtype) := isSmooth_comp N.subtype continuous_subtype_val hσ
  have key : ∀ s : Finset (Fin m), ∃ r : W →ₗ[ℂ] τ,
      IsEquivariantOn σ τ.representation N r ∧
        ∀ i ∈ s, ∀ w ∈ (Wf i).toSubmodule, r (j w) = w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, fun n _ v => by simp, fun i hi => by simp at hi⟩
    | insert a s ha ih =>
      obtain ⟨r, hr, hrs⟩ := ih
      let q : W →ₗ[ℂ] W := LinearMap.id - j.toLinearMap ∘ₗ r
      have hq : ∀ n ∈ N, ∀ x, q (σ n x) = σ n (q x) := by
        intro n hn x
        change σ n x - j (r (σ n x)) = σ n (x - j (r x))
        rw [hr n hn, j.isIntertwining, map_sub]
      have hq0 : ∀ i ∈ s, ∀ w ∈ (Wf i).toSubmodule, q (j w) = 0 := by
        intro i hi w hw
        change j w - j (r (j w)) = 0
        rw [hrs i hi w hw, sub_self]
      let φ : (Wf a).toRepresentation.IntertwiningMap (σ.comp N.subtype) :=
        { toLinearMap := q ∘ₗ j.toLinearMap ∘ₗ (Wf a).toSubmodule.subtype
          isIntertwining' := fun n => by
            ext w
            change q (j (τ.representation n.val w)) = σ n.val (q (j w))
            rw [j.isIntertwining, hq n.val n.property] }
      have hφw : ∀ w : (Wf a).toSubmodule, φ w = q (j w) := fun _ => rfl
      have := hW a
      rcases IsIrreducible.injective_or_eq_zero φ with hφ | hφ
      · have hWs : IsSmooth (Wf a).toRepresentation :=
          CompactSplitting.isSmooth_subrepresentation hτN (Wf a)
        have hWc : HasCompactSmoothDualCoefficients (Wf a).toRepresentation :=
          hasCompactSmoothDualCoefficients_subrepresentation hcof
            (SmoothRep.restrictSubgroup N τ) hc (Wf a)
        have hWa :=
          CompactSplitting.isAdmissible_of_compactCoefficients μ hcof _ hWs (hW a) hWc
        obtain ⟨s', hs'⟩ := CompactSplitting.exists_retraction hcof μ _ hWa (hW a) hWc hσN φ hφ
        have hs'w : ∀ w : (Wf a).toSubmodule, s' (q (j w)) = w := fun w =>
          congrArg (fun f => f w) hs'
        let r' : W →ₗ[ℂ] τ := r + (LinearMap.id - r ∘ₗ j.toLinearMap) ∘ₗ
          (Wf a).toSubmodule.subtype ∘ₗ s'.toLinearMap ∘ₗ q
        have hr'x : ∀ x, r' x = r x + ((s' (q x) : τ) - r (j (s' (q x)))) := fun _ => rfl
        refine ⟨r', ?_, ?_⟩
        · intro n hn x
          have h1 : ((s' (q (σ n x)) : (Wf a).toSubmodule) : τ) =
              τ.representation n (s' (q x)) := by
            rw [hq n hn x]
            exact congrArg Subtype.val (s'.isIntertwining _ _ ⟨n, hn⟩ (q x))
          rw [hr'x, hr'x, h1, j.isIntertwining, hr n hn, hr n hn, map_add, map_sub]
        · intro i hi w hw
          rcases Finset.mem_insert.mp hi with rfl | hi
          · rw [hr'x, hs'w ⟨w, hw⟩]
            abel
          · rw [hr'x, hq0 i hi w hw, map_zero, Submodule.coe_zero, map_zero, map_zero,
              sub_zero, add_zero, hrs i hi w hw]
      · refine ⟨r, hr, fun i hi w hw => ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · have h0 : q (j w) = 0 := by
            rw [← hφw ⟨w, hw⟩, hφ]
            rfl
          have h2 : j w - j (r (j w)) = 0 := h0
          exact (hj (sub_eq_zero.mp h2)).symm
        · exact hrs i hi w hw
  obtain ⟨r, hr, hrall⟩ := key Finset.univ
  refine ⟨r, hr, fun v => ?_⟩
  have hle : (⨆ i, (Wf i).toSubmodule) ≤
      LinearMap.ker (r ∘ₗ j.toLinearMap - LinearMap.id) := by
    refine iSup_le fun i w hw => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      Representation.IntertwiningMap.toLinearMap_apply, hrall i (Finset.mem_univ i) w hw,
      sub_self]
  rw [htop] at hle
  have hv := hle (Submodule.mem_top (x := v))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Representation.IntertwiningMap.toLinearMap_apply, sub_eq_zero] at hv
  exact hv

end Splitting

end Langlands.RestrictedSplitting
