import Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof
import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport

/-!
# Spanning distributions on a finite union of orbits

If each orbit has an invariant distribution with support equal to its
closure, the chosen distributions span the invariant distributions
supported on the union, provided the union is closed.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open Set MulAction FiniteOrbitVanishingProof Hecke.TestFunction

universe uG uX

private theorem eq_zero_of_indicator_eq_zero {X : Type*} [TopologicalSpace X]
    (D : Distribution X) (hD : ∀ (U : Set X) (hU : IsClopen U) (hc : IsCompact U),
      D (characteristic hU hc) = 0) : D = 0 := by
  classical
  ext f
  let S : Set ℂ := {c | c ∈ Set.range f ∧ c ≠ 0}
  have hS : S.Finite :=
    (finite_range_of_locallyConstant_of_hasCompactSupport
      f.locallyConstant f.hasCompactSupport).subset (fun _ hc => hc.1)
  let : Fintype S := hS.fintype
  let φ (c : S) := characteristic (f.locallyConstant.isClopen_fiber c.val)
    (isCompact_fiber f c.property.2)
  have hsum : f = ∑ c : S, c.val • φ c := by
    ext x
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    by_cases hx : f x = 0
    · simp [φ, characteristic_apply, hx, fun c : S => c.property.2.symm]
    · let c : S := ⟨f x, ⟨⟨x, rfl⟩, hx⟩⟩
      rw [Finset.sum_eq_single c]
      · simp [φ, c, characteristic_apply]
      · intro b _ hb
        have hne : f x ≠ b.val := fun h => hb (Subtype.ext h.symm)
        simp [φ, characteristic_apply, hne]
      · simp
  have hφ (c : S) : D (φ c) = 0 := hD _ _ _
  rw [hsum, map_sum]
  simp [hφ]

section Actions

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G]
variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MulAction G X] [ContinuousSMul G X]

private theorem exists_eq_smul_of_invariant [IsPretransitive G X]
    (D R : Distribution X)
    (hD : ∀ g : G, pushforward (Homeomorph.smul g) D = D)
    (hR : ∀ g : G, pushforward (Homeomorph.smul g) R = R)
    (hRne : R ≠ 0) : ∃ c : ℂ, D = c • R := by
  classical
  obtain ⟨U, hU, hcU, hRU⟩ : ∃ (U : Set X) (hU : IsClopen U) (hcU : IsCompact U),
      R (characteristic hU hcU) ≠ 0 := by
    by_contra h
    apply hRne (eq_zero_of_indicator_eq_zero R fun U hU hcU => ?_)
    by_contra hne
    exact h ⟨U, hU, hcU, hne⟩
  have hzero (V : Set X) (hV : IsClopen V) (hcV : IsCompact V) (hne : ¬ V.Nonempty) :
      characteristic hV hcV = (0 : SchwartzBruhat X) := by
    ext x
    exact indicator_of_notMem (fun hx => hne ⟨x, hx⟩) _
  have hUne : U.Nonempty := by
    by_contra h
    exact hRU (by rw [hzero U hU hcU h, map_zero])
  let c := D (characteristic hU hcU) / R (characteristic hU hcU)
  let E := D - c • R
  have hE (g : G) : pushforward (Homeomorph.smul g) E = E := by
    simp only [E, map_sub, map_smul, hD, hR]
  have hEU : E (characteristic hU hcU) = 0 := by
    change D (characteristic hU hcU) - c * R (characteristic hU hcU) = 0
    rw [div_mul_cancel₀ _ hRU, sub_self]
  refine ⟨c, sub_eq_zero.mp (eq_zero_of_indicator_eq_zero E fun V hV hcV => ?_)⟩
  by_cases hVne : V.Nonempty
  · obtain ⟨q, _, hq⟩ :=
      homogeneousIndicatorProportionality G X E hE V U hV hcV hU hcU hVne hUne
    rw [hq, hEU, mul_zero]
  · rw [hzero V hV hcV hVne, map_zero]

variable [TotallyDisconnectedSpace X]

private theorem exists_smul_sub_supportedOn_sdiff
    {C : Set X} (hC : IsClosed C) (hinv : ∀ (g : G) (x : X), x ∈ C → g • x ∈ C)
    {y : X} (hy : y ∈ C) {V : Set X} (hV : IsOpen V) (horbit : V ∩ C = orbit G y)
    (D R : Distribution X) (hD : D ∈ supportedOn C) (hR : R ∈ supportedOn C)
    (hDinv : ∀ g : G, pushforward (Homeomorph.smul g) D = D)
    (hRinv : ∀ g : G, pushforward (Homeomorph.smul g) R = R)
    (hyR : y ∈ support R) : ∃ c : ℂ, D - c • R ∈ supportedOn (C \ orbit G y) := by
  let Y : SubMulAction G X := ⟨C, fun g _ hx => hinv g _ hx⟩
  let yY : Y := ⟨y, hy⟩
  let O : Set Y := orbit G yY
  have hOV : O = Subtype.val ⁻¹' V := by
    ext a
    change a ∈ orbit G yY ↔ a.val ∈ V
    rw [SubMulAction.mem_orbit_subMul_iff, ← horbit]
    exact ⟨And.left, fun h => ⟨h, a.property⟩⟩
  have hO : IsOpen O := hOV ▸ hV.preimage continuous_subtype_val
  let : LocallyCompactSpace Y := hC.locallyCompactSpace
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let : ContinuousSMul G O :=
    Topology.IsInducing.subtypeVal.continuousSMul continuous_id rfl
  let r : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat C := SchwartzBruhat.restrictClosed hC
  have hr (f : SchwartzBruhat X) (a : C) : r f a = f a.val :=
    SchwartzBruhat.restrictClosed_apply hC f a
  have hsurj : Function.Surjective r := SchwartzBruhat.closedRestrictionSurjective X C hC
  let e : SchwartzBruhat O →ₗ[ℂ] SchwartzBruhat Y := SchwartzBruhat.extendZero hO
  have he (f : SchwartzBruhat O) (a : O) : e f a.val = f a :=
    SchwartzBruhat.extendZero_apply_subtype hO f a
  have hoff (f : SchwartzBruhat O) (a : Y) (ha : a ∉ O) : e f a = 0 :=
    SchwartzBruhat.extendZero_apply_of_not_mem hO f ha
  have hrestrict (W : Distribution X) (hW : W ∈ supportedOn C)
      (hWinv : ∀ g : G, pushforward (Homeomorph.smul g) W = W) :
      ∃ E : Distribution Y, (∀ f, E (r f) = W f) ∧
        ∀ g : G, pushforward (Homeomorph.smul g : O ≃ₜ O) (E.comp e) = E.comp e := by
    obtain ⟨E, hE⟩ := exists_descent r hr hsurj W hW
    refine ⟨E, hE, fun g => ?_⟩
    have hYg (x : X) (hx : x ∈ C) :
        Homeomorph.smul g x ∈ C ∧ (Homeomorph.smul g).symm x ∈ C :=
      ⟨hinv g x hx, hinv g⁻¹ x hx⟩
    have hEY : pushforward (Homeomorph.smul g : Y ≃ₜ Y) E = E := by
      have heq : restrictHomeomorph (Homeomorph.smul g) C hYg =
          (Homeomorph.smul g : Y ≃ₜ Y) := by
        ext a
        rfl
      have h := descent_pushforward r hr hsurj W E hE (Homeomorph.smul g) hYg 1
        (by simpa only [one_smul] using hWinv g)
      simpa only [heq, one_smul] using h
    have hOg (a : Y) (ha : a ∈ O) :
        Homeomorph.smul g a ∈ O ∧ (Homeomorph.smul g).symm a ∈ O :=
      ⟨mem_orbit_of_mem_orbit g ha, mem_orbit_of_mem_orbit g⁻¹ ha⟩
    have heq : restrictHomeomorph (Homeomorph.smul g) O hOg =
        (Homeomorph.smul g : O ≃ₜ O) := by
      ext a
      rfl
    have h := extension_dual_pushforward e he hoff E (Homeomorph.smul g) hOg 1
      (by simpa only [one_smul] using hEY)
    simpa only [heq, one_smul] using h
  obtain ⟨ED, hED, hEDinv⟩ := hrestrict D hD hDinv
  obtain ⟨ER, hER, hERinv⟩ := hrestrict R hR hRinv
  have hERne : ER.comp e ≠ 0 := by
    intro heq
    apply ((not_mem_support_iff R y).2 ⟨V, hV, (horbit.symm ▸ mem_orbit_self y).1, ?_⟩) hyR
    ext f
    obtain ⟨φ, hφ⟩ := exists_extension_eq e he hoff (r (SchwartzBruhat.extendZero hV f))
      (fun a ha => by
        rw [hr]
        exact SchwartzBruhat.extendZero_apply_of_not_mem hV f (fun hv => ha (hOV ▸ hv)))
    rw [show restrictOpen hV R f = R (SchwartzBruhat.extendZero hV f) from rfl, ← hER, ← hφ]
    exact congrArg (fun W : Distribution O => W φ) heq
  obtain ⟨c, hc⟩ := exists_eq_smul_of_invariant (ED.comp e) (ER.comp e) hEDinv hERinv hERne
  refine ⟨c, fun f hf => ?_⟩
  obtain ⟨φ, hφ⟩ := exists_extension_eq e he hoff (r f) fun a ha => by
    rw [hr]
    exact hf a.val ⟨a.property, fun ha' => ha (SubMulAction.mem_orbit_subMul_iff.mpr ha')⟩
  change D f - c * R f = 0
  rw [← hED, ← hER, ← hφ]
  exact sub_eq_zero.mpr (congrArg (fun W : Distribution O => W φ) hc)

private theorem mem_span_of_closed_finite_orbits
    {Z : Set X} (hZ : IsClosed Z) (s : Finset X) (hs : Z = ⋃ x ∈ s, orbit G x)
    (L : X → Distribution X)
    (hL : ∀ x ∈ s,
      L x ∈ supportedOn (closure (orbit G x)) ∧ orbit G x ⊆ support (L x) ∧
        ∀ g : G, pushforward (Homeomorph.smul g) (L x) = L x)
    (D : Distribution X) (hD : D ∈ supportedOn Z)
    (hDinv : ∀ g : G, pushforward (Homeomorph.smul g) D = D) :
    D ∈ Submodule.span ℂ (L '' ↑s) := by
  suffices ∀ (n : ℕ) (C : Set X), C ⊆ Z → IsClosed C →
      (∀ (g : G) (x : X), x ∈ C → g • x ∈ C) →
      (Quotient.mk (orbitRel G X) '' C).ncard = n →
      ∀ (E : Distribution X), E ∈ supportedOn C →
        (∀ g : G, pushforward (Homeomorph.smul g) E = E) →
        E ∈ Submodule.span ℂ (L '' ↑s) from
    this _ Z Subset.rfl hZ (orbit_union_invariant s hs) rfl D hD hDinv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hCZ hC hCinv hn E hE hEinv
    rcases C.eq_empty_or_nonempty with rfl | hne
    · have hzero : E = 0 := by ext f; exact hE f (by simp)
      rw [hzero]
      exact Submodule.zero_mem _
    have hfin := (finite_orbit_image_of_finset s hs).subset (image_mono hCZ)
    obtain ⟨y, hy, V, hV, hVO⟩ := exists_relOpen_orbit_of_finite_image hC hCinv hfin hne
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hs ▸ hCZ hy)
    have hxy : orbit G y = orbit G x := orbit_eq_iff.mpr hyx
    obtain ⟨hLsupp, hLorb, hLinv⟩ := hL x hx
    have hLmem : L x ∈ supportedOn C :=
      supportedOn_mono (closure_minimal (hxy ▸ orbit_subset_of_invariant hCinv hy) hC) hLsupp
    obtain ⟨c, hc⟩ := exists_smul_sub_supportedOn_sdiff hC hCinv hy hV hVO E (L x)
      hE hLmem hEinv hLinv (hLorb hyx)
    obtain ⟨hclosed, hinv, hlt⟩ := remove_relOpen_orbit hC hCinv hfin hy hV hVO
    have hsub := ih _ (hn ▸ hlt) _ (sdiff_subset.trans hCZ) hclosed hinv rfl (E - c • L x)
      hc (fun g => by simp only [map_sub, map_smul, hEinv, hLinv])
    have hadd := (Submodule.span ℂ (L '' ↑s)).add_mem hsub
      ((Submodule.span ℂ (L '' ↑s)).smul_mem c (Submodule.subset_span ⟨x, hx, rfl⟩))
    exact sub_add_cancel E (c • L x) ▸ hadd

end Actions

/-- Invariant distributions on a closed finite union of orbits are spanned by
supplied invariant distributions whose supports are the respective orbit closures. -/
def FiniteOrbitDistributionSpanningStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G]
    (X : Type uX) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
    (Z : Set X) (s : Finset X) (L : X → Distribution X),
    IsClosed Z → Z = ⋃ x ∈ s, orbit G x →
    (∀ x ∈ s, L x ∈ supportedOn (closure (orbit G x)) ∧ orbit G x ⊆ support (L x) ∧
      ∀ g : G, pushforward (Homeomorph.smul g) (L x) = L x) →
    ∀ D ∈ supportedOn Z, (∀ g : G, pushforward (Homeomorph.smul g) D = D) →
      D ∈ Submodule.span ℂ (L '' ↑s)

/-- Restriction to a relatively open orbit and induction on the number of orbits. -/
theorem finiteOrbitDistributionSpanning : FiniteOrbitDistributionSpanningStatement.{uG, uX} := by
  intro G _ _ _ _ _ X _ _ _ _ _ _ Z s L hZ hs hL D hD hDinv
  exact mem_span_of_closed_finite_orbits hZ s hs L hL D hD hDinv

end Langlands.HarmonicAnalysis.Distribution
