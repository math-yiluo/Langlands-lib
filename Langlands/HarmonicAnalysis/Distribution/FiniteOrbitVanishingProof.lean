import Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingStatement
import Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingProof
import Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof
import Langlands.Topology.GroupAction.FiniteOrbitProof
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Finite-orbit reduction for anti-invariant distributions -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open Set MulAction

universe uG uX

namespace FiniteOrbitVanishingProof

variable {G : Type uG} [Group G] {X : Type uX} [MulAction G X]

/-- The map on orbit spaces induced by an invariant inclusion. -/
def orbitQuotientInclusion (A : SubMulAction G X) :
    orbitRel.Quotient G A → orbitRel.Quotient G X :=
  Quotient.map' Subtype.val fun _ _ h => SubMulAction.mem_orbit_subMul_iff.mp h

theorem orbitQuotientInclusion_injective (A : SubMulAction G X) :
    Function.Injective (orbitQuotientInclusion A) := by
  intro a b
  induction a using Quotient.inductionOn with | _ a =>
  induction b using Quotient.inductionOn with | _ b =>
  intro h
  exact Quotient.sound (SubMulAction.mem_orbit_subMul_iff.mpr (Quotient.exact h))

theorem range_orbitQuotientInclusion (A : SubMulAction G X) :
    Set.range (orbitQuotientInclusion A) =
      Quotient.mk (orbitRel G X) '' (A : Set X) := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn with | _ a =>
    exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Quotient.mk (orbitRel G A) ⟨x, hx⟩, rfl⟩

theorem finite_orbitQuotient (A : SubMulAction G X)
    (hA : (Quotient.mk (orbitRel G X) '' (A : Set X)).Finite) :
    Finite (orbitRel.Quotient G A) := by
  have hrange : (Set.range (orbitQuotientInclusion A)).Finite := by
    rwa [range_orbitQuotientInclusion]
  let := hrange.fintype
  exact Finite.of_injective
    (fun q => (⟨orbitQuotientInclusion A q, Set.mem_range_self q⟩ :
      Set.range (orbitQuotientInclusion A)))
    (fun _ _ h => orbitQuotientInclusion_injective A (congrArg Subtype.val h))

theorem finite_orbit_image_of_finset (s : Finset X) {Z : Set X}
    (hZ : Z = ⋃ x ∈ s, orbit G x) :
    (Quotient.mk (orbitRel G X) '' Z).Finite := by
  apply (s.finite_toSet.image (Quotient.mk (orbitRel G X))).subset
  rintro _ ⟨z, hz, rfl⟩
  rw [hZ] at hz
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hz
  exact ⟨x, hx, (Quotient.sound hzx).symm⟩

theorem orbit_union_invariant (s : Finset X) {Z : Set X}
    (hZ : Z = ⋃ x ∈ s, orbit G x) :
    ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z := by
  intro g x hx
  rw [hZ] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨y, hy, mem_orbit_of_mem_orbit g hxy⟩

theorem orbit_subset_of_invariant {Z : Set X}
    (hinv : ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z) {y : X} (hy : y ∈ Z) :
    orbit G y ⊆ Z := by
  rintro _ ⟨g, rfl⟩
  exact hinv g y hy

theorem orbit_compl_invariant (y : X) :
    ∀ (g : G) (x : X), x ∉ orbit G y → g • x ∉ orbit G y := by
  intro g x hx h
  apply hx
  simpa using mem_orbit_of_mem_orbit g⁻¹ h

section Topology

variable [TopologicalSpace G] [SigmaCompactSpace G]
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [ContinuousSMul G X]

/-- The relative open-orbit theorem only needs finitely many orbits in the closed
invariant set, even when the ambient action has infinitely many orbits. -/
theorem exists_relOpen_orbit_of_finite_image {Z : Set X} (hZ : IsClosed Z)
    (hinv : ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z)
    (hfin : (Quotient.mk (orbitRel G X) '' Z).Finite) (hne : Z.Nonempty) :
    ∃ y ∈ Z, ∃ V : Set X, IsOpen V ∧ V ∩ Z = orbit G y := by
  let A : SubMulAction G X := ⟨Z, fun g _ hx => hinv g _ hx⟩
  have : LocallyCompactSpace A := hZ.locallyCompactSpace
  have : Finite (orbitRel.Quotient G A) := finite_orbitQuotient A hfin
  have hneA : (Set.univ : Set A).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hx⟩, mem_univ _⟩
  obtain ⟨y, -, V, hV, hVO⟩ :=
    Langlands.Topology.FiniteOrbitProof.exists_relOpen_orbit
      (H := G) (X := A) isClosed_univ (fun _ _ _ => mem_univ _) hneA
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
  refine ⟨y.val, y.property, W, hW, ?_⟩
  have horb : orbit G y = V := by simpa using hVO.symm
  ext x
  constructor
  · rintro ⟨hxW, hxZ⟩
    have hxV : (⟨x, hxZ⟩ : A) ∈ V := by
      rw [← hWV]
      exact hxW
    exact SubMulAction.mem_orbit_subMul_iff.mp (horb ▸ hxV)
  · intro hx
    have hxZ : x ∈ Z := by
      obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hx
      exact hinv g y.val y.property
    refine ⟨?_, hxZ⟩
    have hxO : (⟨x, hxZ⟩ : A) ∈ orbit G y :=
      SubMulAction.mem_orbit_subMul_iff.mpr hx
    have hxV : (⟨x, hxZ⟩ : A) ∈ V := horb ▸ hxO
    rw [← hWV] at hxV
    exact hxV

omit [TopologicalSpace G] [SigmaCompactSpace G] [T2Space X]
  [LocallyCompactSpace X] [ContinuousSMul G X] in
/-- The complement of a relatively open orbit is a smaller closed invariant
union of orbits, measured in the ambient orbit quotient. -/
theorem remove_relOpen_orbit {Z : Set X} (hZ : IsClosed Z)
    (hinv : ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z)
    (hfin : (Quotient.mk (orbitRel G X) '' Z).Finite)
    {y : X} (hy : y ∈ Z) {V : Set X} (hV : IsOpen V)
    (hVO : V ∩ Z = orbit G y) :
    IsClosed (Z \ orbit G y) ∧
      (∀ (g : G) (x : X), x ∈ Z \ orbit G y → g • x ∈ Z \ orbit G y) ∧
      (Quotient.mk (orbitRel G X) '' (Z \ orbit G y)).ncard <
        (Quotient.mk (orbitRel G X) '' Z).ncard := by
  have hset : Z \ orbit G y = Z ∩ Vᶜ := by
    ext x
    simp only [mem_sdiff, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨hxZ, hxO⟩
      exact ⟨hxZ, fun hxV => hxO (hVO ▸ ⟨hxV, hxZ⟩)⟩
    · rintro ⟨hxZ, hxV⟩
      exact ⟨hxZ, fun hxO => hxV ((hVO.symm ▸ hxO).1)⟩
  refine ⟨hset ▸ hZ.inter hV.isClosed_compl, ?_, ?_⟩
  · rintro g x ⟨hxZ, hxO⟩
    exact ⟨hinv g x hxZ, orbit_compl_invariant y g x hxO⟩
  · apply Set.ncard_lt_ncard
    · refine ⟨image_mono sdiff_subset, fun hsub => ?_⟩
      obtain ⟨z, ⟨-, hzO⟩, hz⟩ := hsub (mem_image_of_mem _ hy)
      exact hzO (Quotient.exact hz)
    · exact hfin

end Topology

section Homeomorphisms

variable [TopologicalSpace X]

/-- Restrict a homeomorphism that preserves a subset in both directions. -/
def restrictHomeomorph (σ : X ≃ₜ X) (Z : Set X)
    (hσ : ∀ z ∈ Z, σ z ∈ Z ∧ σ.symm z ∈ Z) : Z ≃ₜ Z :=
  σ.subtype fun z => ⟨fun hz => (hσ z hz).1, fun hz => by
    simpa using (hσ (σ z) hz).2⟩

@[simp]
theorem restrictHomeomorph_apply (σ : X ≃ₜ X) (Z : Set X)
    (hσ : ∀ z ∈ Z, σ z ∈ Z ∧ σ.symm z ∈ Z) (z : Z) :
    (restrictHomeomorph σ Z hσ z).val = σ z.val := rfl

@[simp]
theorem restrictHomeomorph_symm_apply (σ : X ≃ₜ X) (Z : Set X)
    (hσ : ∀ z ∈ Z, σ z ∈ Z ∧ σ.symm z ∈ Z) (z : Z) :
    ((restrictHomeomorph σ Z hσ).symm z).val = σ.symm z.val := rfl

theorem orbit_preserving_on_subset {σ : X ≃ₜ X} {Z : Set X}
    (hinv : ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z)
    (hσ : ∀ z ∈ Z, σ z ∈ orbit G z ∧ σ.symm z ∈ orbit G z) :
    ∀ z ∈ Z, σ z ∈ Z ∧ σ.symm z ∈ Z := by
  intro z hz
  exact ⟨orbit_subset_of_invariant hinv hz (hσ z hz).1,
    orbit_subset_of_invariant hinv hz (hσ z hz).2⟩

theorem orbit_preserving_on_orbit {σ : X ≃ₜ X} {Z : Set X}
    (hinv : ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z)
    (hσ : ∀ z ∈ Z, σ z ∈ orbit G z ∧ σ.symm z ∈ orbit G z)
    {y : X} (hy : y ∈ Z) :
    ∀ z ∈ orbit G y, σ z ∈ orbit G y ∧ σ.symm z ∈ orbit G y := by
  intro z hz
  have hzZ := orbit_subset_of_invariant hinv hy hz
  have horb : orbit G z = orbit G y := orbit_eq_iff.mpr hz
  simpa only [horb] using hσ z hzZ

end Homeomorphisms

section Induction

variable [TopologicalSpace G] [SigmaCompactSpace G]
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [ContinuousSMul G X]

/-- Strong induction on the finite set of orbits meeting the support. The
distribution-theoretic input is precisely removal of a relatively open orbit. -/
theorem vanishing_of_orbit_removal (σ : X ≃ₜ X) (D : Distribution X)
    (hremove : ∀ (Z : Set X), IsClosed Z →
      (∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z) →
      (Quotient.mk (orbitRel G X) '' Z).Finite →
      (∀ z ∈ Z, σ z ∈ orbit G z ∧ σ.symm z ∈ orbit G z) →
      (∀ f : SchwartzBruhat X, (∀ z ∈ Z, f z = 0) → D f = 0) →
      ∀ y ∈ Z, (∃ V : Set X, IsOpen V ∧ V ∩ Z = orbit G y) →
        ∀ f : SchwartzBruhat X, (∀ z ∈ Z \ orbit G y, f z = 0) → D f = 0)
    {Z : Set X} (hZ : IsClosed Z)
    (hinv : ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z)
    (hfin : (Quotient.mk (orbitRel G X) '' Z).Finite)
    (hσ : ∀ z ∈ Z, σ z ∈ orbit G z ∧ σ.symm z ∈ orbit G z)
    (hD : ∀ f : SchwartzBruhat X, (∀ z ∈ Z, f z = 0) → D f = 0) :
    D = 0 := by
  suffices ∀ (n : ℕ) (C : Set X), IsClosed C →
      (∀ (g : G) (x : X), x ∈ C → g • x ∈ C) →
      (Quotient.mk (orbitRel G X) '' C).Finite →
      (Quotient.mk (orbitRel G X) '' C).ncard = n →
      (∀ z ∈ C, σ z ∈ orbit G z ∧ σ.symm z ∈ orbit G z) →
      (∀ f : SchwartzBruhat X, (∀ z ∈ C, f z = 0) → D f = 0) →
      D = 0 from this _ Z hZ hinv hfin rfl hσ hD
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hC hCinv hCfin hn hCσ hDC
    rcases C.eq_empty_or_nonempty with rfl | hne
    · ext f
      exact hDC f (fun _ h => h.elim)
    obtain ⟨y, hy, V, hV, hVO⟩ :=
      exists_relOpen_orbit_of_finite_image hC hCinv hCfin hne
    obtain ⟨hclosed, hinv', hlt⟩ := remove_relOpen_orbit hC hCinv hCfin hy hV hVO
    have hD' := hremove C hC hCinv hCfin hCσ hDC y hy ⟨V, hV, hVO⟩
    exact ih _ (hn ▸ hlt) (C \ orbit G y) hclosed hinv'
      (hCfin.subset (image_mono sdiff_subset)) rfl
      (fun z hz => hCσ z hz.1) hD'

end Induction

section SubspaceAlgebra

variable {Y : Type uX} [TopologicalSpace Y] {Z : Set Y}

/-- A functional killing the kernel of surjective restriction descends through
the algebraic quotient; no topology on distributions is involved. -/
theorem exists_descent
    (r : SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat Z)
    (hr : ∀ f z, r f z = f z.val) (hsurj : Function.Surjective r)
    (D : Distribution Y)
    (hD : ∀ f : SchwartzBruhat Y, (∀ z ∈ Z, f z = 0) → D f = 0) :
    ∃ E : Distribution Z, ∀ f, E (r f) = D f := by
  have hker : r.ker ≤ D.ker := by
    intro f hf
    apply hD f
    intro z hz
    have heq := congrArg (fun φ : SchwartzBruhat Z => φ ⟨z, hz⟩) hf
    change r f ⟨z, hz⟩ = 0 at heq
    rwa [hr] at heq
  let E : Distribution Z :=
    (r.ker.liftQ D hker).comp (r.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  refine ⟨E, fun f => ?_⟩
  change r.ker.liftQ D hker ((r.quotKerEquivOfSurjective hsurj).symm (r f)) = D f
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

theorem restriction_pullback
    (r : SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat Z)
    (hr : ∀ f z, r f z = f z.val)
    (σ : Y ≃ₜ Y) (hσ : ∀ z ∈ Z, σ z ∈ Z ∧ σ.symm z ∈ Z)
    (f : SchwartzBruhat Y) :
    r (Hecke.TestFunction.pullback σ f) =
      Hecke.TestFunction.pullback (restrictHomeomorph σ Z hσ) (r f) := by
  ext z
  simp only [hr, Hecke.TestFunction.pullback_apply, restrictHomeomorph_apply]

theorem descent_pushforward
    (r : SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat Z)
    (hr : ∀ f z, r f z = f z.val) (hsurj : Function.Surjective r)
    (D : Distribution Y) (E : Distribution Z) (hE : ∀ f, E (r f) = D f)
    (σ : Y ≃ₜ Y) (hσ : ∀ z ∈ Z, σ z ∈ Z ∧ σ.symm z ∈ Z) (c : ℂ)
    (hD : pushforward σ D = c • D) :
    pushforward (restrictHomeomorph σ Z hσ) E = c • E := by
  ext φ
  obtain ⟨f, rfl⟩ := hsurj φ
  change E (Hecke.TestFunction.pullback (restrictHomeomorph σ Z hσ) (r f)) = c • E (r f)
  rw [← restriction_pullback r hr, hE, hE]
  exact congrArg (fun F : Distribution Y => F f) hD

variable {U : Set Y}

/-- A test function whose support lies in a subset restricts to a test function
on that subset; no openness or closedness is needed for this direction. -/
theorem exists_restriction_of_support_subset (f : SchwartzBruhat Y)
    (hf : ∀ y, y ∉ U → f y = 0) :
    ∃ φ : SchwartzBruhat U, ∀ u, φ u = f u.val := by
  have hsub : Function.support f ⊆ Set.range (Subtype.val : U → Y) := by
    intro y hy
    have hyU : y ∈ U := by
      by_contra h
      exact hy (hf y h)
    exact ⟨⟨y, hyU⟩, rfl⟩
  have hcomp : IsCompact ((Subtype.val : U → Y) ⁻¹' Function.support f) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage'
      (Hecke.TestFunction.isCompact_support f) hsub
  refine ⟨⟨fun u => f u.val,
    f.locallyConstant.comp_continuous continuous_subtype_val, ?_⟩, fun _ => rfl⟩
  exact HasCompactSupport.intro' hcomp
    ((Hecke.TestFunction.isClopen_support f).isClosed.preimage continuous_subtype_val)
    (fun u hu => not_not.mp hu)

/-- The pointwise laws alone characterize the image of extension by zero. -/
theorem exists_extension_eq
    (e : SchwartzBruhat U →ₗ[ℂ] SchwartzBruhat Y)
    (he : ∀ f u, e f u.val = f u) (hoff : ∀ f y, y ∉ U → e f y = 0)
    (f : SchwartzBruhat Y) (hf : ∀ y, y ∉ U → f y = 0) :
    ∃ φ, e φ = f := by
  obtain ⟨φ, hφ⟩ := exists_restriction_of_support_subset f hf
  refine ⟨φ, ?_⟩
  ext y
  by_cases hy : y ∈ U
  · exact (he φ ⟨y, hy⟩).trans (hφ ⟨y, hy⟩)
  · exact (hoff φ y hy).trans (hf y hy).symm

theorem extension_pullback
    (e : SchwartzBruhat U →ₗ[ℂ] SchwartzBruhat Y)
    (he : ∀ f u, e f u.val = f u) (hoff : ∀ f y, y ∉ U → e f y = 0)
    (σ : Y ≃ₜ Y) (hσ : ∀ u ∈ U, σ u ∈ U ∧ σ.symm u ∈ U)
    (f : SchwartzBruhat U) :
    e (Hecke.TestFunction.pullback (restrictHomeomorph σ U hσ) f) =
      Hecke.TestFunction.pullback σ (e f) := by
  ext y
  by_cases hy : y ∈ U
  · change e _ (⟨y, hy⟩ : U).val = e f (σ y)
    rw [he]
    change f _ = e f (⟨σ y, (hσ y hy).1⟩ : U).val
    rw [he]
    rfl
  · have hσy : σ y ∉ U := fun h => hy (by simpa using (hσ (σ y) h).2)
    simp only [hoff _ y hy, Hecke.TestFunction.pullback_apply, hoff _ (σ y) hσy]

theorem extension_dual_pushforward
    (e : SchwartzBruhat U →ₗ[ℂ] SchwartzBruhat Y)
    (he : ∀ f u, e f u.val = f u) (hoff : ∀ f y, y ∉ U → e f y = 0)
    (D : Distribution Y) (σ : Y ≃ₜ Y)
    (hσ : ∀ u ∈ U, σ u ∈ U ∧ σ.symm u ∈ U) (c : ℂ)
    (hD : pushforward σ D = c • D) :
    pushforward (restrictHomeomorph σ U hσ) (D.comp e) = c • D.comp e := by
  ext f
  change D (e (Hecke.TestFunction.pullback (restrictHomeomorph σ U hσ) f)) =
    c • D (e f)
  rw [extension_pullback e he hoff]
  exact congrArg (fun F : Distribution Y => F (e f)) hD

end SubspaceAlgebra

section OrbitRemoval

variable [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G]
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [ContinuousSMul G X]

/-- Restrict a supported distribution to a relatively open orbit, use homogeneous
vanishing there, and conclude that the distribution is supported on its complement. -/
theorem open_orbit_removal
    (hhom : HomogeneousAntiInvariantVanishingStatement.{uG, uX})
    (hclosed : SchwartzBruhat.ClosedRestrictionSurjectiveStatement.{uX})
    (σ : X ≃ₜ X) {Z : Set X} (hZ : IsClosed Z)
    (hinv : ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z)
    (hσ : ∀ z ∈ Z, σ z ∈ orbit G z ∧ σ.symm z ∈ orbit G z)
    (D : Distribution X)
    (hD : ∀ f : SchwartzBruhat X, (∀ z ∈ Z, f z = 0) → D f = 0)
    (hDinv : ∀ g : G, pushforward (Homeomorph.smul g) D = D)
    (hDanti : pushforward σ D = -D)
    {y : X} (hy : y ∈ Z) {V : Set X} (hV : IsOpen V)
    (hVO : V ∩ Z = orbit G y) :
    ∀ f : SchwartzBruhat X, (∀ z ∈ Z \ orbit G y, f z = 0) → D f = 0 := by
  let A : SubMulAction G X := ⟨Z, fun g _ hx => hinv g _ hx⟩
  have : LocallyCompactSpace A := hZ.locallyCompactSpace
  let r : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Z := SchwartzBruhat.restrictClosed hZ
  have hr : ∀ f z, r f z = f z.val :=
    fun f z => SchwartzBruhat.restrictClosed_apply hZ f z
  have hsurj : Function.Surjective r := hclosed X Z hZ
  obtain ⟨E, hE⟩ := exists_descent r hr hsurj D hD
  let σA : A ≃ₜ A := restrictHomeomorph σ Z (orbit_preserving_on_subset hinv hσ)
  have hEA : pushforward σA E = -E := by
    have h := descent_pushforward r hr hsurj D E hE σ
      (orbit_preserving_on_subset hinv hσ) (-1) (by simpa using hDanti)
    simpa only [neg_one_smul] using h
  have hEinv : ∀ g : G, pushforward (Homeomorph.smul g : A ≃ₜ A) E = E := by
    intro g
    have hg : ∀ z ∈ Z,
        Homeomorph.smul g z ∈ Z ∧ (Homeomorph.smul g).symm z ∈ Z :=
      fun z hz => ⟨hinv g z hz, hinv g⁻¹ z hz⟩
    have heq : restrictHomeomorph (Homeomorph.smul g) Z hg =
        (Homeomorph.smul g : A ≃ₜ A) := by
      ext a
      rfl
    have h := descent_pushforward r hr hsurj D E hE (Homeomorph.smul g) hg 1
      (by simpa only [one_smul] using hDinv g)
    simpa only [heq, one_smul] using h
  let yA : A := ⟨y, hy⟩
  let O : Set A := orbit G yA
  have hO : IsOpen O := by
    have hOeq : O = Subtype.val ⁻¹' V := by
      ext a
      change a ∈ orbit G yA ↔ a.val ∈ V
      rw [SubMulAction.mem_orbit_subMul_iff]
      constructor
      · intro ha
        exact (hVO.symm ▸ ha).1
      · intro ha
        exact hVO ▸ ⟨ha, a.property⟩
    rw [hOeq]
    exact hV.preimage continuous_subtype_val
  have : LocallyCompactSpace O := hO.locallyCompactSpace
  have : ContinuousSMul G O :=
    Topology.IsInducing.subtypeVal.continuousSMul continuous_id rfl
  have hσA : ∀ a : A, σA a ∈ orbit G a ∧ σA.symm a ∈ orbit G a := by
    intro a
    exact ⟨SubMulAction.mem_orbit_subMul_iff.mpr (hσ a.val a.property).1,
      SubMulAction.mem_orbit_subMul_iff.mpr (hσ a.val a.property).2⟩
  have hσO : ∀ a ∈ O, σA a ∈ O ∧ σA.symm a ∈ O :=
    orbit_preserving_on_orbit (Z := Set.univ) (fun _ _ _ => mem_univ _)
      (fun a _ => hσA a) (mem_univ yA)
  let σO : O ≃ₜ O := restrictHomeomorph σA O hσO
  let e : SchwartzBruhat O →ₗ[ℂ] SchwartzBruhat A := SchwartzBruhat.extendZero hO
  have he : ∀ f u, e f u.val = f u :=
    fun f u => SchwartzBruhat.extendZero_apply_subtype hO f u
  have hoff : ∀ f a, a ∉ O → e f a = 0 :=
    fun f _ ha => SchwartzBruhat.extendZero_apply_of_not_mem hO f ha
  let F : Distribution O := E.comp e
  have hFinv : ∀ g : G, pushforward (Homeomorph.smul g) F = F := by
    intro g
    have hg : ∀ a ∈ O,
        Homeomorph.smul g a ∈ O ∧ (Homeomorph.smul g).symm a ∈ O :=
      fun a ha => ⟨mem_orbit_of_mem_orbit g ha, mem_orbit_of_mem_orbit g⁻¹ ha⟩
    have heq : restrictHomeomorph (Homeomorph.smul g) O hg =
        (Homeomorph.smul g : O ≃ₜ O) := by
      ext a
      rfl
    have h := extension_dual_pushforward e he hoff E (Homeomorph.smul g) hg 1
      (by simpa only [one_smul] using hEinv g)
    simpa only [heq, one_smul] using h
  have hFanti : pushforward σO F = -F := by
    have h := extension_dual_pushforward e he hoff E σA hσO (-1)
      (by simpa only [neg_one_smul] using hEA)
    simpa only [neg_one_smul] using h
  have hFzero : F = 0 := hhom G O σO F hFinv hFanti
  intro f hf
  obtain ⟨φ, hφ⟩ := exists_extension_eq e he hoff (r f) (by
    intro a ha
    rw [hr]
    apply hf a.val
    refine ⟨a.property, fun haO => ha ?_⟩
    exact SubMulAction.mem_orbit_subMul_iff.mpr haO)
  calc
    D f = E (r f) := (hE f).symm
    _ = F φ := by change E (r f) = E (e φ); rw [hφ]
    _ = 0 := congrArg (fun Q : Distribution O => Q φ) hFzero

/-- The finite-orbit statement follows from homogeneous vanishing and
surjectivity of closed restriction, all at the original universes. -/
theorem finiteOrbitVanishing_of_homogeneous_and_subspace
    (hhom : HomogeneousAntiInvariantVanishingStatement.{uG, uX})
    (hclosed : SchwartzBruhat.ClosedRestrictionSurjectiveStatement.{uX}) :
    FiniteOrbitAntiInvariantVanishingStatement.{uG, uX} := by
  intro G _ _ _ _ _ X _ _ _ _ _ _ σ Z s hZ hZs hσ D hD hDinv hDanti
  apply vanishing_of_orbit_removal σ D ?_ hZ (orbit_union_invariant s hZs)
    (finite_orbit_image_of_finset s hZs) hσ hD
  intro C hC hCinv _ hCσ hDC y hy hV
  obtain ⟨V, hV, hVO⟩ := hV
  exact open_orbit_removal hhom hclosed σ hC hCinv hCσ D hDC hDinv hDanti hy hV hVO

end OrbitRemoval

/-- The published homogeneous theorem discharges the single-orbit input.
Only the published closed-restriction surjectivity proposition remains. -/
theorem finiteOrbitVanishing_of_closedRestriction
    (hclosed : SchwartzBruhat.ClosedRestrictionSurjectiveStatement.{uX}) :
    FiniteOrbitAntiInvariantVanishingStatement.{uG, uX} :=
  finiteOrbitVanishing_of_homogeneous_and_subspace
    homogeneousAntiInvariantVanishing.{uG, uX} hclosed

end FiniteOrbitVanishingProof

/-- Every invariant, anti-invariant distribution supported on a closed finite
union of orbits vanishes, with the exact published hypotheses and universes. -/
theorem finiteOrbitAntiInvariantVanishing :
    FiniteOrbitAntiInvariantVanishingStatement.{uG, uX} :=
  FiniteOrbitVanishingProof.finiteOrbitVanishing_of_closedRestriction
    SchwartzBruhat.closedRestrictionSurjective.{uX}

end Langlands.HarmonicAnalysis.Distribution
