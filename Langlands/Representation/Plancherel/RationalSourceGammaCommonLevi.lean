import Langlands.Representation.Plancherel.RationalSourceGammaWall
import Langlands.Representation.Plancherel.RationalPlancherelConstantFinite
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.StandardRestrictedConjugation
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # The actual source gamma is constant on the parabolics of one semistandard Levi -/

noncomputable section

namespace Langlands.Plancherel.SourceGammaCommonLevi

/-- **The first sign change.** Let two integer functions `a, a'` on a finite set `R` vanish
at the same points, and let them have opposite signs somewhere. Then there are positive
integers `q, p` such that `q a + p a'` vanishes at some point where the signs differ, is
nonnegative where `a` is positive and nonpositive where `a` is negative. It may vanish at
several points where the signs differ. -/
theorem exists_first_wall {X : Type*} {R : Set X} (hR : R.Finite) (a a' : X → ℤ)
    {x₁ : X} (hx₁ : x₁ ∈ R) (hx₁s : a x₁ * a' x₁ < 0) :
    ∃ q p : ℤ, 0 < q ∧ 0 < p ∧ (∃ x₀ ∈ R, a x₀ * a' x₀ < 0 ∧ q * a x₀ + p * a' x₀ = 0) ∧
      ∀ x ∈ R, (0 < a x → 0 ≤ q * a x + p * a' x) ∧ (a x < 0 → q * a x + p * a' x ≤ 0) := by
  classical
  set D := (hR.subset (Set.sep_subset R fun x => a x * a' x < 0)).toFinset
  have hD : ∀ {x}, x ∈ D ↔ x ∈ R ∧ a x * a' x < 0 := by
    intro x
    simp [D]
  have hne : D.Nonempty := ⟨x₁, hD.2 ⟨hx₁, hx₁s⟩⟩
  obtain ⟨x₀, hx₀D, hmin⟩ := D.exists_min_image (fun x => (|a x| : ℚ) / |a' x|) hne
  obtain ⟨hx₀R, hx₀s⟩ := hD.1 hx₀D
  have ha₀ : a x₀ ≠ 0 := by intro h; rw [h, zero_mul] at hx₀s; exact lt_irrefl 0 hx₀s
  have ha₀' : a' x₀ ≠ 0 := by intro h; rw [h, mul_zero] at hx₀s; exact lt_irrefl 0 hx₀s
  refine ⟨|a' x₀|, |a x₀|, abs_pos.mpr ha₀', abs_pos.mpr ha₀, ⟨x₀, hx₀R, hx₀s, ?_⟩, ?_⟩
  · rcases lt_or_gt_of_ne ha₀ with h | h
    · have h' : 0 < a' x₀ := by nlinarith
      rw [abs_of_pos h', abs_of_neg h]
      ring
    · have h' : a' x₀ < 0 := by nlinarith
      rw [abs_of_neg h', abs_of_pos h]
      ring
  · -- the cross-multiplied minimality
    have hcross : ∀ x ∈ R, a x * a' x < 0 → |a x₀| * |a' x| ≤ |a x| * |a' x₀| := by
      intro x hxR hxs
      have hx := hmin x (hD.2 ⟨hxR, hxs⟩)
      have hax : a x ≠ 0 := by intro h; rw [h, zero_mul] at hxs; exact lt_irrefl 0 hxs
      have hax' : a' x ≠ 0 := by intro h; rw [h, mul_zero] at hxs; exact lt_irrefl 0 hxs
      have h1 : (0 : ℚ) < |(a' x₀ : ℚ)| := by exact_mod_cast abs_pos.mpr ha₀'
      have h2 : (0 : ℚ) < |(a' x : ℚ)| := by exact_mod_cast abs_pos.mpr hax'
      rw [div_le_div_iff₀ (by exact_mod_cast abs_pos.mpr ha₀') (by exact_mod_cast abs_pos.mpr hax')]
        at hx
      exact_mod_cast hx
    intro x hxR
    have hq : 0 < |a' x₀| := abs_pos.mpr ha₀'
    have hp : 0 < |a x₀| := abs_pos.mpr ha₀
    constructor
    · intro hax
      rcases le_or_gt 0 (a' x) with h | h
      · nlinarith
      · have := hcross x hxR (by nlinarith)
        rw [abs_of_neg h, abs_of_pos hax] at this
        nlinarith
    · intro hax
      rcases le_or_gt (a' x) 0 with h | h
      · nlinarith
      · have := hcross x hxR (by nlinarith)
        rw [abs_of_pos h, abs_of_neg hax] at this
        nlinarith


/-- Sign bookkeeping at one root across the first wall `f = q a + p a'`, for the shifted
cocharacter with pairing `g = R f + a'`, where `R` strictly exceeds `|a|` and `|a'|`. -/
theorem wall_signs {a a' q p R : ℤ} (hq : 0 < q) (hp : 0 < p) (haR : |a| < R) (ha'R : |a'| < R)
    (hz : a = 0 ↔ a' = 0) (h1 : 0 < a → 0 ≤ q * a + p * a')
    (h2 : a < 0 → q * a + p * a' ≤ 0) :
    (a = 0 → q * a + p * a' = 0) ∧
    (0 < q * a + p * a' → 0 < a) ∧
    (0 < q * a + p * a' → 0 < R * (q * a + p * a') + a') ∧
    (0 < -(q * a + p * a') → 0 < -a) ∧
    (0 < -(q * a + p * a') → 0 < -(R * (q * a + p * a') + a')) ∧
    (0 ≤ a → 0 ≤ q * a + p * a') ∧
    (0 ≤ R * (q * a + p * a') + a' → 0 ≤ q * a + p * a') ∧
    (0 ≤ -a → 0 ≤ -(q * a + p * a')) ∧
    (0 ≤ -(R * (q * a + p * a') + a') → 0 ≤ -(q * a + p * a')) ∧
    (0 < a + -(R * (q * a + p * a')) ↔ 0 < -(R * (q * a + p * a') + a')) ∧
    (0 < -a + R * (q * a + p * a') ↔ 0 < R * (q * a + p * a') + a') ∧
    (R * (q * a + p * a') + a' = 0 ↔ a' = 0) ∧
    (R * (q * a + p * a') + a' = 0 ↔ a = 0) ∧
    ((R * (q * a + p * a') + a') * a' < 0 → a * a' < 0) ∧
    (q * a + p * a' = 0 → ¬ (R * (q * a + p * a') + a') * a' < 0) := by
  obtain ⟨haR1, haR2⟩ := abs_lt.mp haR
  obtain ⟨ha'R1, ha'R2⟩ := abs_lt.mp ha'R
  set f := q * a + p * a' with hf
  rcases lt_trichotomy f 0 with hneg | hzero | hpos
  · have hf1 : f ≤ -1 := by omega
    have hRf : R * f ≤ -R := by nlinarith
    have ha : a < 0 := by
      rcases lt_trichotomy a 0 with h | h | h
      · exact h
      · exact absurd (by rw [hf, h, hz.mp h]; ring) hneg.ne
      · exact absurd (h1 h) (not_le.mpr hneg)
    have hRf' : -R ≥ R * f := hRf
    refine ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun _ => by omega,
      fun _ => by linarith, fun h => by omega, fun h => by linarith, fun _ => by omega,
      fun _ => by omega, ⟨fun h => by linarith, fun _ => by linarith⟩,
      ⟨fun h => by linarith, fun h => by linarith⟩,
      ⟨fun h => by linarith, fun h => absurd (hz.mpr h) ha.ne⟩,
      ⟨fun h => by linarith, fun h => by omega⟩, fun h => ?_, fun h => by omega⟩
    have hg : R * f + a' < 0 := by linarith
    have : 0 < a' := by nlinarith
    nlinarith
  · have hRf : R * f = 0 := by rw [hzero, mul_zero]
    have hA : 0 < a → a' < 0 := fun h => by nlinarith
    have hB : a < 0 → 0 < a' := fun h => by nlinarith
    have hC : a' < 0 → 0 < a := fun h => by
      rcases lt_trichotomy a 0 with h' | h' | h'
      · exact absurd (hB h') (not_lt.mpr h.le)
      · exact absurd (hz.mp h') h.ne
      · exact h'
    have hD : 0 < a' → a < 0 := fun h => by
      rcases lt_trichotomy a 0 with h' | h' | h'
      · exact h'
      · exact absurd (hz.mp h') h.ne'
      · exact absurd (hA h') (not_lt.mpr h.le)
    rw [hRf]
    refine ⟨fun _ => hzero, fun h => by omega, fun h => by omega, fun h => by omega,
      fun h => by omega, fun _ => by omega, fun _ => by omega, fun _ => by omega,
      fun _ => by omega, ⟨fun h => by have := hA (by omega); omega,
        fun h => by have := hC (by omega); omega⟩,
      ⟨fun h => by have := hB (by omega); omega, fun h => by have := hD (by omega); omega⟩,
      ⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => hz.mpr (by omega), fun h => by
        rw [hz.mp h]; ring⟩, fun h => by rw [zero_add] at h; nlinarith [mul_self_nonneg a'],
      fun _ h => by rw [zero_add] at h; nlinarith [mul_self_nonneg a']⟩
  · have hf1 : 1 ≤ f := by omega
    have hRf : R ≤ R * f := by nlinarith
    have ha : 0 < a := by
      rcases lt_trichotomy a 0 with h | h | h
      · exact absurd (h2 h) (not_le.mpr hpos)
      · exact absurd (by rw [hf, h, hz.mp h]; ring) hpos.ne'
      · exact h
    refine ⟨fun h => by omega, fun _ => ha, fun _ => by linarith, fun h => by omega,
      fun h => by omega, fun _ => hpos.le, fun _ => hpos.le, fun h => by omega,
      fun h => by linarith, ⟨fun h => by linarith, fun h => by linarith⟩,
      ⟨fun _ => by linarith, fun _ => by linarith⟩,
      ⟨fun h => by linarith, fun h => absurd (hz.mpr h) ha.ne'⟩,
      ⟨fun h => by linarith, fun h => by omega⟩, fun h => ?_, fun h => by omega⟩
    have hg : 0 < R * f + a' := by linarith
    have : a' < 0 := by nlinarith
    nlinarith

end Langlands.Plancherel.SourceGammaCommonLevi

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz SourceGammaCommonLevi
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

local instance sourceGammaCommonLeviAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance sourceGammaCommonLeviPointTopology : TopologicalSpace (RationalPoint F G.X) :=
  rationalPointTopology F G.X
local instance sourceGammaCommonLeviPointMeasurable : MeasurableSpace (RationalPoint F G.X) :=
  borel (RationalPoint F G.X)
local instance sourceGammaCommonLeviPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

/-- **Source gamma on a common Levi.** For two cocharacters of a maximal split torus whose
pairings vanish at exactly the same relative roots, the actual source gammas agree, provided
the common compact is limit-stable for the dynamic parabolic of every cocharacter of the
torus. Each step of the proof uses the integral cocharacter `φ = q ζ + p ζ'` representing
the first sign change `(q ζ + p ζ') / (q + p)` on the real segment between the two
cocharacters, which may lie on several root hyperplanes at once. It replaces `ζ` by
`R φ + ζ'`, with `R` strictly larger than all root pairings in absolute value; after
division by `R (q + p) + 1` this is a point of the segment just past the crossing. The
number of roots on which the two cocharacters have opposite signs strictly decreases. -/
theorem gamma_eq_of_pairing_zero_iff (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hKs : ∀ (ξ : cocharacterLattice S)
      (p : (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀),
      (p : RationalPoint F G.X) ∈ K →
        (Dynamic.limitHom (CommGroupScheme.groupHom ξ ≫ i) X₀ p : RationalPoint F G.X) ∈ K)
    (ζ ζ' : cocharacterLattice S)
    (hz : ∀ α ∈ relativeRoots i, latticePairing S α ζ = 0 ↔ latticePairing S α ζ' = 0) :
    gamma (CommGroupScheme.groupHom ζ ≫ i) K hK =
      gamma (CommGroupScheme.groupHom ζ' ≫ i) K hK := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hfin := hT.finite_relativeRoots i
  have hsign := relativeRootSignInclusions F G hG S i hi
  have hcent : ∀ ν ξ : cocharacterLattice S,
      (∀ α ∈ relativeRoots i, latticePairing S α ν = 0 → latticePairing S α ξ = 0) →
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier X₀ ≤
        (Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀ :=
    fun ν ξ h x hx => dynamicCentralizer_le_of_pairing hT i ν ξ h X₀ hx
  have hunip : ∀ ν ξ : cocharacterLattice S,
      (∀ α ∈ relativeRoots i, 0 < latticePairing S α ν → 0 < latticePairing S α ξ) →
      unipotentPoints (CommGroupScheme.groupHom ν ≫ i) ≤
        unipotentPoints (CommGroupScheme.groupHom ξ ≫ i) :=
    fun ν ξ h => (hsign ν ξ).2 h X₀
  have hpar : ∀ ν ξ : cocharacterLattice S,
      (∀ α ∈ relativeRoots i, 0 ≤ latticePairing S α ν → 0 ≤ latticePairing S α ξ) →
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier X₀ ≤
        (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀ :=
    fun ν ξ h => (hsign ν ξ).1.mpr h X₀
  have eopp : ∀ ν : cocharacterLattice S,
      oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i) =
        CommGroupScheme.groupHom (-ν) ≫ i :=
    fun ν => (groupHom_neg_comp_eq_oppositeCocharacter i ν).symm
  set D : cocharacterLattice S → Set (characterLattice S) := fun ξ =>
    {α | α ∈ relativeRoots i ∧ latticePairing S α ξ * latticePairing S α ζ' < 0} with hDdef
  have hDfin : ∀ ξ, (D ξ).Finite := fun ξ => hfin.subset fun α h => h.1
  suffices key : ∀ (n : ℕ) (ξ : cocharacterLattice S), (D ξ).ncard = n →
      (∀ α ∈ relativeRoots i, latticePairing S α ξ = 0 ↔ latticePairing S α ζ' = 0) →
      gamma (CommGroupScheme.groupHom ξ ≫ i) K hK =
        gamma (CommGroupScheme.groupHom ζ' ≫ i) K hK from key _ ζ rfl hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ξ hn hξ
  by_cases hD : ∃ α ∈ relativeRoots i, latticePairing S α ξ * latticePairing S α ζ' < 0
  · obtain ⟨α₁, hα₁, hα₁s⟩ := hD
    obtain ⟨q, p, hq, hp, ⟨α₀, hα₀R, hα₀s, hα₀f⟩, hwall⟩ :=
      exists_first_wall hfin (fun α => latticePairing S α ξ) (fun α => latticePairing S α ζ')
        hα₁ hα₁s
    obtain ⟨M, hM⟩ := (hfin.image fun α =>
      |latticePairing S α ξ| + |latticePairing S α ζ'|).bddAbove
    set R : ℤ := M + 1 with hRdef
    have hR : ∀ α ∈ relativeRoots i,
        |latticePairing S α ξ| < R ∧ |latticePairing S α ζ'| < R := by
      intro α hα
      have h : |latticePairing S α ξ| + |latticePairing S α ζ'| ≤ M := hM ⟨α, hα, rfl⟩
      have h1 := abs_nonneg (latticePairing S α ξ)
      have h2 := abs_nonneg (latticePairing S α ζ')
      exact ⟨by omega, by omega⟩
    set φ : cocharacterLattice S := q • ξ + p • ζ' with hφdef
    set ξ₁ : cocharacterLattice S := R • φ + ζ' with hξ₁def
    have hφp : ∀ α, latticePairing S α φ =
        q * latticePairing S α ξ + p * latticePairing S α ζ' := by
      intro α
      simp only [hφdef, map_add, map_zsmul, smul_eq_mul]
    have hξ₁p : ∀ α, latticePairing S α ξ₁ =
        R * (q * latticePairing S α ξ + p * latticePairing S α ζ') +
          latticePairing S α ζ' := by
      intro α
      simp only [hξ₁def, map_add, map_zsmul, smul_eq_mul, hφp]
    have hsg := fun α (hα : α ∈ relativeRoots i) =>
      wall_signs hq hp (hR α hα).1 (hR α hα).2 (hξ α hα) (hwall α hα).1 (hwall α hα).2
    have hξ₁z : ∀ α ∈ relativeRoots i,
        latticePairing S α ξ₁ = 0 ↔ latticePairing S α ζ' = 0 := by
      intro α hα
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, s12, -, -, -⟩ := hsg α hα
      rw [hξ₁p]
      exact s12
    have hlt : (D ξ₁).ncard < n := by
      rw [← hn]
      refine Set.ncard_lt_ncard ⟨fun α hα => ⟨hα.1, ?_⟩, fun hsub => ?_⟩ (hDfin ξ)
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, s14, -⟩ := hsg α hα.1
        have h := hα.2
        rw [hξ₁p] at h
        exact s14 h
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, s15⟩ := hsg α₀ hα₀R
        have h := (hsub ⟨hα₀R, hα₀s⟩).2
        rw [hξ₁p] at h
        exact s15 hα₀f h
    rw [← ih _ hlt ξ₁ rfl hξ₁z]
    have hshift : ∀ (c : ℤ) (ν : cocharacterLattice S) {x : RationalPoint F G.X},
        x ∈ (Dynamic.centralizer (CommGroupScheme.groupHom φ ≫ i)).carrier X₀ →
        (x ∈ unipotentPoints (CommGroupScheme.groupHom (ν + c • φ) ≫ i) ↔
          x ∈ unipotentPoints (CommGroupScheme.groupHom ν ≫ i)) := by
      intro c ν x hx
      exact Dynamic.mem_unipotent_add_iff_of_mem_centralizer i ν (c • φ) x
        (hcent φ (c • φ) (fun α _ h => by rw [map_zsmul, h, smul_zero]) hx)
    refine gamma_eq_of_wall hG _ _ (CommGroupScheme.groupHom φ ≫ i) K hK ?hM ?hML ?hNU ?hNU'
      ?hNV ?hNV' ?hUP ?hUP' ?hVP ?hVP' ?hB ?hC (hKs ξ) (hKs ξ₁) (hKs φ) ?hφ'
    case hM =>
      refine le_antisymm (hcent ξ₁ ξ fun α hα h => ?_) (hcent ξ ξ₁ fun α hα h => ?_)
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, s13, -, -⟩ := hsg α hα
        rw [hξ₁p] at h
        exact s13.mp h
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, s13, -, -⟩ := hsg α hα
        rw [hξ₁p]
        exact s13.mpr h
    case hML =>
      refine hcent ξ φ fun α hα h => ?_
      obtain ⟨s1, -⟩ := hsg α hα
      rw [hφp]
      exact s1 h
    case hNU =>
      refine hunip φ ξ fun α hα h => ?_
      obtain ⟨-, s2, -⟩ := hsg α hα
      rw [hφp] at h
      exact s2 h
    case hNU' =>
      refine hunip φ ξ₁ fun α hα h => ?_
      obtain ⟨-, -, s3, -⟩ := hsg α hα
      rw [hφp] at h
      rw [hξ₁p]
      exact s3 h
    case hNV =>
      rw [eopp, eopp]
      refine hunip (-φ) (-ξ) fun α hα h => ?_
      obtain ⟨-, -, -, s4, -⟩ := hsg α hα
      rw [map_neg, hφp] at h
      rw [map_neg]
      exact s4 h
    case hNV' =>
      rw [eopp, eopp]
      refine hunip (-φ) (-ξ₁) fun α hα h => ?_
      obtain ⟨-, -, -, -, s5, -⟩ := hsg α hα
      rw [map_neg, hφp] at h
      rw [map_neg, hξ₁p]
      exact s5 h
    case hUP =>
      refine fun x hx => hpar ξ φ (fun α hα h => ?_) (Dynamic.unipotent_le_parabolic _ X₀ hx)
      obtain ⟨-, -, -, -, -, s6, -⟩ := hsg α hα
      rw [hφp]
      exact s6 h
    case hUP' =>
      refine fun x hx => hpar ξ₁ φ (fun α hα h => ?_) (Dynamic.unipotent_le_parabolic _ X₀ hx)
      obtain ⟨-, -, -, -, -, -, s7, -⟩ := hsg α hα
      rw [hξ₁p] at h
      rw [hφp]
      exact s7 h
    case hVP =>
      rw [eopp, eopp]
      refine fun x hx => hpar (-ξ) (-φ) (fun α hα h => ?_)
        (Dynamic.unipotent_le_parabolic _ X₀ hx)
      obtain ⟨-, -, -, -, -, -, -, s8, -⟩ := hsg α hα
      rw [map_neg] at h
      rw [map_neg, hφp]
      exact s8 h
    case hVP' =>
      rw [eopp, eopp]
      refine fun x hx => hpar (-ξ₁) (-φ) (fun α hα h => ?_)
        (Dynamic.unipotent_le_parabolic _ X₀ hx)
      obtain ⟨-, -, -, -, -, -, -, -, s9, -⟩ := hsg α hα
      rw [map_neg, hξ₁p] at h
      rw [map_neg, hφp]
      exact s9 h
    case hB =>
      rw [eopp]
      have hU : unipotentPoints (CommGroupScheme.groupHom (ξ + (-R) • φ) ≫ i) =
          unipotentPoints (CommGroupScheme.groupHom (-ξ₁) ≫ i) := by
        have hpe : ∀ α, latticePairing S α (ξ + (-R) • φ) = latticePairing S α ξ +
            -(R * (q * latticePairing S α ξ + p * latticePairing S α ζ')) := by
          intro α
          simp only [map_add, map_zsmul, smul_eq_mul, hφp]
          ring
        refine le_antisymm (hunip _ _ fun α hα h => ?_) (hunip _ _ fun α hα h => ?_)
        · obtain ⟨-, -, -, -, -, -, -, -, -, s10, -⟩ := hsg α hα
          rw [hpe] at h
          rw [map_neg, hξ₁p]
          exact s10.mp h
        · obtain ⟨-, -, -, -, -, -, -, -, -, s10, -⟩ := hsg α hα
          rw [map_neg, hξ₁p] at h
          rw [hpe]
          exact s10.mpr h
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hxU, hxL⟩
        refine ⟨?_, hxL⟩
        rw [← hU]
        exact (hshift (-R) ξ hxL).mpr hxU
      · rintro ⟨hxU, hxL⟩
        refine ⟨?_, hxL⟩
        rw [← hU] at hxU
        exact (hshift (-R) ξ hxL).mp hxU
    case hC =>
      rw [eopp]
      have hU : unipotentPoints (CommGroupScheme.groupHom (-ξ + R • φ) ≫ i) =
          unipotentPoints (CommGroupScheme.groupHom ξ₁ ≫ i) := by
        have hpe : ∀ α, latticePairing S α (-ξ + R • φ) = -latticePairing S α ξ +
            R * (q * latticePairing S α ξ + p * latticePairing S α ζ') := by
          intro α
          simp only [map_add, map_neg, map_zsmul, smul_eq_mul, hφp]
        refine le_antisymm (hunip _ _ fun α hα h => ?_) (hunip _ _ fun α hα h => ?_)
        · obtain ⟨-, -, -, -, -, -, -, -, -, -, s11, -⟩ := hsg α hα
          rw [hpe] at h
          rw [hξ₁p]
          exact s11.mp h
        · obtain ⟨-, -, -, -, -, -, -, -, -, -, s11, -⟩ := hsg α hα
          rw [hξ₁p] at h
          rw [hpe]
          exact s11.mpr h
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hxU, hxL⟩
        refine ⟨?_, hxL⟩
        rw [← hU]
        exact (hshift R (-ξ) hxL).mpr hxU
      · rintro ⟨hxU, hxL⟩
        refine ⟨?_, hxL⟩
        rw [← hU] at hxU
        exact (hshift R (-ξ) hxL).mp hxU
    case hφ' =>
      rw [eopp]
      exact hKs (-φ)
  · push Not at hD
    have hpos : ∀ α ∈ relativeRoots i,
        (0 < latticePairing S α ξ ↔ 0 < latticePairing S α ζ') := by
      intro α hα
      have h1 := hD α hα
      have h2 := hξ α hα
      constructor
      · intro h
        rcases lt_trichotomy (latticePairing S α ζ') 0 with h' | h' | h'
        · nlinarith
        · exact absurd (h2.mpr h') h.ne'
        · exact h'
      · intro h
        rcases lt_trichotomy (latticePairing S α ξ) 0 with h' | h' | h'
        · nlinarith
        · exact absurd (h2.mp h') h.ne'
        · exact h'
    have hnn : ∀ α ∈ relativeRoots i,
        (0 ≤ latticePairing S α ξ ↔ 0 ≤ latticePairing S α ζ') := by
      intro α hα
      rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hpos α hα, eq_comm, hξ α hα, eq_comm]
    apply gamma_eq_of_dynamic_subgroups_eq
    · exact le_antisymm ((hsign ξ ζ').1.mpr fun α hα => (hnn α hα).mp)
        ((hsign ζ' ξ).1.mpr fun α hα => (hnn α hα).mpr)
    · rw [eopp, eopp]
      refine le_antisymm ((hsign (-ξ) (-ζ')).2 fun α hα h => ?_)
        ((hsign (-ζ') (-ξ)).2 fun α hα h => ?_)
      · rw [map_neg, neg_pos] at h ⊢
        by_contra hc
        exact absurd ((hnn α hα).mpr (not_lt.mp hc)) (not_le.mpr h)
      · rw [map_neg, neg_pos] at h ⊢
        by_contra hc
        exact absurd ((hnn α hα).mp (not_lt.mp hc)) (not_le.mpr h)

end Langlands.Plancherel.RationalDynamicSource
