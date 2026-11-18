import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviBoundedRegion
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UniformSplitCompactBounds
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiCentral
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme

/-! # Assembly of positive-part decay on the actual full minimal Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.HarmonicAnalysis
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

/-- Polynomial right translation commutes with pullback along a group homomorphism. -/
theorem aeval_rightFunctions_comp_hom {H L : Type*} [Group H] [Group L]
    (e : H →* L) (a : H) (p : ℂ[X]) (F : L → ℂ) :
    aeval (GroupAction.rightFunctions a) p (F ∘ e) =
      (aeval (GroupAction.rightFunctions (e a)) p F) ∘ e := by
  funext g
  change aeval (GroupAction.rightFunctions a) p (F ∘ e) g =
    aeval (GroupAction.rightFunctions (e a)) p F (e g)
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.smul_apply, Pi.smul_apply]
  rw [← (GroupAction.rightFunctions (G := H)).map_pow a k,
    GroupAction.rightFunctions_apply,
    ← (GroupAction.rightFunctions (G := L)).map_pow (e a) k,
    GroupAction.rightFunctions_apply]
  simp only [Function.comp_apply, map_mul, map_pow]

section Actual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance assemblyLeviIsAffineHom (J : Set (characterLattice S)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom := leviScheme_isAffineHom i ν J

local instance assemblyLeviLocallyOfFiniteType (J : Set (characterLattice S)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
  (hJ : J ⊆ simpleRelativeRoots i ν)
  {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (K.subgroupOf (standardLeviPoints i ν J)))

include hG hi hν hJ hKo in
/-- Continuity of the existing Levi Xi function in the canonical topology. -/
theorem continuous_rationalLeviXi : Continuous (rationalLeviXi hKc hM) := by
  have hc := (continuous_rationalXi
    (isOpen_leviSchemeCompact (i := i) (ν := ν) (J := J) hKo)
    (isCompact_leviSchemeCompact (i := i) (ν := ν) (J := J) hKc)
    (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM)).comp
      (leviSchemePointsEquiv i ν J).symm.continuous
  convert hc using 1
  funext m
  change rationalLeviXi hKc hM m =
    rationalXi (isCompact_leviSchemeCompact (i := i) (ν := ν) (J := J) hKc)
      (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM)
      ((leviSchemePointsEquiv i ν J).symm m)
  simpa only [ContinuousMulEquiv.apply_symm_apply] using
    (rationalXi_leviScheme hG hi hν hJ hKo hKc hM
      ((leviSchemePointsEquiv i ν J).symm m)).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Quantification over the finite set of outside simple forms is exactly quantification
over the corresponding actual simple roots. -/
theorem forall_mem_rationalOutsideSimpleForms_iff (R : Set (characterLattice S))
    (P : Module.Dual ℝ (RealTorusSpace.V S) → Prop) :
    (∀ f ∈ rationalOutsideSimpleForms hi (ν := ν) R, P f) ↔
      ∀ α ∈ simpleRelativeRoots i ν \ R, P (RealTorusSpace.eval S α) := by
  classical
  unfold rationalOutsideSimpleForms
  constructor
  · intro h α hα
    exact h _ (Finset.mem_image.mpr ⟨α, by simpa using hα, rfl⟩)
  · intro h f hf
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hf
    exact h α (by simpa using hα)

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)

/-- The remaining family-specific input for positive decay: uniform split annihilators at
one strictly positive component point, weighted compact bounds for the full family, and a
polynomial height bound on its full constant term in the shifted closed chamber. -/
def HasRationalSplitDecayInput {κ : Type*}
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (Φ : κ → standardLeviPoints i ν J → ℂ) : Prop :=
  ∃ x : rationalPoints A.toGrp,
    (∀ β ∈ J, RealTorusSpace.eval S β (rationalComponentH0 hG hi hν (qA := q) x) = 0) ∧
    (∀ α ∈ simpleRelativeRoots i ν \ J,
      0 < RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q) x)) ∧
    HasUniformSplitAnnihilators (standardComponentHom hA) x Φ ∧
    HasUniformWeightedCompactBounds Φ (rationalLeviXi hKc hM) ∧
    ∃ t : ℝ, 0 ≤ t ∧ ∃ C : ℝ, ∃ d : ℕ, ∀ ω m,
      m ∈ rationalConstantTermThresholdRegion hG hi hν J t →
      ‖Φ ω (minimalLeviInclusion hG hi hν J m)‖ ≤
        C * rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m) *
          (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d

include hJ hKo in
/-- The explicit family input assembles to the existing decay property on the entire closed
region in the full actual minimal Levi, for every supplied norm. This is a supporting
reduction; it does not discharge the actual induced-orbit input. -/
theorem hasRationalPositivePartDecay_of_splitInput
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : StandardLeviCartanCovering F i ν ∅ K0)
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hN : ∀ v, N v = 0 → v = 0)
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hρ : IsClosedSubgroup ρ) {κ : Type*} {Φ : κ → standardLeviPoints i ν J → ℂ}
    (hinput : HasRationalSplitDecayInput hG hi hν hKc hM hA ρ Φ) :
    HasRationalPositivePartDecay hG hi hν N J
      (fun ω m => positivePart (standardComponentHom hA) (Φ ω)
        (minimalLeviInclusion hG hi hν J m))
      (fun m => rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m)) := by
  let nn : AddGroupNorm (RealTorusSpace.V S) :=
    { N.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := hN }
  let : NormedAddCommGroup (RealTorusSpace.V S) := nn.toNormedAddCommGroup
  let : NormedSpace ℝ (RealTorusSpace.V S) :=
    { norm_smul_le := fun a v => (map_smul_eq_mul N a v).le }
  obtain ⟨x, hx0, hx, hann, hcompactΦ, t, ht, C₁, d, hbound⟩ := hinput
  let inc := minimalLeviInclusion hG hi hν J
  let a := rationalMinimalComponentHom (i := i) (ν := ν) q x
  let S₀ := rationalOutsideSimpleForms hi (ν := ν) Jᶜ
  let S₁ := rationalOutsideSimpleForms hi (ν := ν) J
  have ha₀ : ∀ β ∈ S₀, β (rationalMinimalH0 hG hi hν a) = 0 := by
    exact (forall_mem_rationalOutsideSimpleForms_iff hi (ν := ν) Jᶜ
      (fun β => β (rationalMinimalH0 hG hi hν a) = 0)).mpr
      (fun β hβ => hx0 β (by simpa using hβ.2))
  have ha : ∀ α ∈ S₁, 0 < α (rationalMinimalH0 hG hi hν a) := by
    exact (forall_mem_rationalOutsideSimpleForms_iff hi J _).mpr hx
  have hB0 : ∀ m : standardLeviPoints i ν ∅,
      0 ≤ rationalLeviXi hKc hM (inc m) :=
    fun m => (rationalLeviXi_pos hKo hKc hG hi hν hJ hM (inc m)).le
  have hBa : ∀ m : standardLeviPoints i ν ∅,
      rationalLeviXi hKc hM (inc (m * a)) = rationalLeviXi hKc hM (inc m) :=
    fun m => rationalLeviXi_minimal_mul_component hG hi hν hA hKo hKc hJ hM m x
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  have hcompactp := (hann.hasUniformWeightedCompactBounds_positivePart hcompactΦ
    (fun m => rationalLeviXi_mul_standardComponentHom hG hi hν hA hKo hKc hJ hM m x)).comp inc hinc
  have hHcompact := hasMinimalLeviCompactSublevels_of_cartanCovering hG hi hν hK0 hcover N hN ρ hρ
  obtain ⟨Cσ, _, hσH⟩ := hasMinimalLeviHeightComparison_of_cartanCovering
    hG hi hν hK0 hcover N hN ρ
  have h1 : ∀ ω m, (∀ β ∈ S₀, 0 ≤ β (rationalMinimalH0 hG hi hν m)) →
      (∀ α ∈ S₁, t ≤ α (rationalMinimalH0 hG hi hν m)) →
      ‖Φ ω (inc m)‖ ≤ C₁ * rationalLeviXi hKc hM (inc m) *
        (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d := by
    intro ω m hm0 hm1
    have hm0' := (forall_mem_rationalOutsideSimpleForms_iff hi Jᶜ _).mp hm0
    have hm1' := (forall_mem_rationalOutsideSimpleForms_iff hi J _).mp hm1
    apply hbound ω m
    refine ⟨fun α hα => ?_, hm1'⟩
    by_cases hαJ : α ∈ J
    · exact hm0' α ⟨hα, by simpa using hαJ⟩
    · exact ht.trans (hm1' α ⟨hα, hαJ⟩)
  obtain ⟨Nw, Np, θ, pw, pp, _, hθ, hpw, hpp, hNw, hNp, hrw, hrp, hannw, hannp⟩ := hann
  have hsplit : ∀ ω, (fun m => Φ ω (inc m)) =
      (fun m => weakPart (standardComponentHom hA) (Φ ω) (inc m)) +
      (fun m => positivePart (standardComponentHom hA) (Φ ω) (inc m)) := by
    intro ω
    funext m
    exact (congrFun (weakPart_add_positivePart (standardComponentHom hA) (Φ ω)) (inc m)).symm
  have hannw' : ∀ ω, aeval (GroupAction.rightFunctions a) (pw ω)
      ((weakPart (standardComponentHom hA) (Φ ω)) ∘ inc) = 0 := by
    intro ω
    rw [aeval_rightFunctions_comp_hom inc a, minimalLeviInclusion_rationalMinimalComponentHom
      hG hi hν hA, hannw ω]
    rfl
  have hannp' : ∀ ω, aeval (GroupAction.rightFunctions a) (pp ω)
      ((positivePart (standardComponentHom hA) (Φ ω)) ∘ inc) = 0 := by
    intro ω
    rw [aeval_rightFunctions_comp_hom inc a, minimalLeviInclusion_rationalMinimalComponentHom
      hG hi hν hA, hannp ω]
    rfl
  intro δ hδ
  obtain ⟨Q, hQ, hsub⟩ := hHcompact (t / δ)
  obtain ⟨C₀, _, hC₀⟩ := hcompactp Q hQ
  obtain ⟨ε, hε, C, hdecay⟩ := exists_norm_le_exp_of_decomposition
    (rationalMinimalH0_mul hG hi hν) ha₀ ha
    (fun m => rationalHeight_nonneg (F := F) ρ (m : rationalPoints G))
    (fun m m' => rationalHeight_mul_le (F := F) ρ (m : rationalPoints G) (m' : rationalPoints G))
    ⟨Cσ, hσH⟩ hB0 hBa hsplit hθ hpw hpp hNw hNp hrw hrp hannw' hannp'
    ht h1 hδ (fun ω m _ _ hm => hC₀ ω m (hsub m hm))
  refine ⟨ε, hε, max C 1, zero_lt_one.trans_le (le_max_right _ _), fun ω m hm => ?_⟩
  have hm0 : ∀ β ∈ S₀, 0 ≤ β (rationalMinimalH0 hG hi hν m) :=
    (forall_mem_rationalOutsideSimpleForms_iff hi Jᶜ _).mpr fun β hβ => hm.1 β hβ.1
  have hm1 : ∀ α ∈ S₁, δ * ‖rationalMinimalH0 hG hi hν m‖ ≤
      α (rationalMinimalH0 hG hi hν m) :=
    (forall_mem_rationalOutsideSimpleForms_iff hi J _).mpr hm.2
  exact (hdecay ω m hm0 hm1).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hB0 m))
      (Real.exp_pos _).le)

end Actual

end Langlands.HarishChandraSchwartz
