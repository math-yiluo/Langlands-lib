import Langlands.Group.PrescribedChamberCartanCover
import Langlands.Representation.CuspidalSupport.RationalNormKernelPositiveGenerators
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Aubert.General.RationalIwasawaCartan

/-! # Central Cartan charts retaining the actual norm-kernel orthant -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.BruhatTits.SpecialCompact Langlands.Plancherel.RenardCartan

namespace Langlands.Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} [Fintype (SimpleRoot i ν)]
    (d : NormKernelFundamentalCocharacters i ν)

/-- One ambient chart for the specified norm-kernel orthant, with the final
factor in the full rational-point center. -/
def normKernelCentralCartanChart (K₀ : Subgroup (rationalPoints G))
    (t : rationalPoints G) : Set (rationalPoints G) :=
  {g | ∃ n : SimpleRoot i ν → ℕ, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀,
    ∃ z ∈ Subgroup.center (rationalPoints G),
      g = k₁ * ((d.orthantHom (.ofAdd n)).val * t) * k₂ * z}

@[simp] theorem mem_normKernelCentralCartanChart
    (K₀ : Subgroup (rationalPoints G)) (t g : rationalPoints G) :
    g ∈ normKernelCentralCartanChart d K₀ t ↔
      ∃ n : SimpleRoot i ν → ℕ, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀,
        ∃ z ∈ Subgroup.center (rationalPoints G),
          g = k₁ * ((d.orthantHom (.ofAdd n)).val * t) * k₂ * z :=
  Iff.rfl

/-- The supplied actual same-compact Cartan witness gives finite ambient
charts for this exact corrected orthant. -/
theorem NormKernelFundamentalCocharacters.exists_finite_centralCartanCover
    [Mono i.hom.hom.left]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
    {Z : GroupScheme (Spec (CommRingCat.of F))} (j : Z ⟶ G)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))
    (hsj : s ≫ j = i)
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    {F₀ : Set (rationalPoints Z)} (hF₀ : IsFiniteLatticeTransversal s F₀) :
    ∃ T : Set (rationalPoints G), T.Finite ∧
      ∀ g : rationalPoints G, ∃ t ∈ T,
        g ∈ normKernelCentralCartanChart d (D.specialCompactSubgroup x) t := by
  let : Smooth G.X.hom := hG.smooth
  classical
  have hfull : levi i ν Finset.univ = ⊤ :=
    levi_univ_eq_top i ν hStandard hG hi hν
  have hexists (I : Finset (SimpleRoot i ν)) :
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ :=
    (hStandard F G hG S i hi ν hν _ (rootSet_subset i ν I)).1
  have hfinite : (simpleRelativeRoots i ν).Finite := Set.finite_coe_iff.mp inferInstance
  have hcentral (c : cocharacterLattice S)
      (hc : ∀ α, simpleRootPairing i ν α c = 0) :
      uniformizerPowers i (.ofAdd c) ∈ Subgroup.center (rationalPoints G) := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    exact commute_uniformizerPowers i ν hfinite Finset.univ (hexists _) c
      (fun β _ => hc β) g (by rw [hfull]; exact Subgroup.mem_top _)
  obtain ⟨jM, _, _, _, _, _, _, hlat⟩ := hcompat ∅ (Set.empty_subset _)
  obtain ⟨B, hB⟩ :=
    exists_rep_rationalCartanSet i ν j s h hsj hlat.1 hF₀.1 Finset.univ
  have hcover : ∀ g : rationalPoints G,
      ∃ k₁ ∈ D.specialCompactSubgroup x, ∃ c : cocharacterLattice S,
        ∃ f ∈ rationalPoints.map j '' F₀, ∃ k₂ ∈ D.specialCompactSubgroup x,
          (∀ α, -B ≤ simpleRootPairing i ν α c) ∧
            g = k₁ * uniformizerPowers i (.ofAdd c) * f * k₂ := by
    intro g
    obtain ⟨k₁, hk₁, t, ht, k₂, hk₂, hg⟩ :=
      exists_cartan_levi D x ν hcompat hF₀ Finset.univ g
        (by rw [hfull]; exact Subgroup.mem_top _)
    obtain ⟨c, f, hf, htcf, hc⟩ := hB t ht
    refine ⟨k₁, hk₁.1, c, f, hf, k₂, hk₂.1,
      fun α => hc α (Finset.mem_univ α), ?_⟩
    simpa only [htcf, mul_assoc] using hg
  obtain ⟨T, hT, hcharts⟩ := exists_finite_prescribed_chamber_cartan_cover
    (D.specialCompactSubgroup x : Set (rationalPoints G))
    (uniformizerPowers i) (simpleRootPairing i ν) d.cocharacter
    (fun α => d.pair_pos α) (fun α β hβα => d.pair_eq_zero α β hβα)
    (rationalPoints.map j '' F₀) (hF₀.1.image _) hcentral B hcover
  refine ⟨T, hT, fun g => ?_⟩
  obtain ⟨n, k₁, hk₁, t, ht, k₂, hk₂, z, hz, hg⟩ := hcharts g
  refine ⟨t, ht, n, k₁, hk₁, k₂, hk₂, z, hz, ?_⟩
  change g = k₁ * (uniformizerPowers i (.ofAdd (∑ α, n α • d.cocharacter α)) * t) * k₂ * z
  simpa only [mul_assoc] using hg

/-- Literal factorization interface for the same prescribed orthant and finite
residual set, ready for the actual subgroup residual-cover construction. -/
theorem NormKernelFundamentalCocharacters.exists_finite_centralCartanFactorization
    [Mono i.hom.hom.left]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
    {Z : GroupScheme (Spec (CommRingCat.of F))} (j : Z ⟶ G)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))
    (hsj : s ≫ j = i)
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    {F₀ : Set (rationalPoints Z)} (hF₀ : IsFiniteLatticeTransversal s F₀) :
    ∃ T : Set (rationalPoints G), T.Finite ∧
      ∀ g : rationalPoints G, ∃ n : SimpleRoot i ν → ℕ,
        ∃ k₁ ∈ D.specialCompactSubgroup x, ∃ t ∈ T,
          ∃ k₂ ∈ D.specialCompactSubgroup x,
            ∃ z ∈ Subgroup.center (rationalPoints G),
              g = k₁ * ((d.orthantHom (.ofAdd n)).val * t) * k₂ * z := by
  obtain ⟨T, hT, hcover⟩ :=
    d.exists_finite_centralCartanCover hG hi hν hStandard D x j s h hsj hcompat hF₀
  refine ⟨T, hT, fun g => ?_⟩
  obtain ⟨t, ht, n, k₁, hk₁, k₂, hk₂, z, hz, hg⟩ := hcover g
  exact ⟨n, k₁, hk₁, t, ht, k₂, hk₂, z, hz, hg⟩

end Langlands.Aubert.General.RationalPointFamily
