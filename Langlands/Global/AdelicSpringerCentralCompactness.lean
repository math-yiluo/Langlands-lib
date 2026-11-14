import Langlands.Global.AdelicGaloisOverlapMatchingProof

/-! # Springer's compactness theorem from the split inputs and a Galois twisting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

variable (T : CommGroupScheme (Spec (CommRingCat.of L)))
  (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G) (ν : cocharacterLattice T)

omit [NumberField F] [FiniteDimensional F L] [IsGalois F L] [LocallyOfFiniteType G.X.hom] in
/-- Two-sided bounds `d < |χ(t)| ≤ c` put the inverse of `t` in the simple-root box of any
radius at least `max 1 (max c d⁻¹)`. -/
theorem inv_mem_torusCharacterBox_of_bounds {c d : ℝ≥0ˣ} (t : AdelicGroupPoints L T.toGrp)
    (hup : ∀ β ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T β t ≤ c)
    (hlow : ∀ β ∈ simpleRelativeRoots i ν, d < PositiveRealTorus.normCharacter L T β t) :
    t⁻¹ ∈ torusCharacterBox L T (simpleRelativeRoots i ν)
      (max 1 (max (c : ℝ≥0) ((d⁻¹ : ℝ≥0ˣ) : ℝ≥0))) := by
  intro β hβ
  have hinv : (PositiveRealTorus.normCharacter L T β t⁻¹ : ℝ≥0) =
      ((PositiveRealTorus.normCharacter L T β t : ℝ≥0))⁻¹ := by
    rw [map_inv, Units.val_inv_eq_inv_val]
  rw [hinv]
  have hu0 : (0 : ℝ≥0) < (PositiveRealTorus.normCharacter L T β t : ℝ≥0) :=
    pos_iff_ne_zero.mpr (Units.ne_zero _)
  have huc : (PositiveRealTorus.normCharacter L T β t : ℝ≥0) ≤ (c : ℝ≥0) :=
    Units.val_le_val.mpr (hup β hβ)
  have hdu : (d : ℝ≥0) ≤ (PositiveRealTorus.normCharacter L T β t : ℝ≥0) :=
    Units.val_le_val.mpr (hlow β hβ).le
  have hd0 : (0 : ℝ≥0) < (d : ℝ≥0) := pos_iff_ne_zero.mpr (Units.ne_zero _)
  refine ⟨inv_anti₀ hu0 (huc.trans ((le_max_left _ _).trans (le_max_right _ _))), ?_⟩
  calc ((PositiveRealTorus.normCharacter L T β t : ℝ≥0))⁻¹ ≤ (d : ℝ≥0)⁻¹ :=
        inv_anti₀ hd0 hdu
    _ = ((d⁻¹ : ℝ≥0ˣ) : ℝ≥0) := (Units.val_inv_eq_inv_val d).symm
    _ ≤ _ := (le_max_right _ _).trans (le_max_right _ _)

/-- When a ground-field maximal split torus is central, the inverse-orbit matching
alternative never occurs. Hence the twisted factorization has two-sided simple-root bounds,
which is the bounded-root cover of the scalar-extension image. -/
theorem hasBoundedRootScalarExtensionCover_of_hasTwistedOverlapMatching
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {s : S.toGrp ⟶ G}
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s) (hG : IsConnectedReductive G)
    (hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hM : HasTwistedOverlapMatching F L G T i ν) :
    HasBoundedRootScalarExtensionCover F L G T i ν := by
  obtain ⟨C, hC, c, d, hM⟩ := hM
  refine ⟨max 1 (max (c : ℝ≥0) ((d⁻¹ : ℝ≥0ˣ) : ℝ≥0)), le_max_left _ _, C⁻¹, hC.inv,
    fun g => ?_⟩
  obtain ⟨x, hx, t, p, q, hfac, ht, htc, hmatch⟩ := hM g⁻¹
  have hlow : ∀ α ∈ simpleRelativeRoots i ν,
      d < PositiveRealTorus.normCharacter L T α t := by
    intro α hα
    by_contra hle
    obtain ⟨J, hJ, hJ1, hJm⟩ := hmatch α hα (not_lt.mp hle)
    have h := hs.eq_simpleRelativeRoots_of_inverse_orbit_matching i ν hc hG hGL hi hν J hJ
      ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹) hJm 1
    rw [hJ1] at h
    have hmem : α ∈ simpleRelativeRoots i ν \ {α} := by rw [h]; exact hα
    exact hmem.2 rfl
  refine ⟨rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G) q, ?_⟩
  have hfac' : ((rationalNormOne L _ (rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G) q) *
        scalarExtensionNormOneMap F L G g : normOneSubgroup L _) :
          AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) =
      map L _ _ (Standard.parabolicHom i ν ∅) ((p⁻¹ : normOneSubgroup L _) :
          AdelicGroupPoints L (Standard.parabolicScheme i ν ∅)) *
        map L T.toGrp _ i t⁻¹ * x⁻¹ := by
    rw [map_inv, Subgroup.coe_inv] at hfac
    rw [Subgroup.coe_mul, rationalNormOne_val, inv_eq_iff_eq_inv.mp hfac, Subgroup.coe_inv,
      map_inv, map_inv]
    simp only [rationalSection]
    group
  rw [hfac']
  refine Set.mul_mem_mul (Set.mul_mem_mul ⟨_, (p⁻¹).prop, rfl⟩ ⟨t⁻¹, ⟨?_, ?_⟩, rfl⟩)
    (Set.inv_mem_inv.mpr hx)
  · rw [map_inv]
    exact inv_mem ht
  · exact inv_mem_torusCharacterBox_of_bounds F L G T i ν t htc hlow

end Langlands.Global.AdelicGaloisUnit

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme Langlands.Global.AdelicGaloisUnit

/-- Springer's compactness theorem, conditional on the split fundamental-set theorem, the
split overlap estimate and the Galois twisting of a split Borel pair over a finite Galois
splitting field. -/
theorem centralSplitCompactQuotient_of_splitInputs
    (hF : SplitAdelicFundamentalSetStatement.{u}) (hO : SplitSiegelOverlapStatement.{u})
    (hT : GaloisBorelTwistingStatement.{u}) : CentralSplitCompactQuotientStatement.{u} := by
  intro F _ _ G _ _ hG S s hs hc
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, ν, hν, htw⟩ := hT F G hG
  let : NumberField D.carrier := NumberField.of_module_finite F D.carrier
  have hM := splitGaloisOverlapMatching hF hO F G hG D ν hν htw
  exact D.hasCompactNormOneRationalCover_of_boundedRootCover hG ν hν
    (hasBoundedRootScalarExtensionCover_of_hasTwistedOverlapMatching F D.carrier G D.torus
      D.inclusion ν hs hc hG (D.isConnectedReductive hG)
      (D.isMaximalTorus.isMaximalSplitTorus D.isSplitTorus) hν hM)

end Langlands.Global.AdelicSiegelFactors
