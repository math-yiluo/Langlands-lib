import Langlands.Global.AdelicLocalFinitenessBoundaryModelConstruction
import Langlands.Global.AdelicLocalFinitenessSiegelRepresentatives
import Langlands.Global.AdelicLocalFinitenessChamberCoordinates
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicCompatibleIwasawaCompact
import Langlands.Global.AdelicSiegelChamberReduction
import Langlands.Global.AdelicSiegelChamberReductionProof
import Langlands.Global.AdelicSpringerCentralCompactnessProof
import Langlands.Global.InfinitePlaceLeviIwasawaProof
import Langlands.Global.IntegralIwasawaFamilyProof
import Langlands.Global.FinitePlaceIwasawaProof
import Langlands.Global.AdelicPositiveTorusSplitComponentProof

/-! # Local finiteness of `Ξ_main` in the Fréchet spaces `𝔉^R_L`

The compact boundary model of `AdelicLocalFinitenessBoundaryReduction` exists for every base point
(`uniformGrowthLocalFinitenessBoundaryModel`), and hence `UniformGrowthLocalFinitenessStatement`
holds (`uniformGrowthLocalFiniteness`, Bernstein–Lapid, Theorem 7.2).
-/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

open scoped Classical in
/-- **The compact boundary model exists.** For the standard parabolic family of the maximal split
torus and generic cocharacter, an Iwasawa subgroup of the minimal parabolic which is maximal
compact, its Siegel cover, the chamber coordinates of the group data and the rational Siegel
representatives supply the hypotheses of `StandardParabolicFamily.exists_boundaryModel`. -/
theorem uniformGrowthLocalFinitenessBoundaryModel :
    UniformGrowthLocalFinitenessBoundaryModelStatement.{u, u, u} := by
  intro F _ _ G T _ _ _ iT ν hG hT hν Ua hUa uMap huMap t r z hz N d rho hN hrho hsmooth hcalc
    n W X hX L hLo hLc s₀
  let 𝓕 := StandardParabolicFamily.ofMaximalSplitTorus hG iT hT ν hν
  have : ∀ α : simpleRelativeRoots 𝓕.i 𝓕.ν, IsAffine (Ua α).X.left := hUa
  have : ∀ α : simpleRelativeRoots 𝓕.i 𝓕.ν, IsClosedImmersion (uMap α).hom.hom.left := huMap
  have : Finite (simpleRelativeRoots 𝓕.i 𝓕.ν) := 𝓕.finite_simpleRoots.to_subtype
  have : Fintype (simpleRelativeRoots 𝓕.i 𝓕.ν) := Fintype.ofFinite _
  have : IsClosedImmersion (Standard.parabolicHom iT ν ∅).hom.hom.left :=
    Standard.isClosedSubgroup_parabolicHom iT ν ∅
  have : IsAffine (Standard.parabolicScheme iT ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.parabolicHom iT ν ∅).hom.hom.left
  -- the rational characters of `P₀` are free of finite rank
  let J₀ : StandardIndex F G 𝓕.i 𝓕.ν := ⟨∅, empty_subset _⟩
  let rP : ParabolicRootPresentation (𝓕.p J₀) (𝓕.l J₀) (𝓕.a J₀) :=
    ⟨⟨𝓕.T, 𝓕.i, 𝓕.ν, J₀.val, 𝓕.f J₀⟩, 𝓕.isCompatible J₀⟩
  have hfree := @ParabolicRootPresentation.rationalCharacters_free_finite _ _ _ _ _ _ _ _ _ _ rP
    hG (𝓕.affineP J₀)
  have : Module.Free ℤ (rationalCharacters (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅)) := hfree.1
  have : Module.Finite ℤ (rationalCharacters (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅)) := hfree.2
  -- the Siegel setup, a maximal compact Iwasawa subgroup and its Siegel cover
  obtain ⟨T₀, j, hS⟩ := exists_siegelAlgebraicSetup_of_generic F iT ν hG hT hν
  obtain ⟨K, hKpar, -⟩ := adelicCompatibleIwasawaCompactStatement_of_local
    InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement
    FinitePlaceGroupPoints.parabolicIwasawaStatement IntegralIwasawaFamily.existenceStatement
    F G hG T iT ν T₀ j hS
  obtain ⟨C, t₀, hCK, hcover⟩ := exists_isSiegelCover_of_chamber centralSplitCompactQuotient
    adelicSiegelChamberReduction F G hG T iT ν T₀ j hS K hKpar
  subst hCK
  have hK : IsIwasawaCompact (Standard.parabolicHom iT ν ∅) C.compactSubgroup :=
    hKpar.isIwasawaCompact
  -- the chamber coordinates of the group data
  obtain ⟨dT, e, hd, hRoot, hCen, hstep, hez⟩ :=
    adelicLocalFinitenessChamberCoordinates F iT ν hG hT hν uMap t z hz
  -- the rational Siegel representatives
  obtain ⟨Lsec, hLsec, hLroot⟩ := exists_rootTrivialSection iT (simpleRelativeRoots iT ν) z
    (fun k β hβ => hz.2.2.2.2.2.2.1 k ⟨β, hβ⟩) hz.2.2.2.2.2.2.2.1 hz.2.2.2.2.2.2.2.2
  obtain ⟨Ω, M, r', hΩ, hM, hr', hrep⟩ := exists_siegelRepresentatives rho hN hrho hG hS C t₀
    hcover hK Lsec hLsec hLroot (𝓕.commute_of_rootTrivial positiveTorusSplitComponent)
  let step : simpleRelativeRoots iT ν → ℝ := fun α => localFinitenessRootStep iT ν t α
  let θ : simpleRelativeRoots iT ν → ℝ := fun α => Real.log ((t₀ : NNReal) : ℝ) / step α
  have hY : ∀ x : AdelicGroupPoints F G, ∃ q : RationalGroupPoints F G,
      AdelicGroupPoints.finite F G (rational F G q * x) ∈ Ω ∧
      (∀ α, θ α ≤ (e (hK.height (rational F G q * x))).1 α) ∧
      RepresentationGrowth.adelicHeight F G rho (rational F G q * x) ≤
        M * RepresentationGrowth.adelicHeight F G rho x ^ r' := by
    intro x
    obtain ⟨q, hqΩ, hqht, h, hqH, hqθ⟩ := hrep x
    refine ⟨q, hqΩ, fun α => ?_, hqht⟩
    rw [hqH, ← hd h, hRoot h α]
    exact div_le_div_of_nonneg_right (hqθ α.val α.property) (hstep α).1.le
  exact 𝓕.exists_boundaryModel hK e positiveTorusSplitComponent hz j hsmooth rho hcalc hN hrho dT
    step hS hd (fun α => (hstep α).1) hRoot (fun h hh => (hCen h).mp hh) (fun α => (hstep α).2)
    hez θ Ω hΩ M r' hM hr' hY X hX L hLo hLc s₀

/-- **Local finiteness of `Ξ_main`** (Bernstein–Lapid, Theorem 7.2): the published
`UniformGrowthLocalFinitenessStatement`. -/
theorem uniformGrowthLocalFiniteness : UniformGrowthLocalFinitenessStatement.{u} :=
  uniformGrowthLocalFiniteness_of_boundaryModel uniformGrowthLocalFinitenessBoundaryModel

end Langlands.Global
