import Langlands.Global.AdelicGoodPositionIwasawaCompactStatement
import Langlands.Global.AdelicStandardLeviCompactAssembly
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicSiegelSetupExistenceProof
import Langlands.Global.InfinitePlaceStandardLeviCompact
import Langlands.Global.FinitePlaceStandardLeviCompact
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicContainsMinimalProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationAmbientTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof
import Langlands.Geometry.Building.GroupAxiomsExistenceReduction
import Langlands.Geometry.Building.RootValuationBuildingConstructionProof
import Langlands.Geometry.Building.RootGroupActionAxiomProof
import Langlands.Geometry.Building.IwahoriDecompositionAxiomProof
import Langlands.Geometry.Building.IntegralModelAxiomsProof

/-! # Proof: maximal compact subgroups in good position with Iwasawa coverage

A parabolic subgroup `P` contains a minimal parabolic, which is the minimal standard parabolic
`P_∅` of a compatible standard family. Local compact subgroups serving `P_∅` and all standard
Levi subgroups exist at every place; at the finite places they come from Bruhat–Tits theory.
The adelic assembly gives one maximal compact `K` with `P_∅(𝔸) K = G(𝔸)`, and `P_∅ ⊆ P` gives
`P(𝔸) K = G(𝔸)` (Mœglin–Waldspurger I.1.4). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G H H' : GroupScheme (Spec (CommRingCat.of F))}

/-- Iwasawa coverage passes from a subgroup to one with a larger all-test image. -/
theorem IsIwasawaCompact.of_range_le {p : H ⟶ G} {p' : H' ⟶ G}
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (h : SubgroupFunctor.range p ≤ SubgroupFunctor.range p') :
    IsIwasawaCompact p' K := by
  have hRange : Set.range (map F H G p) ⊆ Set.range (map F H' G p') := by
    change (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range p) :
      Set (AdelicGroupPoints F G)) ⊆
      (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range p') :
        Set (AdelicGroupPoints F G))
    exact fun x hx => h _ hx
  refine ⟨hK.isCompact, Set.eq_univ_of_univ_subset ?_⟩
  rw [← hK.range_mul]
  exact Set.mul_subset_mul_right hRange

end AdelicGroupPoints

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Every parabolic subgroup contains the minimal standard parabolic `P_∅` of some compatible
standard family, as all-test images. Take a minimal parabolic inside `P`, conjugate the
minimal standard parabolic of the Siegel setup onto it by a rational point `g`, and build the
standard family of the conjugated maximal split torus `Int(g) ∘ i` with the same generic
cocharacter. -/
theorem exists_minimalIndex_range_le (hG : IsConnectedReductive G) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p) :
    ∃ 𝓕 : StandardParabolicFamily F G,
      SubgroupFunctor.range (𝓕.p 𝓕.minimalIndex) ≤ SubgroupFunctor.range p := by
  obtain ⟨Q, q, hq, hle⟩ := parabolicContainsMinimalStatement F G hG P p hp
  obtain ⟨T, i, ν, T₀, j, hS⟩ := AdelicSiegelFactors.siegelAlgebraicSetupExistence.{u} F G hG
  have hi : IsMaximalSplitTorus i := hS.1
  have hν : IsGenericCocharacter i ν := hS.2.1
  have hstd : IsMinimalParabolicSubgroup (Standard.parabolicHom i ν ∅) := hS.2.2.1
  obtain ⟨g, e, he⟩ := minimalParabolicConjugacy.{u} F G hG _ _ _ q hstd hq
  let E := G.innerIso g
  let 𝓕 := StandardParabolicFamily.ofMaximalSplitTorus hG (i ≫ E.hom) (hi.comp_iso E) ν
    ((isGenericCocharacter_comp_ambientIso_iff i ν E).mpr hν)
  refine ⟨𝓕, le_trans (le_of_eq ?_) hle⟩
  rw [(𝓕.isCompatible 𝓕.minimalIndex).parabolic_eq]
  change standardParabolic (i ≫ E.hom) ν ∅ = _
  rw [standardParabolic_comp_ambientIso, ← (Standard.isRepresentedBy_parabolicHom i ν ∅).2,
    ← SubgroupFunctor.range_comp_iso, he, SubgroupFunctor.range_iso_comp]

end StandardParabolicFamily

/-- **Maximal compact subgroups in good position with Iwasawa coverage**
(Mœglin–Waldspurger I.1.4). For a parabolic subgroup `P` of a connected reductive group over a
number field there are a standard parabolic family whose minimal standard parabolic lies in
`P` and a maximal compact subgroup `K` of `G(𝔸)` with `P(𝔸) K = P₀(𝔸) K = G(𝔸)` and maximal
compact inverse images in every standard Levi subgroup. -/
theorem goodPositionIwasawaCompact : GoodPositionIwasawaCompactStatement.{u} := by
  intro F _ _ G P _ _ _ _ p _ hG hp
  obtain ⟨𝓕, h𝓕⟩ := StandardParabolicFamily.exists_minimalIndex_range_le hG p hp
  have hBT : Geometry.Building.BruhatTitsAvailabilityStatement.{u} :=
    Geometry.Building.bruhatTitsAvailabilityReduction
      (Geometry.Building.groupAxiomsExistenceReduction
        Geometry.Building.rootValuationBuildingConstruction
        Geometry.Building.rootGroupActionAxiom
        Geometry.Building.iwahoriDecompositionAxiom
        Geometry.Building.integralModelAxioms)
  have hlocal : ∀ v : Place F,
      ∃ L : Subgroup (PlaceGroupPoints F G v), 𝓕.IsStandardLeviCompact v L := by
    rintro (v | v)
    · exact InfinitePlaceGroupPoints.infinitePlaceStandardLeviCompact F G 𝓕 v
    · exact FinitePlaceGroupPoints.finitePlaceStandardLeviCompactReduction hBT F G 𝓕 v
  obtain ⟨K, hK, hLevi⟩ := 𝓕.standardLeviCompactAssembly hlocal
  have hK₀ : IsIwasawaCompact (𝓕.p 𝓕.minimalIndex) K := hK.isIwasawaCompact
  exact ⟨𝓕, K, hK.1, hK₀.of_range_le h𝓕, hK₀, hLevi⟩

end Langlands.Global
