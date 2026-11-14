import Langlands.Geometry.Building.GenericPointSharpExchange
import Langlands.Geometry.Building.ChamberSimpleParahoricFactorization
import Langlands.Geometry.Building.NormalizerAffineRootAction
import Langlands.Geometry.Building.BuildingFacetPartition

/-! # Chamber exchange with the actual normalizer stabilizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The image in the original rational-point group of the setwise normalizer
stabilizer of an apartment subset. -/
def chamberNormalizer (C : Set D.Apartment) : Subgroup (rationalPoints G) :=
  (MulAction.stabilizer (normalizerPoints i) C).map (normalizerPoints i).subtype

theorem mem_chamberNormalizer {C : Set D.Apartment} {g : rationalPoints G} :
    g ∈ D.chamberNormalizer C ↔
      ∃ n : normalizerPoints i, n • C = C ∧ (n : rationalPoints G) = g := by
  rfl

theorem chamberNormalizer_le_normalizer (C : Set D.Apartment) :
    D.chamberNormalizer C ≤ normalizerPoints i := by
  rintro g ⟨n, _, rfl⟩
  exact n.property

/-- A root-preserving actual normalizer element fixing an interior point preserves
its chamber setwise. -/
theorem normalizer_smul_chamber_eq_of_smul_eq
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C) (n : normalizerPoints i)
    (hn : n • x = x) : n • C = C := by
  have himage : AffineRootSystem.IsChamber D.affineRoots (n • C) :=
    hC.image (D.normalizerAffineEquiv_mem_rootStabilizer n)
  exact himage.isFacet.eq_of_mem_mem hC.isFacet
    (hn ▸ Set.smul_mem_smul_set hx) hx

/-- Generic sharp point exchange yields chamber-simple factorization, retaining
a final factor in the actual setwise normalizer stabilizer. -/
theorem sharpFixer_subset_reflection_mul_wall_mul_chamberNormalizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hext : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots =
      Set.range (rootForm i))
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {alpha : relativeRoots i} (hwall : psi.linear = rootForm i alpha)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    (D.sharpFixer C : Set (rationalPoints G)) ⊆
      (D.sharpFixer (AffineRootSystem.affineReflection psi hv.1 '' C) :
        Set (rationalPoints G)) *
        (D.affineRootGroup alpha psi : Set (rationalPoints G)) *
        (D.chamberNormalizer C : Set (rationalPoints G)) := by
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨nu, hnu, hpos⟩ :=
    RelativeRoot.exists_genericCocharacter_pairing_pos i hT alpha.property.1
  obtain ⟨x, hx⟩ := hpsi.2.2.1.nonempty
  intro g hg
  have hgx : g ∈ D.sharpFixer {x} :=
    D.sharpFixer_anti (Set.singleton_subset_iff.mpr hx) hg
  obtain ⟨ab, ⟨a, ha, b, hb, rfl⟩, n, hn, habn⟩ :=
    D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi x nu hnu hgx
  have haR := D.negativeChamberRootGroups_le_reflection hsys hAS4
    hpsi hwall hpos hx hv ha
  obtain ⟨b', hb', u, hu, hbu⟩ :=
    D.positiveChamberRootGroups_subset_reflection_mul_wall hT
      (hT.finite_relativeRoots i) hsys hext hderiv hAS4 hpsi hwall hpos hx hv hb
  obtain ⟨_, hnN, hnx⟩ := mem_sharpNormalizerStabilizer.mp hn
  have hnC : n ∈ D.chamberNormalizer C :=
    (D.mem_chamberNormalizer).mpr
      ⟨⟨n, hnN⟩,
        D.normalizer_smul_chamber_eq_of_smul_eq hpsi.2.2.1 hx ⟨n, hnN⟩ hnx, rfl⟩
  refine ⟨a * b' * u, ⟨a * b', mul_mem haR hb', u, hu, rfl⟩, n, hnC, ?_⟩
  change b' * u = b at hbu
  change a * b' * u * n = g
  rw [mul_assoc a b' u, hbu]
  exact habn

end Langlands.Geometry.Building.KPApartmentData
