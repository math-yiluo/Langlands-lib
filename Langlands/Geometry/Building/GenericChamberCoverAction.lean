import Langlands.Geometry.Building.GenericChamberRankOneCover
import Langlands.Geometry.Building.AffineSimpleAdmissibility

/-! # Left multiplication preserving the sharp chamber normalizer cover -/

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

/-- Rational points whose left multiplication and inverse left multiplication
preserve the sharp chamber normalizer cover. -/
def sharpChamberCoverStabilizer (C : Set D.Apartment) :
    Subgroup (rationalPoints G) where
  carrier := {h | (∀ g ∈ D.sharpChamberNormalizerCover C,
      h * g ∈ D.sharpChamberNormalizerCover C) ∧
    (∀ g ∈ D.sharpChamberNormalizerCover C,
      h⁻¹ * g ∈ D.sharpChamberNormalizerCover C)}
  one_mem' := by constructor <;> intro g hg <;> simpa using hg
  mul_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    constructor
    · intro g hg
      simpa only [mul_assoc] using ha (b * g) (hb g hg)
    · intro g hg
      simpa only [mul_inv_rev, mul_assoc] using hbi (a⁻¹ * g) (hai g hg)
  inv_mem' := by
    rintro a ⟨ha, hai⟩
    exact ⟨hai, by simpa only [inv_inv] using ha⟩

theorem sharpFixer_le_sharpChamberCoverStabilizer (C : Set D.Apartment) :
    D.sharpFixer C ≤ D.sharpChamberCoverStabilizer C := by
  intro p hp
  exact ⟨fun _ hg => D.mul_mem_sharpChamberNormalizerCover_of_mem_sharpFixer hp hg,
    fun _ hg => D.mul_mem_sharpChamberNormalizerCover_of_mem_sharpFixer (inv_mem hp) hg⟩

theorem normalizer_mul_mem_cover_of_stabilizes_chamber
    {C : Set D.Apartment} (n : normalizerPoints i) (hn : n • C = C)
    {g : rationalPoints G} (hg : g ∈ D.sharpChamberNormalizerCover C) :
    (n : rationalPoints G) * g ∈ D.sharpChamberNormalizerCover C := by
  obtain ⟨p, hp, m, q, hq, rfl⟩ := hg
  have hp' := D.sharpFixer_le_comap n C hp
  change (n : rationalPoints G) * p * (n : rationalPoints G)⁻¹ ∈
    D.sharpFixer (n • C) at hp'
  rw [hn] at hp'
  refine ⟨(n : rationalPoints G) * p * (n : rationalPoints G)⁻¹, hp',
    n * m, q, hq, ?_⟩
  simp only [Subgroup.coe_mul]
  group

theorem chamberNormalizer_le_sharpChamberCoverStabilizer (C : Set D.Apartment) :
    D.chamberNormalizer C ≤ D.sharpChamberCoverStabilizer C := by
  rintro g ⟨n, hn, rfl⟩
  have hni : n⁻¹ • C = C := by
    have h := congrArg (fun E : Set D.Apartment => n⁻¹ • E) hn
    simpa only [inv_smul_smul] using h.symm
  exact ⟨fun _ hg => D.normalizer_mul_mem_cover_of_stabilizes_chamber n hn hg,
    fun _ hg => by simpa only [Subgroup.coe_inv, Subgroup.subtype_apply] using
      D.normalizer_mul_mem_cover_of_stabilizes_chamber n⁻¹ hni hg⟩

/-- Chamber exchange and the rank-one identity make a simple reflection lift
preserve the cover under left multiplication. -/
theorem reflection_mul_mem_sharpChamberNormalizerCover
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hext : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots =
      Set.range (rootForm i))
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {a : relativeRoots i} (hwall : psi.linear = rootForm i a)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v)
    (r : normalizerPoints i)
    (hr : D.normalizerAffineEquiv r = AffineRootSystem.affineReflection psi hv.1)
    (hra : weylAction i r a = -(a : characterLattice S))
    {g : rationalPoints G} (hg : g ∈ D.sharpChamberNormalizerCover C) :
    (r : rationalPoints G) * g ∈ D.sharpChamberNormalizerCover C := by
  obtain ⟨p, hp, m, q, hq, rfl⟩ := hg
  obtain ⟨pu, ⟨p', hp', u, hu, hpu⟩, c, hc, hpuc⟩ :=
    D.sharpFixer_subset_reflection_mul_wall_mul_chamberNormalizer
      hG hi hsys hext hderiv hAS4 hpsi hwall hv hp
  obtain ⟨cN, _, hcN⟩ := D.mem_chamberNormalizer.mp hc
  have hrC : r • (AffineRootSystem.affineReflection psi hv.1 '' C) = C := by
    change (D.normalizerAffineEquiv r : D.Apartment → D.Apartment) ''
      (AffineRootSystem.affineReflection psi hv.1 '' C) = C
    rw [hr, Set.image_image]
    have hinv : (fun x => AffineRootSystem.affineReflection psi hv.1
        (AffineRootSystem.affineReflection psi hv.1 x)) = id :=
      funext (AffineRootSystem.affineReflection_involutive psi hv.1)
    rw [hinv]
    exact Set.image_id C
  have hleft := D.sharpFixer_le_comap r
    (AffineRootSystem.affineReflection psi hv.1 '' C) hp'
  change (r : rationalPoints G) * p' * (r : rationalPoints G)⁻¹ ∈
    D.sharpFixer (r • (AffineRootSystem.affineReflection psi hv.1 '' C)) at hleft
  rw [hrC] at hleft
  have hmid := D.reflection_wall_mul_normalizer_mem_cover hG hi hAS4
    hpsi hwall hv r hr hra hu (cN * m)
  have H := D.mul_mem_sharpChamberNormalizerCover_of_mem_sharpFixer_right
    (D.mul_mem_sharpChamberNormalizerCover_of_mem_sharpFixer hleft hmid) hq
  change p' * u = pu at hpu
  change pu * c = p at hpuc
  rw [← hpuc, ← hpu, ← hcN]
  convert H using 1
  simp only [Subgroup.coe_mul]
  group

/-- A simple lift and its inverse preserve the cover. Its square stabilizes the
chamber, so inverse preservation follows without identifying the apartment kernel. -/
theorem reflection_mem_sharpChamberCoverStabilizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hext : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots =
      Set.range (rootForm i))
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {a : relativeRoots i} (hwall : psi.linear = rootForm i a)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v)
    (r : normalizerPoints i)
    (hr : D.normalizerAffineEquiv r = AffineRootSystem.affineReflection psi hv.1)
    (hra : weylAction i r a = -(a : characterLattice S)) :
    (r : rationalPoints G) ∈ D.sharpChamberCoverStabilizer C := by
  have hf : ∀ g ∈ D.sharpChamberNormalizerCover C,
      (r : rationalPoints G) * g ∈ D.sharpChamberNormalizerCover C :=
    fun _ hg => D.reflection_mul_mem_sharpChamberNormalizerCover
      hG hi hsys hext hderiv hAS4 hpsi hwall hv r hr hra hg
  have hsqC : (r * r) • C = C := by
    change (D.normalizerAffineEquiv (r * r) : D.Apartment → D.Apartment) '' C = C
    rw [map_mul, hr, AffineRootSystem.affineReflection_mul_self]
    exact Set.image_id C
  have hsq : (r : rationalPoints G) * (r : rationalPoints G) ∈
      D.sharpChamberCoverStabilizer C :=
    D.chamberNormalizer_le_sharpChamberCoverStabilizer C
      ((D.mem_chamberNormalizer).mpr ⟨r * r, hsqC, rfl⟩)
  refine ⟨hf, ?_⟩
  intro g hg
  have H := hsq.2 ((r : rationalPoints G) * g) (hf g hg)
  convert H using 1
  group

/-- If every chamber-simple reflection has a cover-preserving actual lift,
then every actual normalizer point preserves the cover. -/
theorem normalizer_le_sharpChamberCoverStabilizer_of_simple_lifts
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hlift : ∀ s ∈ AffineRootSystem.chamberSimpleReflections D.affineRoots C,
      ∃ r : normalizerPoints i,
        (r : rationalPoints G) ∈ D.sharpChamberCoverStabilizer C ∧
        D.normalizerAffineEquiv r = (s : D.Apartment ≃ᵃ[ℝ] D.Apartment)) :
    normalizerPoints i ≤ D.sharpChamberCoverStabilizer C := by
  let HN := (D.sharpChamberCoverStabilizer C).comap (normalizerPoints i).subtype
  let HW := (HN.map D.normalizerAffineEquiv).comap
    (AffineRootSystem.affineWeylGroup D.affineRoots).subtype
  have hgen : Subgroup.closure
      (AffineRootSystem.chamberSimpleReflections D.affineRoots C) ≤ HW := by
    apply (Subgroup.closure_le _).mpr
    intro s hs
    obtain ⟨r, hr, hrs⟩ := hlift s hs
    exact ⟨r, hr, hrs⟩
  rw [hsys.closure_chamberSimpleReflections hC] at hgen
  intro n hn
  let nN : normalizerPoints i := ⟨n, hn⟩
  have hCn : AffineRootSystem.IsChamber D.affineRoots (nN • C) :=
    hC.image (D.normalizerAffineEquiv_mem_rootStabilizer nN)
  obtain ⟨w, hw, -⟩ := Langlands.Geometry.Building.affineChamberSimpleTransitivity
    (TranslationSpace i) D.Apartment D.affineRoots hsys C (nN • C) hC hCn
  obtain ⟨m, hm, hmw⟩ := hgen (Subgroup.mem_top w)
  have hmC : m • C = nN • C := by
    change (D.normalizerAffineEquiv m : D.Apartment → D.Apartment) '' C = _
    rw [hmw]
    exact hw
  have hkC : (m⁻¹ * nN) • C = C := by
    rw [mul_smul, ← hmC, inv_smul_smul]
  have hk := D.chamberNormalizer_le_sharpChamberCoverStabilizer C
    ((D.mem_chamberNormalizer).mpr ⟨m⁻¹ * nN, hkC, rfl⟩)
  have H := (D.sharpChamberCoverStabilizer C).mul_mem hm hk
  change (m : rationalPoints G) * ((m : rationalPoints G)⁻¹ * n) ∈ _ at H
  simpa only [mul_inv_cancel_left] using H

end Langlands.Geometry.Building.KPApartmentData
