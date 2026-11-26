import Langlands.GroupScheme.Rational.BorelInducedNonvanishingStatement
import Langlands.GroupScheme.Rational.SplitHighestWeightClassificationProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Reductive.CovariantSocle
import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Proof: nonvanishing of the spaces `E(λ)` of Borel-equivariant functions -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- For a cocharacter negative on every simple root, a root pairs nonnegatively with it
exactly when the root is not positive. -/
theorem nonneg_latticePairing_root_iff_not_isPos {ν : cocharacterLattice p.torus}
    (hν : ∀ a : p.base.support, latticePairing p.torus (p.rootDatum.root a) ν < 0)
    (j : p.rootIndex) :
    0 ≤ latticePairing p.torus (p.rootDatum.root j) ν ↔ ¬ p.base.IsPos j := by
  classical
  obtain ⟨f, hfs, hf, he⟩ := p.base.exists_root_eq_sum_int j
  have hpair : latticePairing p.torus (p.rootDatum.root j) ν =
      ∑ a ∈ p.base.support, f a * latticePairing p.torus (p.rootDatum.root a) ν := by
    rw [he, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  have hheight := RootPairing.Base.height_eq_sum he
  rcases hf with hf | hf
  · obtain ⟨hle, b, hb⟩ := Pi.lt_def.mp hf
    have hle' : ∀ a, 0 ≤ f a := fun a => hle a
    have hb' : 0 < f b := hb
    have hbs : b ∈ p.base.support := hfs (Function.mem_support.mpr hb'.ne')
    have hneg : latticePairing p.torus (p.rootDatum.root j) ν < 0 := by
      rw [hpair, ← neg_pos, ← Finset.sum_neg_distrib]
      refine Finset.sum_pos' (fun a ha => ?_) ⟨b, hbs, ?_⟩
      · have h1 := hν ⟨a, ha⟩
        have h2 := hle' a
        nlinarith
      · have h1 := hν ⟨b, hbs⟩
        nlinarith
    have hpos : p.base.IsPos j := by
      rw [RootPairing.Base.isPos_iff, hheight]
      exact Finset.sum_pos' (fun a _ => hle' a) ⟨b, hbs, hb'⟩
    exact ⟨fun h => absurd h (not_le.mpr hneg), fun h => absurd hpos h⟩
  · obtain ⟨hle, b, hb⟩ := Pi.lt_def.mp hf
    have hle' : ∀ a, f a ≤ 0 := fun a => hle a
    have hb' : f b < 0 := hb
    have hbs : b ∈ p.base.support := hfs (Function.mem_support.mpr hb'.ne)
    have hposp : 0 < latticePairing p.torus (p.rootDatum.root j) ν := by
      rw [hpair]
      refine Finset.sum_pos' (fun a ha => ?_) ⟨b, hbs, ?_⟩
      · have h1 := hν ⟨a, ha⟩
        have h2 := hle' a
        nlinarith
      · have h1 := hν ⟨b, hbs⟩
        nlinarith
    have hnpos : ¬ p.base.IsPos j := by
      rw [RootPairing.Base.isPos_iff, hheight, not_lt, ← neg_nonneg, ← Finset.sum_neg_distrib]
      exact Finset.sum_nonneg fun a _ => neg_nonneg.mpr (hle' a)
    exact ⟨fun _ => hnpos, fun _ => hposp.le⟩

/-- Every cocharacter negative on the simple roots has the same dynamic parabolic as the
reverse of the chosen positive cocharacter: both are the negative Borel subgroup. -/
theorem parabolic_eq_of_neg_simpleRoots {ν : cocharacterLattice p.torus}
    (hν : ∀ a : p.base.support, latticePairing p.torus (p.rootDatum.root a) ν < 0) :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ p.inclusion) =
      Dynamic.parabolic (Dynamic.oppositeCocharacter p.positiveGm) := by
  have hν' : ∀ a : p.base.support,
      latticePairing p.torus (p.rootDatum.root a) (-p.positiveCocharacter) < 0 := by
    intro a
    have h := (p.latticePairing_root_positiveCocharacter_pos_iff a).mpr
      (RootPairing.Base.isPos_of_mem_support a.2)
    rw [map_neg]
    exact neg_neg_of_pos h
  have hsign : ∀ α ∈ relativeRoots p.inclusion,
      (0 ≤ latticePairing p.torus α ν ↔
        0 ≤ latticePairing p.torus α (-p.positiveCocharacter)) := by
    intro α hα
    obtain ⟨j, rfl⟩ : ∃ j, p.rootDatum.root j = α := by
      rw [← Set.mem_range, p.isRootDatum.2.1]
      exact hα
    rw [p.nonneg_latticePairing_root_iff_not_isPos hν j,
      p.nonneg_latticePairing_root_iff_not_isPos hν' j]
  have hmax := p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus
  rw [positiveGm, ← groupHom_neg_comp_eq_oppositeCocharacter]
  exact le_antisymm
    ((relativeRootSignInclusions k G p.isConnectedReductive p.torus p.inclusion hmax ν _).1.2
      fun α hα => (hsign α hα).1)
    ((relativeRootSignInclusions k G p.isConnectedReductive p.torus p.inclusion hmax _ ν).1.2
      fun α hα => (hsign α hα).2)

end SplitPinning

namespace HomogeneousQuotientFromEmbedding

open AffineCoordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance borelInducedNonvanishingInstG : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance borelInducedNonvanishingInstH : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom

/-- A function is right covariant for `χ` exactly when its composite with inversion has
left-covariant coordinate for `-χ`. No homogeneous quotient is involved. -/
theorem isRightCharacterCovariant_iff_coordinate (i : H ⟶ G) (χ : rationalCharacters H)
    (f : Γ(G.X.left, ⊤)) :
    IsRightCharacterCovariant i χ f ↔
      coordinateEquiv G f ∈ leftCovariantSubspace i (characterCoordinate H (-χ)) := by
  have key : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
      (pointAlgebraHom G T ((h ≫ i.hom.hom) * g) (coordinateEquiv G f) =
        pointAlgebraHom H T h (characterCoordinate H (-χ)) *
          pointAlgebraHom G T g (coordinateEquiv G f)) ↔
      ((g⁻¹ * (h⁻¹ ≫ i.hom.hom)).left.appTop f =
        (characterEval χ T h⁻¹).1 * (g⁻¹).left.appTop f) := by
    intro T h g
    rw [pointAlgebraHom_coordinateEquiv, pointAlgebraHom_coordinateEquiv,
      pointAlgebraHom_characterCoordinate, characterEval_neg, ← map_inv, mul_inv_rev,
      GrpObj.inv_comp]
  rw [mem_leftCovariantSubspace_iff_points]
  constructor
  · intro hf T h g
    exact (key T h g).mpr (hf T g⁻¹ h⁻¹)
  · intro hf T a b
    have e := (key T b⁻¹ a⁻¹).mp (hf T b⁻¹ a⁻¹)
    rwa [inv_inv, inv_inv] at e

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- Right covariance is unchanged when the subgroup is replaced by an isomorphic one with
the same inclusion and the transported character. -/
theorem isRightCharacterCovariant_iso_iff {H' : GroupScheme (Spec (CommRingCat.of k))}
    (e : H' ≅ H) (i : H ⟶ G) (χ : rationalCharacters H) (f : Γ(G.X.left, ⊤)) :
    IsRightCharacterCovariant (e.hom ≫ i) (characterRestrict e.hom χ) f ↔
      IsRightCharacterCovariant i χ f := by
  constructor
  · intro hf T a b
    have h := hf T a (b ≫ e.inv.hom.hom)
    have hb : (b ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = b := by
      rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
    rwa [characterEval_characterRestrict, hb, Grp.comp_hom_hom, ← Category.assoc, hb] at h
  · intro hf T a b
    rw [characterEval_characterRestrict, Grp.comp_hom_hom, ← Category.assoc]
    exact hf T a (b ≫ e.hom.hom.hom)

end HomogeneousQuotientFromEmbedding

open AffineCoordinates HomogeneousQuotientFromEmbedding Chevalley

/-- Milne, Proposition 22.27(a), in the 2022 corrected reprint: the space `E(λ)` of
functions on `G` that are right covariant for the opposite Borel subgroup is nonzero
exactly when `λ` is dominant. -/
theorem splitBorelInducedNonvanishing : SplitBorelInducedNonvanishingStatement.{u} := by
  intro k _ G _ p ν hν B' i hi hrep t ht χ
  let := isAffine_of_isAffineHom G.X.hom
  have hrep' :
      (Dynamic.parabolic (Dynamic.oppositeCocharacter p.positiveGm)).IsRepresentedBy i := by
    rwa [← p.parabolic_eq_of_neg_simpleRoots hν]
  let e := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    p.isRepresentedBy_negativeBorelHom hrep'
  have he : e.hom ≫ i = p.negativeBorelHom :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _
  have het : p.torusToNegativeBorel ≫ e.hom = t := by
    apply SubgroupFunctor.IsRepresentedBy.hom_ext hrep
    rw [Category.assoc, he, p.torusToNegativeBorel_comp, ht]
  set lam := rationalCharacters.equivCharacterLattice p.torus (characterRestrict t χ)
  have hχ : characterRestrict e.hom χ = p.borelCharacter lam := by
    rw [p.eq_borelCharacter (characterRestrict e.hom χ), ← AddMonoidHom.comp_apply,
      ← characterRestrict_comp, het]
  -- The covariance condition in coordinates, for the negative Borel subgroup.
  have hkey : ∀ f : Γ(G.X.left, ⊤),
      IsRightCharacterCovariant i (-χ) f ↔
        coordinateEquiv G f ∈
          leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam) := by
    intro f
    rw [← isRightCharacterCovariant_iso_iff e i (-χ) f, he,
      isRightCharacterCovariant_iff_coordinate, map_neg, neg_neg, hχ]
    rfl
  constructor
  · rintro ⟨f, hf0, hf⟩
    have hF := (hkey f).mp hf
    set F := coordinateEquiv G f with hFdef
    have hF0 : F ≠ 0 := by
      intro h0
      apply hf0
      have h1 := congrArg (coordinateEquiv G).symm h0
      rwa [hFdef, AlgEquiv.symm_apply_apply, map_zero] at h1
    let V := affineCovariantSocle G F
    have hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam) :=
      affineCovariantSocle_le_leftCovariantSubspace G p.negativeBorelHom _ hF
    have hV0 : V ≠ ⊥ := by
      intro hbot
      apply hF0
      have hm := mem_affineCovariantSocle G F
      rwa [show affineCovariantSocle G F = ⊥ from hbot, Submodule.mem_bot] at hm
    let b := Module.finBasis k V
    obtain ⟨v, hvfix, hv1, -⟩ :=
      affineRegularRepresentation_exists_normalized_fixedVector G V b
        (rightAct_mem_affineCovariantSocle G F) p.negativeBorelHom p.positiveUnipotentHom
        p.isUnipotent_positiveUnipotent _ hcov hV0 p.cellCoordinate_mem_nonZeroDivisors
        p.exists_factors_of_isUnit_cellCoordinate
    have hreal : p.IsRealizedBy lam (affineRegularCoordinateMap G V b v) :=
      ⟨hcov (affineRegularCoordinateMap_mem G V b v),
        affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector G V b
          (rightAct_mem_affineCovariantSocle G F) p.positiveUnipotentHom hvfix, hv1⟩
    exact hreal.isHighestWeight_affineCovariantSocleRepresentation.isDominantWeight
  · intro hdom
    obtain ⟨F, hF⟩ := p.isRealizedWeight_of_isDominantWeight' lam hdom
    refine ⟨(coordinateEquiv G).symm F, ?_, ?_⟩
    · intro h0
      have h1 := congrArg (coordinateEquiv G) h0
      rw [AlgEquiv.apply_symm_apply, map_zero] at h1
      have h2 := hF.2.2
      rw [h1, map_zero] at h2
      exact zero_ne_one h2
    · rw [hkey, AlgEquiv.apply_symm_apply]
      exact hF.1

end Langlands.GroupScheme
