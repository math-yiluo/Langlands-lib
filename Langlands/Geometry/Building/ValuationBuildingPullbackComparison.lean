import Langlands.Geometry.Building.ValuationBuildingQuotientMap
import Langlands.Geometry.Building.DerivedAffineRoots
import Langlands.Geometry.Building.CentralIsogenyAffineRoots
import Langlands.Geometry.Building.AffineRootSystemTransport

/-!
# Apartment comparisons for the derived and central-isogeny pullbacks

The derived valuation pullback `KPApartmentData.derivedPullback` through a derived inclusion
`d : D → G`, and the central-isogeny pullback `KPApartmentData.centralIsogenyPullback` through a
central isogeny `q : C → G`, are apartment comparisons (`KPApartmentData.Comparison`) along the
induced maps of rational points: the inverse point pullback intertwines the normalizer actions,
the image of each sharp fixer `D(k)^♯_x` (resp. `C(k)^♯_x`) is the corresponding sharp fixer of
`G(k)`, and the affine roots correspond.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

section Derived

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hA : IsSplitTorus A.toGrp)
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (hi : IsMaximalSplitTorus i) {ω : kˣ → ℝ} (P : KPApartmentData i ω)

/-- The image under `d` of a filtration subgroup of the derived pullback is the corresponding
filtration subgroup of `G(k)`. -/
theorem map_filtration_derivedPullback (y : P.Apartment) (a : relativeRoots i) (r : ℝ) :
    ((P.derivedPullback e c j i d hd h hT hS hA hc hi).filtration
        (P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi y) (e ≫ a.val) r).map
        (rationalPoints.map d) = P.filtration y a.val r := by
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ((P.mem_filtration_derivedPullback_iff e c j i d hd h hT hS hA hc hi y a r u).mp hu).2
  · intro hg
    obtain ⟨u, hu⟩ := (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).surjective
      ⟨g, P.filtration_le_rootGroupPoints y a.val r hg⟩
    have hu' : rationalPoints.map d u.val = g := congrArg Subtype.val hu
    refine ⟨u.val, ?_, hu'⟩
    exact (P.mem_filtration_derivedPullback_iff e c j i d hd h hT hS hA hc hi y a r u.val).mpr
      ⟨u.property, by rw [hu']; exact hg⟩

/-- The image under `d` of a sharp fixer of the derived pullback is the corresponding sharp
fixer of `G(k)`. -/
theorem map_sharpFixer_derivedPullback (y : P.Apartment) :
    ((P.derivedPullback e c j i d hd h hT hS hA hc hi).sharpFixer
        {P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi y}).map (rationalPoints.map d) =
      P.sharpFixer {y} := by
  rw [sharpFixer, sharpFixer, Subgroup.map_iSup]
  refine ((RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).iSup_comp
    (g := fun α : relativeRoots j =>
      ((P.derivedPullback e c j i d hd h hT hS hA hc hi).rootFixer α
        {P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi y}).map
          (rationalPoints.map d))).symm.trans (iSup_congr fun a => ?_)
  rw [rootFixer_singleton, rootFixer_singleton]
  exact P.map_filtration_derivedPullback e c j i d hd h hT hS hA hc hi y a 0

/-- The derived pullback is an apartment comparison along `d`. -/
def derivedComparison :
    Comparison (P.derivedPullback e c j i d hd h hT hS hA hc hi) P (rationalPoints.map d) where
  e := (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi).symm
  map_mem_normalizerPoints n :=
    (DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n).2
  e_smul n x := by
    obtain ⟨y, rfl⟩ := (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi).surjective x
    apply (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi).injective
    rw [AffineEquiv.apply_symm_apply, AffineEquiv.symm_apply_apply]
    exact (P.derivedApartmentEquiv_smul e c j i d hd h hT hS hA hc hi n y).symm
  map_sharpFixer x := by
    obtain ⟨y, rfl⟩ := (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi).surjective x
    rw [AffineEquiv.symm_apply_apply]
    exact P.map_sharpFixer_derivedPullback e c j i d hd h hT hS hA hc hi y
  transportedRoots_eq := by
    rw [← P.transportedRoots_derivedPullback e c j i d hd h hT hS hA hc hi,
      AffineRootSystem.transportedRoots_symm]

theorem derivedComparison_e_symm_apply (y : P.Apartment) :
    (P.derivedComparison e c j i d hd h hT hS hA hc hi).e.symm y =
      P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi y :=
  rfl

end Derived

section CentralIsogeny

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  (q : C ⟶ G) (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))
  {ω : kˣ → ℝ} (D : KPApartmentData j ω)

/-- The image under `q` of a filtration subgroup of the central-isogeny pullback is the
corresponding filtration subgroup of `G(k)`. -/
theorem map_filtration_centralIsogenyPullback (y : D.Apartment) (a : relativeRoots j) (r : ℝ) :
    ((D.centralIsogenyPullback q hq hS hT t h ht).filtration
        (D.centralIsogenyApartmentEquiv q hq hS hT t h ht y) (t ≫ a.val) r).map
        (rationalPoints.map q) = D.filtration y a.val r := by
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ((D.mem_filtration_centralIsogenyPullback_iff q hq hS hT t h ht y a r u).mp hu).2
  · intro hg
    obtain ⟨u, hu⟩ := (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a).surjective
      ⟨g, D.filtration_le_rootGroupPoints y a.val r hg⟩
    have hu' : rationalPoints.map q u.val = g := congrArg Subtype.val hu
    refine ⟨u.val, ?_, hu'⟩
    exact (D.mem_filtration_centralIsogenyPullback_iff q hq hS hT t h ht y a r u.val).mpr
      ⟨u.property, by rw [hu']; exact hg⟩

/-- The image under `q` of a sharp fixer of the central-isogeny pullback is the corresponding
sharp fixer of `G(k)`. -/
theorem map_sharpFixer_centralIsogenyPullback (y : D.Apartment) :
    ((D.centralIsogenyPullback q hq hS hT t h ht).sharpFixer
        {D.centralIsogenyApartmentEquiv q hq hS hT t h ht y}).map (rationalPoints.map q) =
      D.sharpFixer {y} := by
  rw [sharpFixer, sharpFixer, Subgroup.map_iSup]
  refine ((centralIsogenyRootPullbackEquiv q hq hS hT t h ht).iSup_comp
    (g := fun α : relativeRoots i =>
      ((D.centralIsogenyPullback q hq hS hT t h ht).rootFixer α
        {D.centralIsogenyApartmentEquiv q hq hS hT t h ht y}).map
          (rationalPoints.map q))).symm.trans (iSup_congr fun a => ?_)
  rw [rootFixer_singleton, rootFixer_singleton]
  exact D.map_filtration_centralIsogenyPullback q hq hS hT t h ht y a 0

/-- The central-isogeny pullback is an apartment comparison along `q`. -/
def centralIsogenyComparison :
    Comparison (D.centralIsogenyPullback q hq hS hT t h ht) D (rationalPoints.map q) where
  e := (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht).symm
  map_mem_normalizerPoints n := (splitTorusIsogenyNormalizerMap q hS hT t h ht n).2
  e_smul n x := by
    obtain ⟨y, rfl⟩ := (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht).surjective x
    apply (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht).injective
    rw [AffineEquiv.apply_symm_apply, AffineEquiv.symm_apply_apply]
    exact (D.centralIsogenyApartmentEquiv_smul q hq hS hT t h ht n y).symm
  map_sharpFixer x := by
    obtain ⟨y, rfl⟩ := (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht).surjective x
    rw [AffineEquiv.symm_apply_apply]
    exact D.map_sharpFixer_centralIsogenyPullback q hq hS hT t h ht y
  transportedRoots_eq := by
    rw [← D.transportedRoots_centralIsogenyPullback q hq hS hT t h ht,
      AffineRootSystem.transportedRoots_symm]

theorem centralIsogenyComparison_e_symm_apply (y : D.Apartment) :
    (D.centralIsogenyComparison q hq hS hT t h ht).e.symm y =
      D.centralIsogenyApartmentEquiv q hq hS hT t h ht y :=
  rfl

end CentralIsogeny

end Langlands.Geometry.Building.KPApartmentData
