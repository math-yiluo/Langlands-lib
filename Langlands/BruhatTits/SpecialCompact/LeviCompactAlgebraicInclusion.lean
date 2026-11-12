import Langlands.BruhatTits.SpecialCompact.LeviCompactInclusion
import Langlands.Representation.Plancherel.ParabolicLeviLogarithmBounds
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Levi compact inclusion from root-character triviality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.Plancherel
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)

include hS in
/-- Every actual relative-root subgroup lies in the rational norm kernel:
rational characters are trivial on a dynamic unipotent group containing it. -/
theorem rootGroupPoints_le_rationalCommonNormKernel_of_split
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    rootGroupPoints i a ≤ rationalCommonNormKernel G := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨nu, hnu⟩ := hS.exists_genericCocharacter i
  intro g hg
  apply (mem_rationalCommonNormKernel G g).mpr
  intro chi
  have hchar : rationalCharacterEval chi g = 1 := by
    rcases lt_or_gt_of_ne (hnu a ha) with hneg | hpos
    · apply rationalCharacterEval_eq_one_of_mem_unipotent chi
        (CommGroupScheme.groupHom (-nu) ≫ i)
      apply RelativeRoot.subgroup_le_dynamicUnipotent i (-nu) _ (Over.mk (𝟙 _)) hg
      simpa using neg_pos.mpr hneg
    · exact rationalCharacterEval_eq_one_of_mem_unipotent chi
        (CommGroupScheme.groupHom nu ≫ i)
        (RelativeRoot.subgroup_le_dynamicUnipotent i nu hpos (Over.mk (𝟙 _)) hg)
  rw [hchar, map_one]

variable [Mono i.hom.hom.left]
    (D : KPApartmentData i (localFieldOrder F))

include hS in
/-- The generated sharp fixer is norm one using only actual root-group
containment, with no valuation-topology hypothesis. -/
theorem KPApartmentData.sharpFixer_le_normKernel_of_split (x : D.Apartment) :
    D.sharpFixer {x} ≤ rationalCommonNormKernel G := by
  change (⨆ a : relativeRoots i, D.rootFixer a {x}) ≤ _
  refine iSup_le fun a => ?_
  intro g hg
  exact rootGroupPoints_le_rationalCommonNormKernel_of_split hS i a.property hg.1

end Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (zeta : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j)
    (D : KPApartmentData i (localFieldOrder F))
    (hM : IsConnectedReductive M) (hiM : IsMaximalSplitTorus iM)
    (CM : CentralizerDatum iM) (C : CentralizerDatum i)
    (hD : D.IsOmegaCompatible C)
    (c : CM.Z ⟶ C.Z) (hc : CM.j ≫ j = c ≫ C.j)
    (DM : KPApartmentData iM (localFieldOrder F)) (hDM : DM.IsOmegaCompatible CM)

include hS hcomp hj hjc hM hiM CM C hD c hc hDM in
/-- A supplied compatible Levi restriction has its original norm-one
fixer in the literal ambient preimage, without a separate Levi V7 premise. -/
theorem leviSpecialCompactSubgroup_le_comap_of_compatible
    (x : D.Apartment) (xM : DM.Apartment) (hres : IsLeviRestriction j x xM) :
    DM.specialCompactSubgroup xM ≤
      (D.specialCompactSubgroup x).comap (rationalPoints.map j) := by
  intro m hm
  obtain ⟨hmnorm, hmfix⟩ := (KPApartmentData.mem_specialCompactSubgroup DM).mp hm
  obtain ⟨n, hnfix, p, hp, hmp⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff DM.sharpFixerFamily xM m).mp hmfix
  have hpNorm := DM.sharpFixer_le_normKernel_of_split hS iM xM hp
  have hnNorm : (n : rationalPoints M) ∈ rationalCommonNormKernel M := by
    have hmem := (rationalCommonNormKernel M).mul_mem
      ((rationalCommonNormKernel M).inv_mem hpNorm) hmnorm
    rwa [hmp, inv_mul_cancel_left] at hmem
  have hpn := sharpFixer_le_of_isLeviRestriction hS i iM j hcomp zeta hj hjc D DM x xM hres hp
  have hnGfix := normalizer_smul_eq_of_isLeviRestriction (i := i) (iM := iM)
    (hS := hS) (j := j) (hcomp := hcomp) (ζ := zeta) (hj := hj) (hjc := hjc)
    (D := D) (hM := hM) (hiM := hiM) (CM := CM) (C := C) (hO := hD) (c := c) (hc := hc)
    DM hDM x xM hres n hnNorm hnfix
  apply (KPApartmentData.mem_specialCompactSubgroup D).mpr
  refine ⟨map_mem_rationalCommonNormKernel j hmnorm, ?_⟩
  rw [hmp, map_mul, mul_smul]
  change rationalPoints.map j p •
    (normalizerPointsMap iM j i hcomp n : rationalPoints G) • D.apartmentMap x =
      D.apartmentMap x
  rw [← D.apartmentMap_smul, hnGfix]
  exact D.sharpFixer_le_reducedFixer x hpn

/-- The actual Levi inclusion restricts to the two original norm-one
fixers on a compatible restriction pair. -/
def leviSpecialCompactInclusionOfCompatible
    (x : D.Apartment) (xM : DM.Apartment) (hres : IsLeviRestriction j x xM) :
    DM.specialCompactSubgroup xM →* D.specialCompactSubgroup x where
  toFun m := ⟨rationalPoints.map j m,
    leviSpecialCompactSubgroup_le_comap_of_compatible
      (hS := hS) (i := i) (iM := iM) (j := j) (hcomp := hcomp) (zeta := zeta)
      (hj := hj) (hjc := hjc) (D := D) (hM := hM) (hiM := hiM)
      (CM := CM) (C := C) (hD := hD) (c := c) (hc := hc)
      (DM := DM) (hDM := hDM) x xM hres m.property⟩
  map_one' := Subtype.ext (rationalPoints.map j).map_one
  map_mul' m n := Subtype.ext ((rationalPoints.map j).map_mul
    (m : rationalPoints M) (n : rationalPoints M))

end Langlands.BruhatTits.SpecialCompact
