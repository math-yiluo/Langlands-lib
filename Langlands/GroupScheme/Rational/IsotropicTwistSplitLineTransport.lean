import Langlands.GroupScheme.LocalGroupIsoBorelRefinement
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Descent.FppfReflection

/-! # Cocharacters transported across local group identifications -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- A cocharacter of the twist gives a homomorphism into the original group over the cover. -/
def transportedCocharacter (φ : LocalGroupIso G H U) (χ : (Gm S).toGrp ⟶ H) :
    (baseChange U.hom).obj (Gm S).toGrp ⟶ (baseChange U.hom).obj G :=
  (baseChange U.hom).map χ ≫ φ.toBaseChangeIso.inv

/-- Transport preserves closedness of the multiplicative-group inclusion. -/
theorem isClosedSubgroup_transportedCocharacter (φ : LocalGroupIso G H U)
    {χ : (Gm S).toGrp ⟶ H} (hχ : IsClosedSubgroup χ) :
    IsClosedSubgroup (φ.transportedCocharacter χ) :=
  (hχ.baseChange U.hom).comp_iso φ.toBaseChangeIso.symm

/-- The transported homomorphism evaluates by applying the inverse local identification. -/
theorem transportedCocharacter_coverPoints (φ : LocalGroupIso G H U)
    (χ : (Gm S).toGrp ⟶ H) {Z : Over S} (a : Z ⟶ U) (t : Z ⟶ (Gm S).X) :
    coverPointsEquiv G a ((coverPointsEquiv (Gm S).toGrp a).symm t ≫
      (φ.transportedCocharacter χ).hom.hom) = (φ.toFun a).symm (t ≫ χ.hom.hom) := by
  let x := (coverPointsEquiv (Gm S).toGrp a).symm t
  let y := x ≫ ((baseChange U.hom).map χ).hom.hom
  change coverPointsEquiv G a (x ≫ (φ.transportedCocharacter χ).hom.hom) = _
  rw [transportedCocharacter, Grp.comp_hom_hom, ← Category.assoc]
  change coverPointsEquiv G a (y ≫ φ.toBaseChangeIso.inv.hom.hom) = _
  apply (φ.toFun a).injective
  rw [MulEquiv.apply_symm_apply, ← φ.toBaseChangeIso_coverPoints,
    MulEquiv.symm_apply_apply, Category.assoc]
  have h := congrArg (fun f => f.hom.hom) φ.toBaseChangeIso.inv_hom_id
  rw [Grp.comp_hom_hom, Grp.id_hom_hom] at h
  rw [h, Category.comp_id]
  exact (coverPointsEquiv_comp χ a x).trans (by rw [MulEquiv.apply_symm_apply])

/-- On every test scheme the overlap conjugates the two evaluations of the cocharacter. -/
theorem conjugation_transportedCocharacter (φ : LocalGroupIso G H U)
    (χ : (Gm S).toGrp ⟶ H) {ξ : Cocycle G U}
    (hφ : φ.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    {Z : Over S} (a b : Z ⟶ U) (t : Z ⟶ (Gm S).X) :
    let value (c : Z ⟶ U) := coverPointsEquiv G c
      ((coverPointsEquiv (Gm S).toGrp c).symm t ≫ (φ.transportedCocharacter χ).hom.hom)
    ξ.toFun a b * value b * (ξ.toFun a b)⁻¹ = value a := by
  dsimp only
  rw [transportedCocharacter_coverPoints, transportedCocharacter_coverPoints]
  apply (φ.toFun a).injective
  rw [MulEquiv.apply_symm_apply]
  simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id,
    MulEquiv.apply_symm_apply] using hφ a b ((φ.toFun b).symm (t ≫ χ.hom.hom))

/-- A constant section over the cover projects to the pullback along the cover point. -/
private theorem coverPointsEquiv_constantPoint
    (p : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj G).X)
    {Z : Over S} (a : Z ⟶ U) :
    coverPointsEquiv G a (((baseChange U.hom).obj G).constantPoint p (coverTest a)) =
      a ≫ baseChangeBasePointsEquiv U.hom G p := by
  apply Over.OverMorphism.ext
  rw [coverPointsEquiv_left, Over.comp_left, baseChangeBasePointsEquiv_left]
  simp only [constantPoint, Over.comp_left, Over.homMk_left, coverTest, Over.mk_hom]
  exact Category.assoc _ _ _

private theorem transportedCocharacter_coverPoints_of_conjugate
    (φ : LocalGroupIso G H U) (χ : (Gm S).toGrp ⟶ H) (ν : (Gm S).toGrp ⟶ G)
    (p : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj G).X)
    (hp : (baseChange U.hom).map ν ≫ (((baseChange U.hom).obj G).innerIso p).hom =
      φ.transportedCocharacter χ)
    {Z : Over S} (a : Z ⟶ U) (t : Z ⟶ (Gm S).X) :
    let g := baseChangeBasePointsEquiv U.hom G p
    coverPointsEquiv G a ((coverPointsEquiv (Gm S).toGrp a).symm t ≫
      (φ.transportedCocharacter χ).hom.hom) =
      (a ≫ g) * (t ≫ ν.hom.hom) * (a ≫ g)⁻¹ := by
  dsimp only
  rw [← hp, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom,
    map_mul, map_mul, map_inv, coverPointsEquiv_constantPoint, coverPointsEquiv_comp,
    MulEquiv.apply_symm_apply]

/-- A conjugacy of the transported cocharacter to a cocharacter over the base gives a
cochain whose twist of the discrepancy cocycle takes values in the centralizer. -/
theorem twist_mem_torusCentralizer_of_conjugate
    (φ : LocalGroupIso G H U) (χ : (Gm S).toGrp ⟶ H) {ξ : Cocycle G U}
    (hφ : φ.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (ν : (Gm S).toGrp ⟶ G)
    (p : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj G).X)
    (hp : (baseChange U.hom).map ν ≫ (((baseChange U.hom).obj G).innerIso p).hom =
      φ.transportedCocharacter χ)
    {Z : Over S} (a b : Z ⟶ U) :
    (ξ.twist (baseChangeBasePointsEquiv U.hom G p)).toFun a b ∈
      (torusCentralizer ν).carrier Z := by
  rw [mem_torusCentralizer]
  intro V r t
  rw [← (ξ.twist (baseChangeBasePointsEquiv U.hom G p)).naturality r a b]
  let g := baseChangeBasePointsEquiv U.hom G p
  let x := t ≫ ν.hom.hom
  let ga := (r ≫ a) ≫ g
  let gb := (r ≫ b) ≫ g
  let c := ξ.toFun (r ≫ a) (r ≫ b)
  change Commute (ga⁻¹ * c * gb) x
  have h := φ.conjugation_transportedCocharacter χ hφ (r ≫ a) (r ≫ b) t
  dsimp only at h
  simp only [φ.transportedCocharacter_coverPoints_of_conjugate χ ν p hp] at h
  change c * (gb * x * gb⁻¹) * c⁻¹ = ga * x * ga⁻¹ at h
  apply mul_inv_eq_iff_eq_mul.mp
  calc
    (ga⁻¹ * c * gb) * x * (ga⁻¹ * c * gb)⁻¹ =
        ga⁻¹ * (c * (gb * x * gb⁻¹) * c⁻¹) * ga := by group
    _ = x := by rw [h]; group

/-- Closedness of the original split line descends to the conjugate cocharacter
over the base if the cover is surjective and fppf. -/
theorem isClosedSubgroup_of_transportedCocharacter_conjugate
    [Flat U.hom] [LocallyOfFinitePresentation U.hom] [Surjective U.hom]
    (φ : LocalGroupIso G H U) {χ : (Gm S).toGrp ⟶ H} (hχ : IsClosedSubgroup χ)
    (ν : (Gm S).toGrp ⟶ G)
    (p : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj G).X)
    (hp : (baseChange U.hom).map ν ≫ (((baseChange U.hom).obj G).innerIso p).hom =
      φ.transportedCocharacter χ) : IsClosedSubgroup ν := by
  apply IsClosedSubgroup.of_baseChange_of_fppf U.hom
  apply (IsClosedSubgroup.comp_iso_iff _ (((baseChange U.hom).obj G).innerIso p)).mp
  rw [hp]
  exact φ.isClosedSubgroup_transportedCocharacter hχ

end Langlands.GroupScheme.LocalGroupIso
