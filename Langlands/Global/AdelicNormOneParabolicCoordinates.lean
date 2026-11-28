import Langlands.Global.AdelicAdjunctionIwasawaMeasure
import Langlands.Global.AdelicIwasawaCompatibleMeasureProof
import Langlands.Global.AdelicParabolicNormOneIwasawaMeasure
import Langlands.Global.AdelicRelativeLeviHaar
import Langlands.Global.LeftCosetSemidirectHaarDensity
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet

/-! # Radical and Levi coordinates of the ambient norm-one parabolic -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure

open Langlands.GroupScheme Langlands.Global.PositiveRealTorus
  Langlands.Global.EisensteinConstantTerm
open Langlands.Global.LeftCosetSpace (fundamentalDomain measurableSet_fundamentalDomain)

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] (l : M ⟶ P)

local notation "Pₐ" => AdelicGroupPoints F P
local notation "Mₐ" => AdelicGroupPoints F M
local notation "H" => ambientNormOneLevi p
local notation "L" => ambientNormOneLevi (l ≫ p)
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p))
local notation "Q" => ambientNormOneParabolicImage p

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left] in
/-- The actual ambient norm-one parabolic, expressed either on parabolic points or as an
image in the ambient group. -/
def normOneParabolicImageEquiv : H ≃ₜ* Q := by
  let f : H →* Q :=
    { toFun := fun x => ⟨⟨map F P G p x.val, x.2⟩, ⟨x.val, rfl⟩⟩
      map_one' := Subtype.ext (Subtype.ext (map_one (map F P G p)))
      map_mul' x y := Subtype.ext (Subtype.ext (map_mul (map F P G p) x.val y.val)) }
  have hf : IsEmbedding f :=
    IsEmbedding.subtypeVal.of_comp_iff.mp <|
      IsEmbedding.subtypeVal.of_comp_iff.mp
        ((isClosedEmbedding_map F P G p).isEmbedding.comp IsEmbedding.subtypeVal)
  have hs : Function.Surjective f := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    change map F P G p y = x at hy
    have hy' : y ∈ H := by
      change map F P G p y ∈ normOneSubgroup F G
      rwa [hy]
    exact ⟨⟨y, hy'⟩, Subtype.ext (Subtype.ext hy)⟩
  let e := MulEquiv.ofBijective f ⟨hf.injective, hs⟩
  exact
    { toMulEquiv := e
      continuous_toFun := hf.continuous
      continuous_invFun := hf.isInducing.continuous_iff.mpr (by
        change Continuous (e ∘ e.symm)
        rw [show e ∘ e.symm = (id : Q → Q) from funext e.apply_symm_apply]
        exact continuous_id) }

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType P.X.hom] in
@[simp] theorem normOneParabolicImageEquiv_apply (q : H) :
    (normOneParabolicImageEquiv p q).val.val = map F P G p q.val := rfl

variable [IsIso (subgroupMultiplication l iU)]
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)

include hU in
private theorem radical_mem_normOneParabolic (u : N) : radicalInclusion p iU u ∈ H := by
  change (map F P G p).toMonoidHom (radicalInclusion p iU u) ∈ normOneSubgroup F G
  rw [map_radicalInclusion]
  rcases u.2 with ⟨v, hv⟩
  change AdelicGroupPoints F U at v
  change map F U G (iU ≫ p) v = u.val at hv
  rw [← hv, ← characterLog_eq_zero_iff, characterLog_map,
    characterLog_eq_zero_of_isUnipotent hU.1.isUnipotent, map_zero]

/-- The radical inclusion in the ambient norm-one parabolic. -/
def normOneRadicalInclusion : N →* H :=
  (radicalInclusion p iU).codRestrict _ (radical_mem_normOneParabolic p iU hU)

/-- The Levi section in the ambient norm-one parabolic. -/
def normOneLeviSection : L →* H :=
  ((map F M P l).toMonoidHom.comp (L).subtype).codRestrict _ fun m => by
    change map F P G p (map F M P l m.val) ∈ normOneSubgroup F G
    rw [← map_comp_apply_of_hom]
    exact m.2

set_option quotPrecheck false in
local notation "retraction" => leviRetraction l iU hU.1.isNormal
local notation "fullCoordinates" => coordinates p iU l hU

private theorem projected_mem_normOneLevi (q : H) :
    map F P M retraction q.val ∈ L := by
  let x := (fullCoordinates).symm q.val
  have hq : fullCoordinates x = q.val := (fullCoordinates).apply_symm_apply _
  have hx : map F P M retraction q.val = x.2 := by
    rw [← hq]
    exact proj_coordinates p iU l hU x
  have hprod : radicalInclusion p iU x.1 * map F M P l x.2 ∈ H := by
    change fullCoordinates x ∈ H
    rw [hq]
    exact q.2
  have hm := ((H).mul_mem_cancel_left (radical_mem_normOneParabolic p iU hU x.1)).mp hprod
  change map F M G (l ≫ p) (map F P M retraction q.val) ∈ normOneSubgroup F G
  rw [hx, map_comp_apply_of_hom]
  exact hm

/-- The norm-one Levi projection induced by the actual parabolic retraction. -/
def normOneLeviProjection : H →* L :=
  ((map F P M retraction).toMonoidHom.comp (H).subtype).codRestrict _
    (projected_mem_normOneLevi p iU l hU)

local notation "radIncl" => normOneRadicalInclusion p iU hU
local notation "leviSect" => normOneLeviSection p l
local notation "leviProj" => normOneLeviProjection p iU l hU

private theorem project_section (m : L) : leviProj (leviSect m) = m := by
  apply Subtype.ext
  change map F P M retraction (map F M P l m.val) = m.val
  rw [← map_comp_apply_of_hom, levi_comp_leviRetraction]
  rfl

private theorem project_eq_one_iff (q : H) : leviProj q = 1 ↔ ∃ n : N, radIncl n = q := by
  constructor
  · intro hq
    let x := (fullCoordinates).symm q.val
    have hx : fullCoordinates x = q.val := (fullCoordinates).apply_symm_apply _
    have hm : x.2 = 1 := by
      have hv : map F P M retraction q.val = 1 := congrArg Subtype.val hq
      have hpj : map F P M retraction (fullCoordinates x) = x.2 :=
        proj_coordinates p iU l hU x
      exact hpj.symm.trans ((congrArg (map F P M retraction) hx).trans hv)
    refine ⟨x.1, Subtype.ext ?_⟩
    rw [coordinates_apply, hm, map_one, mul_one] at hx
    exact hx
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    change map F P M retraction (radicalInclusion p iU u) = 1
    have h : map F P M retraction (fullCoordinates (u, 1)) = 1 :=
      proj_coordinates p iU l hU (u, 1)
    simpa only [coordinates_apply, map_one, mul_one] using h

private theorem project_radical (u : N) : leviProj (radIncl u) = 1 :=
  (project_eq_one_iff p iU l hU _).mpr ⟨u, rfl⟩

private theorem isEmbedding_normOneRadicalInclusion : IsEmbedding radIncl :=
  IsEmbedding.subtypeVal.of_comp_iff.mp (isEmbedding_radicalInclusion p iU)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsClosedImmersion p.hom.hom.left]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
private theorem continuous_normOneLeviSection : Continuous leviSect :=
  ((map F M P l).continuous.comp continuous_subtype_val).subtype_mk _

private theorem continuous_normOneLeviProjection : Continuous leviProj :=
  ((map F P M retraction).continuous.comp continuous_subtype_val).subtype_mk _

open Langlands.Global.LeftCosetSpace.Semidirect in
/-- Radical-first multiplication in the actual ambient norm-one parabolic. -/
def normOneParabolicCoordinates : N × L ≃ₜ H :=
  prodHomeomorph radIncl leviSect leviProj (project_section p iU l hU)
    (fun q hq => (project_eq_one_iff p iU l hU q).mp hq) (project_radical p iU l hU)
    (isEmbedding_normOneRadicalInclusion p iU hU)
    (continuous_normOneLeviSection p l) (continuous_normOneLeviProjection p iU l hU)

@[simp] theorem normOneParabolicCoordinates_apply (x : N × L) :
    (normOneParabolicCoordinates p iU l hU x).val =
      radicalInclusion p iU x.1 * map F M P l x.2.val := rfl

private local instance : LocallyCompactSpace N :=
  (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)).locallyCompactSpace

open Langlands.Global.LeftCosetSpace.Semidirect in
/-- The inverse of the modulus of the Levi action on the radical. -/
def normOneParabolicDensity : L → ℝ≥0∞ :=
  inverseConjugationModulus radIncl leviSect leviProj (project_section p iU l hU)
    (fun q hq => (project_eq_one_iff p iU l hU q).mp hq) (project_radical p iU l hU)
    (isEmbedding_normOneRadicalInclusion p iU hU) (continuous_normOneLeviSection p l)

open Langlands.Global.LeftCosetSpace.Semidirect in
/-- For a dynamic parabolic the density is the published negative modulus parameter
evaluated on the actual Levi point. -/
theorem normOneParabolicDensity_eq_inverseModulus
    (hG : IsConnectedReductive G)
    {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hN : (Dynamic.unipotent χ).IsRepresentedBy (iU ≫ p)) (m : L) :
    normOneParabolicDensity p iU l hU m = ENNReal.ofReal (inverseModulus l m.val) := by
  let c := conj radIncl leviSect leviProj (project_section p iU l hU)
    (fun q hq => (project_eq_one_iff p iU l hU q).mp hq) (project_radical p iU l hU)
    (isEmbedding_normOneRadicalInclusion p iU hU) (continuous_normOneLeviSection p l) m
  have hc : mulEquivHaarChar c = (parabolicModulus F hP hN (map F M P l m.val) : ℝ≥0) := by
    rw [parabolicModulus_apply]
    apply Aubert.General.CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter
      (map F U G (iU ≫ p)).toMonoidHom.range
      (isClosed_range_map_unipotent F hN) _ (ContinuousMulEquiv.refl N)
    intro n
    have h := congrArg ((map F P G p).toMonoidHom.comp (H).subtype)
      (i_conj radIncl leviSect leviProj (project_section p iU l hU)
        (fun q hq => (project_eq_one_iff p iU l hU q).mp hq) (project_radical p iU l hU)
        (isEmbedding_normOneRadicalInclusion p iU hU) (continuous_normOneLeviSection p l) m n)
    change (map F P G p).toMonoidHom (radicalInclusion p iU (c n)) =
      (map F P G p).toMonoidHom ((map F M P l m.val) * radicalInclusion p iU n *
        (map F M P l m.val)⁻¹) at h
    change (c n).val = (map F P G p).toMonoidHom (map F M P l m.val) * n.val *
      ((map F P G p).toMonoidHom (map F M P l m.val))⁻¹
    simpa only [map_mul, map_inv, map_radicalInclusion] using h
  have hmod := IwasawaCompatibleMeasure.parabolicModulus_eq_characterNorm
    adelicParabolicModulus hG hP hN (map F M P l m.val)
  have hd := ofReal_inverseModulus l m.val
  rw [IwasawaCompatibleMeasure.parameterPower_neg_modulusParameter] at hd
  have hval : inverseModulus l m.val =
      (((characterNorm F P (Lie.adjointDeterminantCharacter P).toMul
        (map F M P l m.val) : ℝ≥0) : ℝ))⁻¹ := by
    apply Complex.ofReal_injective
    rwa [Complex.ofReal_inv]
  change (((mulEquivHaarChar c)⁻¹ : ℝ≥0) : ℝ≥0∞) = _
  rw [hc, hmod, hval, ← NNReal.coe_inv]
  simp only [ENNReal.ofReal_coe_nnreal]

open Langlands.Global.LeftCosetSpace.Semidirect in
/-- The radical Haar factor may be held fixed when normalizing the Levi measure. -/
theorem exists_normOneParabolicHaarProduct (dn : Measure N) [dn.IsHaarMeasure]
    (dp : Measure H) [dp.IsHaarMeasure] :
    ∃ dm : Measure L, dm.IsHaarMeasure ∧
      MeasurePreserving (normOneParabolicCoordinates p iU l hU)
        (dn.prod (dm.withDensity (normOneParabolicDensity p iU l hU))) dp := by
  let E := normOneParabolicCoordinates p iU l hU
  let d := normOneParabolicDensity p iU l hU
  let dm₀ : Measure L := Measure.haar
  let dp₀ := Measure.map E (dn.prod (dm₀.withDensity d))
  let : dp₀.IsHaarMeasure :=
    isHaarMeasure_map_weightedProduct radIncl leviSect leviProj (project_section p iU l hU)
      (fun q hq => (project_eq_one_iff p iU l hU q).mp hq) (project_radical p iU l hU)
      (isEmbedding_normOneRadicalInclusion p iU hU) (continuous_normOneLeviSection p l)
      (continuous_normOneLeviProjection p iU l hU) dn dm₀
  let c := dp.haarScalarFactor dp₀
  have hc : 0 < c := haarScalarFactor_pos_of_isHaarMeasure dp dp₀
  refine ⟨c • dm₀, IsHaarMeasure.nnreal_smul _ hc.ne', E.continuous.measurable, ?_⟩
  change Measure.map E (dn.prod ((c • dm₀).withDensity d)) = dp
  rw [← Measure.coe_nnreal_smul, withDensity_smul_measure, Measure.prod_smul_right,
    Measure.map_smul _ E.continuous.measurable.aemeasurable]
  exact (isMulLeftInvariant_eq_smul dp dp₀).symm

section Principal

local notation "ΓP" => relativeLeviRationalSubgroup p
local notation "ΓM" => relativeLeviRationalSubgroup (l ≫ p)
local notation "ΓN" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p))

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem mem_relativePrincipal_iff {S : GroupScheme (Spec (CommRingCat.of F))}
    (f : S ⟶ G) (q : ambientNormOneLevi f) :
    q ∈ relativeLeviRationalSubgroup f ↔ q.val ∈ rationalSubgroup F S := by
  constructor
  · rintro ⟨x, ⟨d, hd⟩, hx⟩
    exact ⟨d, (congrArg Subtype.val hd).trans (congrArg Subtype.val hx)⟩
  · rintro ⟨d, hd⟩
    exact ⟨rationalNormOne F S d, ⟨d, rfl⟩, Subtype.ext hd⟩

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsClosedImmersion p.hom.hom.left]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
private theorem section_mem_principal (m : L) (hm : m ∈ ΓM) : leviSect m ∈ ΓP := by
  rw [mem_relativePrincipal_iff] at hm ⊢
  obtain ⟨d, hd⟩ := hm
  change map F M P l m.val ∈ rationalSubgroup F P
  rw [← hd, map_rational]
  exact ⟨_, rfl⟩

private theorem projection_mem_principal (q : H) (hq : q ∈ ΓP) : leviProj q ∈ ΓM := by
  rw [mem_relativePrincipal_iff] at hq ⊢
  exact proj_mem_rationalSubgroup iU l hU hq

include hU in
/-- The lattice kernel in radical-first coordinates is the actual principal radical. -/
theorem normOneRadical_comap_principal : (ΓP).comap radIncl = ΓN := by
  ext u
  rw [Subgroup.mem_comap, mem_relativePrincipal_iff, mem_rationalSubgroup_range_iff]
  change radicalInclusion p iU u ∈ rationalSubgroup F P ↔ u.val ∈ rationalImage F (iU ≫ p)
  constructor
  · rintro ⟨q, hq⟩
    have hr : u.val ∈ rationalSubgroup F G := by
      refine ⟨P.affinePointsTarget p (CommAlgCat.of F F) q, ?_⟩
      rw [← map_rational p q, hq]
      exact map_radicalInclusion p iU u
    obtain ⟨d, hd⟩ := hr
    have hmem : rational F G d ∈ (N : Set (AdelicGroupPoints F G)) := hd ▸ u.property
    obtain ⟨v, hv⟩ := (rational_mem_adelicPoints_range_iff
      (inferInstance : IsClosedImmersion (iU ≫ p).hom.hom.left) d).mp hmem
    exact ⟨v, (map_rational (iU ≫ p) (show RationalGroupPoints F U from v)).trans
      ((congrArg (rational F G) hv).trans hd)⟩
  · rintro ⟨v, hv⟩
    change RationalGroupPoints F U at v
    refine ⟨U.affinePointsTarget iU (CommAlgCat.of F F) v,
      (isClosedEmbedding_map F P G p).injective ?_⟩
    rw [← map_rational iU v, ← map_comp_apply_of_hom]
    exact hv.trans (map_radicalInclusion p iU u).symm

open Langlands.Global.LeftCosetSpace.Semidirect in
/-- A radical-first product of strict fundamental domains is a strict fundamental
domain for the actual principal parabolic lattice. -/
theorem normOneParabolicFundamentalDomain (dp : Measure H) :
    IsFundamentalDomain ΓP
      (normOneParabolicCoordinates p iU l hU ''
        (fundamentalDomain ΓN
          (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p))) ×ˢ
        fundamentalDomain ΓM (isDiscrete_relativeLeviRationalSubgroup (l ≫ p)))) dp := by
  let E := normOneParabolicCoordinates p iU l hU
  let hN := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p))
  let hM := isDiscrete_relativeLeviRationalSubgroup (l ≫ p)
  have hD := (measurableSet_fundamentalDomain ΓN hN).prod (measurableSet_fundamentalDomain ΓM hM)
  refine IsFundamentalDomain.mk'
    (E.toMeasurableEquiv.measurableEmbedding.measurableSet_image' hD).nullMeasurableSet ?_
  intro x
  let h' : IsDiscrete ((ΓP).comap radIncl : Set N) :=
    (normOneRadical_comap_principal p iU hU).symm ▸ hN
  have h := productFundamentalDomain_unique radIncl leviSect leviProj
    (project_section p iU l hU) (fun q hq => (project_eq_one_iff p iU l hU q).mp hq)
    (project_radical p iU l hU) (isEmbedding_normOneRadicalInclusion p iU hU)
    (continuous_normOneLeviSection p l) (continuous_normOneLeviProjection p iU l hU)
    ΓP ΓM hM (section_mem_principal p l) (projection_mem_principal p iU l hU) h' x
  have heq : fundamentalDomain ((ΓP).comap radIncl) h' = fundamentalDomain ΓN hN := by
    congr 1
    exact normOneRadical_comap_principal p iU hU
  change ∃! g' : ΓP, g'.val * x ∈ E '' (fundamentalDomain ΓN hN ×ˢ fundamentalDomain ΓM hM)
  simpa only [heq, E, normOneParabolicCoordinates] using h

end Principal

end Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure
