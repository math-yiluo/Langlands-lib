import Langlands.Global.AdelicWeilPositiveQuotient
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure
import Langlands.GroupScheme.Rational.AffineWeilParabolicRadicalTransportProof
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction

/-! # The proper parabolic radical families under adelic Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj ENNReal TensorProduct

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints AdelicWeilRestriction Langlands.GroupScheme
open AffineWeilParabolicRadicalTransport

private theorem geometricRadical_of_radical {F : Type u} [Field F]
    {G P U : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    {p : P ⟶ G} {r : U ⟶ P} (hp : IsParabolicSubgroup p) (hr : IsUnipotentRadical r) :
    LeviSubgroup.IsGeometricUnipotentRadical r := by
  obtain ⟨χ, hχ⟩ := exists_isRepresentedBy_parabolic hG hp
  exact isGeometricUnipotentRadical_of_isRepresentedBy hG χ hχ
    (isRepresentedBy_unipotent_of_isUnipotentRadical hG χ hχ hr)

section FullRange

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  {P G : GroupScheme (Spec (CommRingCat.of L))}
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- Full all-test range of a closed subgroup is preserved and reflected by Weil restriction. -/
private theorem range_weil_eq_top_iff (p : P ⟶ G) (hp : IsClosedSubgroup p) :
    SubgroupFunctor.range (AffineWeil.map K L p) = ⊤ ↔ SubgroupFunctor.range p = ⊤ := by
  refine ⟨?_, ?_⟩
  · intro h
    let : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
    have hsurj (C : CommAlgCat (CommRingCat.of L)) (y : G.affinePoints C) :
        ∃ x, P.affinePointsTarget p C x = y := by
      obtain ⟨y', hy'⟩ := AffineWeil.exists_affinePointMap_multiplication_eq K G C y
      let D := (AffineWeil.restrictScalars K L).obj C
      let eqG := AffineWeil.pointsEquiv K L G D
      have hy : eqG.symm y' ∈ (SubgroupFunctor.range (AffineWeil.map K L p)).carrier
          ((algSpec _).obj (Opposite.op D)) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hy
      let x' := AffineWeil.pointsEquiv K L P D x
      have hmap : P.affinePointsTarget p ((AffineWeil.tensorFunctor K L).obj D) x' = y' := by
        change P.affinePointsTarget p (CommAlgCat.of L (L ⊗[K] D))
          (AffineWeil.pointsEquiv K L P D x) = y'
        rw [← AffineWeil.map_affinePoints K L p]
        change eqG (x ≫ (AffineWeil.map K L p).hom.hom) = y'
        rw [hx, MulEquiv.apply_symm_apply]
      have hnat := DFunLike.congr_fun
        (P.affinePointsTarget_naturality p (AffineWeil.multiplication K C)) x'
      exact ⟨P.affinePointMap (AffineWeil.multiplication K C) x',
        hnat.symm.trans ((congrArg (G.affinePointMap (AffineWeil.multiplication K C)) hmap).trans
          hy')⟩
    let a := AffineCoordinates.groupSchemeIso G
    let C := AffineCoordinates.algebra G
    obtain ⟨x, hx⟩ := hsurj C a.hom.hom.hom
    have hsection : a.inv.hom.hom ≫ (x ≫ p.hom.hom) = 𝟙 G.X := by
      change x ≫ p.hom.hom = a.hom.hom.hom at hx
      rw [hx, ← Grp.comp_hom_hom, a.inv_hom_id, Grp.id_hom_hom]
    apply SubgroupFunctor.ext
    intro Z
    apply Subgroup.ext
    intro y
    refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
    apply SubgroupFunctor.mem_range.mpr
    exact ⟨y ≫ a.inv.hom.hom ≫ x, by rw [Category.assoc, Category.assoc, hsection,
      Category.comp_id]⟩
  · intro h
    let : IsClosedImmersion p.hom.hom.left := hp
    let : IsIso p := isIso_of_full_range p (Over.mono_of_mono_left _) h
    let a := AffineWeil.mapIso K L (asIso p)
    change SubgroupFunctor.range a.hom = ⊤
    exact full_range_of_isIso a.hom

end FullRange

section Comparison

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of L))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {W : GroupScheme (Spec (CommRingCat.of K))}
  (w : W ≅ AffineWeil.groupScheme K L G)
  {U : GroupScheme (Spec (CommRingCat.of L))} [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
  {V : GroupScheme (Spec (CommRingCat.of K))}
  (v : V ≅ AffineWeil.groupScheme K L U)
  {q : V ⟶ W} {p : U ⟶ G}

set_option backward.isDefEq.respectTransparency false in
private theorem ambientEquiv_map_of_square (h : q ≫ w.hom = v.hom ≫ AffineWeil.map K L p)
    (x : AdelicGroupPoints K V) :
    ambientEquiv K L w (AdelicGroupPoints.map K V W q x) =
      AdelicGroupPoints.map L U G p (ambientEquiv K L v x) := by
  rw [ambientEquiv_apply, ← map_comp_apply_of_hom, h, map_comp_apply_of_hom,
    adelicPointsEquiv_map, ambientEquiv_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem principalEquiv_map_of_square (h : q ≫ w.hom = v.hom ≫ AffineWeil.map K L p)
    (x : RationalGroupPoints K V) :
    principalEquiv K L w (V.affinePointsTarget q (CommAlgCat.of K K) x) =
      U.affinePointsTarget p (CommAlgCat.of L L) (principalEquiv K L v x) := by
  apply (rational_injective L G)
  have hK := DFunLike.congr_fun (rational_naturality K V q) x
  have hL := DFunLike.congr_fun (rational_naturality L U p) (principalEquiv K L v x)
  change rational K W (V.affinePointsTarget q (CommAlgCat.of K K) x) =
    AdelicGroupPoints.map K V W q (rational K V x) at hK
  change rational L G (U.affinePointsTarget p (CommAlgCat.of L L) (principalEquiv K L v x)) =
    AdelicGroupPoints.map L U G p (rational L U (principalEquiv K L v x)) at hL
  rw [← ambientEquiv_rational, hK, hL, ambientEquiv_map_of_square K L w v h, ambientEquiv_rational]

/-- Two subgroup functors have corresponding full adelic and principal points. -/
def WeilSubgroupsMatch (D : SubgroupFunctor W) (E : SubgroupFunctor G) : Prop :=
  (∀ x, ambientEquiv K L w x ∈ AdelicSubgroupPoints.adelicPoints L G E ↔
    x ∈ AdelicSubgroupPoints.adelicPoints K W D) ∧
  (∀ x, principalEquiv K L w x ∈ AdelicSubgroupPoints.rationalPoints L G E ↔
    x ∈ AdelicSubgroupPoints.rationalPoints K W D)

set_option backward.isDefEq.respectTransparency false in
private theorem weilSubgroupsMatch_range_of_square
    (h : q ≫ w.hom = v.hom ≫ AffineWeil.map K L p) :
    WeilSubgroupsMatch K L w (SubgroupFunctor.range q) (SubgroupFunctor.range p) := by
  constructor
  · intro x
    change (∃ y : AdelicGroupPoints L U, AdelicGroupPoints.map L U G p y = ambientEquiv K L w x) ↔
      ∃ y : AdelicGroupPoints K V, AdelicGroupPoints.map K V W q y = x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (ambientEquiv K L v).surjective y
      exact ⟨y, (ambientEquiv K L w).injective
        ((ambientEquiv_map_of_square K L w v h y).trans hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨ambientEquiv K L v y, (ambientEquiv_map_of_square K L w v h y).symm⟩
  · intro x
    change (∃ y : RationalGroupPoints L U,
        U.affinePointsTarget p (CommAlgCat.of L L) y = principalEquiv K L w x) ↔
      ∃ y : RationalGroupPoints K V, V.affinePointsTarget q (CommAlgCat.of K K) y = x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (principalEquiv K L v).surjective y
      exact ⟨y, (principalEquiv K L w).injective
        ((principalEquiv_map_of_square K L w v h y).trans hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨principalEquiv K L v y, (principalEquiv_map_of_square K L w v h y).symm⟩

end Comparison

section Parabolics

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  {G : GroupScheme (Spec (CommRingCat.of L))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {W : GroupScheme (Spec (CommRingCat.of K))}
  (w : W ≅ AffineWeil.groupScheme K L G)
  (hPD : ParabolicDynamicStatement.{u}) (hW : IsConnectedReductive W) (hG : IsConnectedReductive G)

private theorem range_comp_iso_eq_top_iff {F : Type u} [Field F]
    {H A B : GroupScheme (Spec (CommRingCat.of F))} (l : H ⟶ A) (a : A ≅ B) :
    SubgroupFunctor.range (l ≫ a.hom) = ⊤ ↔ SubgroupFunctor.range l = ⊤ := by
  have ha : SubgroupFunctor.range ((𝟙 A) ≫ a.hom) = ⊤ := full_range_of_isIso _
  rw [← ha, SubgroupFunctor.range_comp_iso_eq_iff, SubgroupFunctor.range_id]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Every lower-field proper parabolic radical has a matching upper-field one. -/
theorem exists_upper_parabolicRadical (Q : ProperRationalParabolic W) :
    ∃ P : ProperRationalParabolic G, WeilSubgroupsMatch K L w
      (properRationalParabolicRadicals hPD hW Q) (properRationalParabolicRadicals hPD hG P) := by
  obtain ⟨P₀, U₀, p, r, hp, hpQ, hr, hrad⟩ := rationalParabolicRadical_spec hPD hW Q.val
  let hWG : IsConnectedReductive (AffineWeil.groupScheme K L G) :=
    AffineWeil.isConnectedReductive_restriction K L G hG
  have hpw := hp.comp_iso w
  obtain ⟨P', U', aP, lP, aU, lU, p', r', hp', hr', eP, eU, heP, heU⟩ :=
    (affineWeilParabolicRadicalTransport K L G hG).2 P₀ U₀ (p ≫ w.hom) r hpw
      (geometricRadical_of_radical hWG hpw hr)
  let : IsAffine P'.X.left := aP
  let : LocallyOfFiniteType P'.X.hom := lP
  let : IsAffine U'.X.left := aU
  let : LocallyOfFiniteType U'.X.hom := lU
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom P'.X.hom := hp'.isClosedSubgroup.isAffineHom
  have hproper : SubgroupFunctor.range p' ≠ ⊤ := by
    intro h
    have h' := (range_weil_eq_top_iff K L p' hp'.isClosedSubgroup).mpr h
    apply Q.property
    rw [← hpQ, ← range_comp_iso_eq_top_iff p w, ← heP, SubgroupFunctor.range_iso_comp]
    exact h'
  let P : ProperRationalParabolic G := ⟨⟨_, ⟨P', p', hp', rfl⟩⟩, hproper⟩
  have hrad' : properRationalParabolicRadicals hPD hG P = SubgroupFunctor.range (r' ≫ p') :=
    properRationalParabolicRadicals_eq hPD hG hp' hproper hr'.1
  refine ⟨P, ?_⟩
  change WeilSubgroupsMatch K L w (rationalParabolicRadical hPD hW Q.val) _
  rw [← hrad, hrad']
  apply weilSubgroupsMatch_range_of_square K L w eU
  simp only [AffineWeil.map_comp, Category.assoc, reassoc_of% heU, heP]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Every upper-field proper parabolic radical has a matching lower-field one. -/
theorem exists_lower_parabolicRadical (P : ProperRationalParabolic G) :
    ∃ Q : ProperRationalParabolic W, WeilSubgroupsMatch K L w
      (properRationalParabolicRadicals hPD hW Q) (properRationalParabolicRadicals hPD hG P) := by
  obtain ⟨P', U', p, r, hp, hpP, hr, hrad⟩ := rationalParabolicRadical_spec hPD hG P.val
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom P'.X.hom := hp.isClosedSubgroup.isAffineHom
  let : IsAffineHom U'.X.hom := hr.isClosedSubgroup.isAffineHom
  let : IsAffine P'.X.left := isAffine_of_isAffineHom P'.X.hom
  let : IsAffine U'.X.left := isAffine_of_isAffineHom U'.X.hom
  let : LocallyOfFiniteType P'.X.hom := hp.isClosedSubgroup.locallyOfFiniteType
  let : LocallyOfFiniteType U'.X.hom := hr.isClosedSubgroup.locallyOfFiniteType
  obtain ⟨hp', hr'⟩ := (affineWeilParabolicRadicalTransport K L G hG).1 P' U' p r hp
    (geometricRadical_of_radical hG hp hr)
  let q := AffineWeil.map K L p ≫ w.inv
  have hq : IsParabolicSubgroup q := hp'.comp_iso w.symm
  have hproper : SubgroupFunctor.range q ≠ ⊤ := by
    intro h
    apply P.property
    rw [← hpP, ← range_weil_eq_top_iff K L p hp.isClosedSubgroup]
    exact (range_comp_iso_eq_top_iff _ w.symm).mp h
  let Q : ProperRationalParabolic W := ⟨⟨_, ⟨_, q, hq, rfl⟩⟩, hproper⟩
  have hradK : properRationalParabolicRadicals hPD hW Q =
      SubgroupFunctor.range (AffineWeil.map K L r ≫ q) :=
    properRationalParabolicRadicals_eq hPD hW hq hproper hr'.1
  refine ⟨Q, ?_⟩
  change WeilSubgroupsMatch K L w _ (rationalParabolicRadical hPD hG P.val)
  rw [hradK, ← hrad]
  apply weilSubgroupsMatch_range_of_square K L w (Iso.refl _)
  simp only [q, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.refl_hom,
    Category.id_comp, AffineWeil.map_comp]

end Parabolics

section RadicalMeasures

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of L))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {W : GroupScheme (Spec (CommRingCat.of K))} [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom]
  (w : W ≅ AffineWeil.groupScheme K L G)
  (hPD : ParabolicDynamicStatement.{u}) (hW : IsConnectedReductive W) (hG : IsConnectedReductive G)
  (Q : ProperRationalParabolic W) (P : ProperRationalParabolic G)

local notation "D" => properRationalParabolicRadicals hPD hW Q
local notation "E" => properRationalParabolicRadicals hPD hG P

/-- The induced isomorphism of the actual adelic radicals. -/
def weilRadicalAdelicEquiv (matchPoints : WeilSubgroupsMatch K L w D E) :
    AdelicSubgroupPoints.adelicPoints K W D ≃ₜ*
    AdelicSubgroupPoints.adelicPoints L G E := by
  exact Langlands.QuotientIntegration.subgroupContinuousMulEquiv (ambientEquiv K L w)
    (AdelicSubgroupPoints.adelicPoints K W D) (AdelicSubgroupPoints.adelicPoints L G E) matchPoints.1

omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom] in
@[simp]
theorem weilRadicalAdelicEquiv_val (m : WeilSubgroupsMatch K L w D E)
    (x : AdelicSubgroupPoints.adelicPoints K W D) :
    (weilRadicalAdelicEquiv K L w hPD hW hG Q P m x : AdelicGroupPoints L G) =
      ambientEquiv K L w x := rfl

omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom] in
private theorem weilRadicalAdelicEquiv_mem_rational (m : WeilSubgroupsMatch K L w D E)
    (x : AdelicSubgroupPoints.adelicPoints K W D) :
    weilRadicalAdelicEquiv K L w hPD hW hG Q P m x ∈ AdelicSubgroupPoints.rationalSubgroup L G E ↔
      x ∈ AdelicSubgroupPoints.rationalSubgroup K W D := by
  let a := weilRadicalAdelicEquiv K L w hPD hW hG Q P m
  have h (y : AdelicSubgroupPoints.rationalPoints K W D) :
      a (AdelicSubgroupPoints.rational K W D y) =
        AdelicSubgroupPoints.rational L G E
          ⟨principalEquiv K L w y.val, (m.2 y.val).mpr y.property⟩ :=
    Subtype.ext (ambientEquiv_rational K L w y.val)
  constructor
  · rintro ⟨z, hz⟩
    let y := (principalEquiv K L w).symm z.val
    have hy : principalEquiv K L w y = z.val := (principalEquiv K L w).apply_symm_apply z.val
    have hmem : y ∈ AdelicSubgroupPoints.rationalPoints K W D :=
      (m.2 y).mp (hy.symm ▸ z.property)
    refine ⟨⟨y, hmem⟩, a.injective ?_⟩
    exact (h ⟨y, hmem⟩).trans
      ((congrArg (AdelicSubgroupPoints.rational L G E) (Subtype.ext hy)).trans hz)
  · rintro ⟨y, rfl⟩
    exact ⟨_, (h y).symm⟩

/-- The induced map on actual left rational quotients of the radicals. -/
def weilRadicalQuotientEquiv (matchPoints : WeilSubgroupsMatch K L w D E) :
    AdelicSubgroupPoints.RationalQuotient K W D ≃ᵐ
    AdelicSubgroupPoints.RationalQuotient L G E :=
  LeftCosetSpace.measurableEquivOfMulEquiv
    (weilRadicalAdelicEquiv K L w hPD hW hG Q P matchPoints) _ _
    (weilRadicalAdelicEquiv_mem_rational K L w hPD hW hG Q P matchPoints)

omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom] in
@[simp]
theorem weilRadicalQuotientEquiv_mk (m : WeilSubgroupsMatch K L w D E)
    (x : AdelicSubgroupPoints.adelicPoints K W D) :
    weilRadicalQuotientEquiv K L w hPD hW hG Q P m (LeftCosetSpace.mk _ x) =
      LeftCosetSpace.mk _ (weilRadicalAdelicEquiv K L w hPD hW hG Q P m x) := rfl

set_option maxHeartbeats 900000 in
/-- Passing to mass one cancels the change of Haar normalization on the radical groups. -/
theorem measurePreserving_weilRadicalQuotient (m : WeilSubgroupsMatch K L w D E) :
    MeasurePreserving (weilRadicalQuotientEquiv K L w hPD hW hG Q P m)
      (properParabolicQuotientMeasure K W hPD hW Q)
      (properParabolicQuotientMeasure L G hPD hG P) := by
  let a := weilRadicalAdelicEquiv K L w hPD hW hG Q P m
  let b := weilRadicalQuotientEquiv K L w hPD hW hG Q P m
  let Γ := AdelicSubgroupPoints.rationalSubgroup L G E
  let mK : Measure (AdelicSubgroupPoints.adelicPoints K W D) := Measure.haar
  let mL : Measure (AdelicSubgroupPoints.adelicPoints L G E) := Measure.haar
  let qK := AdelicSubgroupPoints.rationalQuotientHaarMeasure K W D
  let qL := AdelicSubgroupPoints.rationalQuotientHaarMeasure L G E
  let c := haarScalarFactor (Measure.map a mK) mL
  let : (Measure.map a mK).IsHaarMeasure := a.isHaarMeasure_map mK
  let : (Measure.map a mK).Regular := Measure.Regular.map a.toHomeomorph
  have hm : Measure.map a mK = (c : ℝ≥0∞) • mL := isMulLeftInvariant_eq_smul_of_regular _ _
  have hK := AdelicSubgroupPoints.isDiscrete_rationalSubgroup K W D
  have hL := AdelicSubgroupPoints.isDiscrete_rationalSubgroup L G E
  have hraw : Measure.map b qK = (c : ℝ≥0∞) • qL := by
    have hh := LeftCosetSpace.measurePreserving_discreteQuotientMeasure a _ Γ
      (weilRadicalAdelicEquiv_mem_rational K L w hPD hW hG Q P m) hK hL
      mK (Measure.map a mK) ⟨a.continuous.measurable, rfl⟩
    refine hh.map_eq.trans ?_
    rw [hm]
    exact LeftCosetSpace.quotientMeasure_smul Γ mL (LeftCosetSpace.fundamentalDomain Γ hL) _
  let dK := AdelicSubgroupPoints.quotientMassNormalizer K W D
  let dL := AdelicSubgroupPoints.quotientMassNormalizer L G E
  have hnorm : Measure.map b (properParabolicQuotientMeasure K W hPD hW Q) =
      (dK * (c : ℝ≥0∞)) • qL := by
    change Measure.map b (dK • qK) = _
    rw [Measure.map_smul _ b.measurable.aemeasurable, hraw, smul_smul]
  have hmass : (dK * (c : ℝ≥0∞)) * qL Set.univ = 1 := by
    have h := congrArg (fun z : Measure (AdelicSubgroupPoints.RationalQuotient L G E) =>
      z Set.univ) hnorm
    simpa only [Measure.map_apply b.measurable MeasurableSet.univ, Set.preimage_univ,
      measure_univ, Measure.smul_apply, smul_eq_mul] using h.symm
  have hd : dK * (c : ℝ≥0∞) = dL := ENNReal.eq_inv_of_mul_eq_one_left hmass
  exact ⟨b.measurable, hnorm.trans (congrArg (· • qL) hd)⟩

end RadicalMeasures

end Langlands.Automorphic.GroupSchemeFunctions
