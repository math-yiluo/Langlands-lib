import Langlands.Global.ArthurTruncationBruhatIndices
import Langlands.Global.ArthurTruncationNestedConstantTerm
import Langlands.Global.AdelicEisensteinGeometricLemmaProof

/-! # Bruhat expansion of a parabolic cutoff contribution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Classical

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Group.RelativeWeylIndexing Langlands.Aubert.General.RationalPointFamily
  AdelicGroupPoints EisensteinConstantTerm ArthurParabolicSpaces
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

section Transport

variable {P U V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left] [IsAffine V.X.left]

private theorem transport_bruhat {p p' : P ⟶ G} (hp : p = p') (l : U ⟶ P)
    [IsClosedImmersion (l ≫ p).hom.hom.left] [IsClosedImmersion (l ≫ p').hom.hom.left]
    {j j' : V ⟶ G} (hj : j = j') [IsClosedImmersion j.hom.hom.left]
    [IsClosedImmersion j'.hom.hom.left] (w y : A) (Φ Ψ : A → ℂ)
    (hΦ : ∀ x, subgroupConstantTerm F (l ≫ p') Φ x = Ψ x) (z : ℂ)
    (h : Integrable (fun x => subgroupConstantTerm F (l ≫ p) Φ
        (w⁻¹ * (x.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)).val * y))
        (intertwiningMeasure F p l j w) ∧
      (∫ x, subgroupConstantTerm F (l ≫ p) Φ
        (w⁻¹ * (x.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)).val * y)
        ∂intertwiningMeasure F p l j w) = z) :
    Integrable (fun x => Ψ
        (w⁻¹ * (x.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j')).val * y))
        (intertwiningMeasure F p' l j' w) ∧
      (∫ x, Ψ (w⁻¹ * (x.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j')).val * y)
        ∂intertwiningMeasure F p' l j' w) = z := by
  subst p
  subst j
  simpa only [hΦ] using h

end Transport

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "B" => SimpleRoot i ν
local notation "roots" => rootSet i ν
local notation "par" => Standard.parabolicHom i ν
local notation "rad" => Standard.unipotentHom i ν
local notation "iRad" => Standard.unipotentToParabolic i ν
local notation "cTerm" => constantTerm F i ν
local notation "H" => height (K := K) hi hK hρ

/-- Convert a finite set of simple roots to the characters used in the truncation definition. -/
def labelFinset (S : Finset B) : Finset (characterLattice T) :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

omit [NumberField F] [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
@[simp] theorem coe_labelFinset (S : Finset B) :
    (labelFinset S : Set (characterLattice T)) = roots S := by
  ext a
  simp only [Finset.mem_coe, labelFinset, Finset.mem_map, Function.Embedding.coeFn_mk, mem_rootSet]

omit [NumberField F] [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
@[simp] theorem card_labelFinset (S : Finset B) : (labelFinset S).card = S.card :=
  Finset.card_map _

include hG hi in
omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
theorem labelFinset_mem_powerset (S : Finset B) : labelFinset S ∈ (simpleFinset ν hG hi).powerset := by
  apply Finset.mem_powerset.mpr
  intro a ha
  rw [← Finset.mem_coe, coe_labelFinset] at ha
  exact (mem_simpleFinset hG hi).mpr (rootSet_subset i ν S ha)

/-- The common quotient for a Weyl cell with smaller source and target indices `J, R`. -/
abbrev BruhatRadicalQuotient (J R : Finset B) (w : A) :=
  LeftCosetSpace (intertwiningRationalSubgroup F (par (roots J)) (iRad (roots J)) (rad (roots R)) w)

/-- The normalized measure in the smaller radical integral. -/
abbrev bruhatRadicalMeasure (J R : Finset B) (w : A) : Measure (BruhatRadicalQuotient J R w) :=
  intertwiningMeasure F (par (roots J)) (iRad (roots J)) (rad (roots R)) w

/-- The integral's argument in `G(𝔸)`. -/
def bruhatEvaluation {J R : Finset B} {w : A} (y : A) (v : BruhatRadicalQuotient J R w) : A :=
  w⁻¹ * (v.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (rad (roots R)))).val * y

/-- The nested constant term on a Weyl cell, with the original parabolic's cutoff. -/
def bruhatCutoffIntegrand (S J R : Finset B) (w : A) (Tp : V T) (φ : A → ℂ)
    (y : A) (v : BruhatRadicalQuotient J R w) : ℂ :=
  let z := bruhatEvaluation (J := J) (R := R) (w := w) y v
  cTerm (roots J) φ z * (ArthurRelative.tauHat hG hi ν D (roots S) (simpleRelativeRoots i ν)
    (H z - Tp) : ℂ)

/-- The normalized integral of one smaller-radical kernel in a Weyl cell. -/
abbrev bruhatCutoffIntegral (S J R : Finset B) (w : A) (Tp : V T) (φ : A → ℂ) (y : A) : ℂ :=
  ∫ v, bruhatCutoffIntegrand hG hi D hK hρ S J R w Tp φ y v ∂bruhatRadicalMeasure J R w

/-- Rational cosets for the smaller target parabolic in a fixed Weyl cell. -/
abbrev BruhatOuterCosets (Q R : Finset B) :=
  OuterCosets (rationalImage F (par (roots Q))) (rationalImage F (par (roots R)))

/-- The contribution from a fixed Weyl cell after the smaller radical has been unfolded. -/
abbrev bruhatCutoffSum (Q S J R : Finset B) (w : A) (Tp : V T) (φ : A → ℂ) (x : A) : ℂ :=
  ∑' c : BruhatOuterCosets Q R,
    bruhatCutoffIntegral hG hi D hK hρ S J R w Tp φ
      (((c.out : rationalImage F (par (roots Q))) : A) * x)

include hν in
set_option maxHeartbeats 1400000 in
/-- For a fixed outer parabolic and a single cutoff kernel, the geometric lemma gives
its expansion, summability in the outer rational cosets, and integrability in each fiber. -/
theorem constantTerm_cutoffSeries_bruhat
    (hunf : GeometricLemmaUnfoldingStatement.{u}) [Fintype B] [Fintype (relativeWeylGroup i)]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M (relativeWeylGroup i))
    (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (Q S : Finset B) (n : relativeWeylGroup i → normalizerPoints i)
    (hn : ∀ w, (QuotientGroup.mk (n w) : relativeWeylGroup i) = w)
    (Tp : V T) (φ : A → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ) (x : A) :
    let I := {w : relativeWeylGroup i // IsMinimal cs Q S w}
    let J (w : I) := intersectionSubset cs Q S w.val
    let R (w : I) := intersectionSubset cs S Q w.val⁻¹
    let wA (w : I) := innerAdelicPoint F G (n w.val).val
    let y (w : I) (c : BruhatOuterCosets Q (R w)) :=
      (((c.out : rationalImage F (par (roots Q))) : A) * x)
    (∀ (w : I) (c : BruhatOuterCosets Q (R w)),
      Integrable (bruhatCutoffIntegrand hG hi D hK hρ S (J w) (R w) (wA w) Tp φ (y w c))
        (bruhatRadicalMeasure (J w) (R w) (wA w))) ∧
    (∀ w : I, Summable (fun c : BruhatOuterCosets Q (R w) =>
      bruhatCutoffIntegral hG hi D hK hρ S (J w) (R w) (wA w) Tp φ (y w c))) ∧
    cTerm (roots Q) (fun z => ∑' c : ParabolicRationalCosets F (par (roots S)),
      cutoffKernel hG hi D hK hρ (roots S) Tp φ
        (((c.out : rationalSubgroup F G) : A) * z)) x =
      ∑ w ∈ Finset.univ.filter (IsMinimal cs Q S),
        bruhatCutoffSum hG hi D hK hρ Q S (intersectionSubset cs Q S w)
          (intersectionSubset cs S Q w⁻¹) (innerAdelicPoint F G (n w).val) Tp φ x := by
  classical
  intro I J R wA y
  let : Fintype I := Fintype.ofFinite _
  let p := par (roots S)
  let q := par (roots Q)
  let iu := iRad (roots S)
  let iv := iRad (roots Q)
  let w (j : I) := (n j.val).val
  let Φ := cutoffKernel hG hi D hK hρ (roots S) Tp φ
  have hS := rootSet_subset i ν S
  have hQ := rootSet_subset i ν Q
  have hIU := (Standard.parabolicStructure i ν hG hi hν _ hS).2.2.1
  have hIV := (Standard.parabolicStructure i ν hG hi hν _ hQ).2.2.1
  have hP := (Standard.parabolicStructure i ν hG hi hν _ hS).1
  have hQp := (Standard.parabolicStructure i ν hG hi hν _ hQ).1
  have hiv : iv ≫ q = rad (roots Q) := Standard.unipotentToParabolic_comp i ν _
  let : IsClosedImmersion (iv ≫ q).hom.hom.left := hiv ▸ inferInstanceAs
    (IsClosedImmersion (rad (roots Q)).hom.hom.left)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iv ≫ q))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iv ≫ q)
      hIV.1.smooth hIV.1.connectedSpace hIV.1.isUnipotent
  have hm : Measurable Φ := cutoffKernel_measurable hG hi hν D hK hρ _ Tp φ hφ
  have hPInv : ∀ z ∈ rationalImage F p, ∀ x, Φ (z * x) = Φ x := by
    intro z hz g
    exact truncationKernel_parabolicRational_mul hG hi hν D hK hρ hS Tp φ hφ.2.2
      ((mem_parabolicRationalImage_iff (i := i) (ν := ν) _ z).mpr hz) g
  have hUInv : ∀ u ∈ parabolicUnipotentImage F p iu, ∀ x, Φ (u * x) = Φ x := by
    intro u hu g
    change u ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iu ≫ p)) at hu
    rw [show iu ≫ p = rad (roots S) from Standard.unipotentToParabolic_comp i ν _] at hu
    exact cutoffKernel_radical_mul hG hi hν hK hρ D hS Tp φ hφ.2.2 ⟨u, hu⟩ g
  have hdata (j : I) := eisensteinGeometricLemmaDatum_of_minimal F G hG T i hi ν hν cs hcs S Q
    (n j.val) (by rw [hn]; exact j.2)
  have hdata' (j : I) : ∃
      (f : Standard.parabolicScheme i ν (roots (J j)) ⟶ Standard.parabolicScheme i ν (roots S))
      (g : Standard.parabolicScheme i ν (roots (R j)) ⟶ Standard.parabolicScheme i ν (roots Q)),
      f ≫ p = par (roots (J j)) ∧ g ≫ q = par (roots (R j)) ∧
        IsGeometricLemmaDatum p iu q iv f g (w j) := by
    have h := hdata j
    dsimp only at h
    rw [hn j.val] at h
    obtain ⟨f, g, hf, hg, hdat, -, -⟩ := h
    exact ⟨f, g, hf, hg, hdat⟩
  have hQ' (j : I) : rationalImage F (par (roots (R j))) =
      (rationalImage F q ⊓ (rationalImage F p).map (MulAut.conj (wA j)).toMonoidHom) ⊔
        rationalImage F (iv ≫ q) := by
    obtain ⟨f, g, hf, hg, hdat⟩ := hdata' j
    exact hg ▸ hdat.rationalImage_right
  have hB (j : I) (y : A)
      (hfin : ∫⁻ v, ‖Φ ((wA j)⁻¹ *
        (v.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iv ≫ q))).val * y)‖ₑ
        ∂stabilizerMeasure F p (iv ≫ q) (wA j) < ∞) :
      Integrable (bruhatCutoffIntegrand hG hi D hK hρ S (J j) (R j) (wA j) Tp φ y)
        (bruhatRadicalMeasure (J j) (R j) (wA j)) ∧
      bruhatCutoffIntegral hG hi D hK hρ S (J j) (R j) (wA j) Tp φ y =
        ∫ v, Φ ((wA j)⁻¹ *
          (v.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iv ≫ q))).val * y)
          ∂stabilizerMeasure F p (iv ≫ q) (wA j) := by
    obtain ⟨f, g, hf, hg, hdat⟩ := hdata' j
    let pJ := par (roots (J j))
    let qR := par (roots (R j))
    let iJ := iRad (roots (J j))
    let iR := iRad (roots (R j))
    have hJ := (Standard.parabolicStructure i ν hG hi hν _ (rootSet_subset i ν (J j)))
    have hR := (Standard.parabolicStructure i ν hG hi hν _ (rootSet_subset i ν (R j)))
    have hJu : iJ ≫ pJ = rad (roots (J j)) := Standard.unipotentToParabolic_comp i ν _
    have hJcomp : iJ ≫ f ≫ p = rad (roots (J j)) := by rw [hf]; exact hJu
    have hRcomp : iR ≫ g ≫ q = rad (roots (R j)) := by
      rw [hg]
      exact Standard.unipotentToParabolic_comp i ν _
    let : IsClosedImmersion (f ≫ p).hom.hom.left := hf ▸ inferInstanceAs
      (IsClosedImmersion pJ.hom.hom.left)
    let : IsClosedImmersion (iJ ≫ f ≫ p).hom.hom.left := hJcomp ▸ inferInstanceAs
      (IsClosedImmersion (rad (roots (J j))).hom.hom.left)
    let : IsClosedImmersion (iJ ≫ pJ).hom.hom.left := hJu ▸ inferInstanceAs
      (IsClosedImmersion (rad (roots (J j))).hom.hom.left)
    let : IsClosedImmersion (iR ≫ g ≫ q).hom.hom.left := hRcomp ▸ inferInstanceAs
      (IsClosedImmersion (rad (roots (R j))).hom.hom.left)
    have hGeo := hunf F G _ _ _ _ _ _ _ _ p iu q iv (w j) f iJ g iR
      hG hP hIU hQp hIV (hf ▸ hJ.1) hJ.2.2.1 (hg ▸ hR.1) hR.2.2.1 hdat
      Φ hm hUInv hPInv y hfin
    have hmatch (z : A) : subgroupConstantTerm F (iJ ≫ pJ) Φ z =
        cTerm (roots (J j)) φ z * (ArthurRelative.tauHat hG hi ν D (roots S) (simpleRelativeRoots i ν)
          (H z - Tp) : ℂ) := by
      rw [subgroupConstantTerm_congr_hom hJu]
      exact constantTerm_cutoffKernel_of_subset hG hi hν D hK hρ
        ((rootSet_subset_iff i ν (J j) S).mpr (intersectionSubset_subset cs Q S _)) hS Tp φ hφ z
    exact transport_bruhat hf iJ hRcomp (wA j) y Φ _ hmatch _ hGeo
  obtain ⟨C, hC, hbound⟩ := exists_enorm_cutoffSeries_bound_on_radical hG hi hν D hK hρ
    (labelFinset S) (labelFinset_mem_powerset hG hi S) (roots Q) hQ Tp φ hφ x
  have hcanon : ∀ v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (rad (roots Q))),
      ∑' c : ParabolicRationalCosets F p,
        ‖Φ (((c.out : rationalSubgroup F G) : A) * ((v : A) * x))‖ₑ ≤ C := by
    simp only [coe_labelFinset] at hbound
    exact hbound
  have hcanon' : ∀ v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iv ≫ q)),
      ∑' c : ParabolicRationalCosets F p,
        ‖Φ (((c.out : rationalSubgroup F G) : A) * ((v : A) * x))‖ₑ ≤ C := by
    rw [hiv]
    exact hcanon
  have hcore := constantTerm_series_eq_of_measurable (q := q) (iV := iv) (p := p)
    (isDoubleCosetRepresentatives_of_minimal F G hG T i hi ν hν cs hcs S Q n hn)
    (fun j : I => rationalImage F (par (roots (R j)))) hQ' hIV.1.isNormal hm hPInv x C hC hcanon'
    (fun j y => bruhatCutoffIntegral hG hi D hK hρ S (J j) (R j) (wA j) Tp φ y)
    (fun j y => Integrable (bruhatCutoffIntegrand hG hi D hK hρ S (J j) (R j) (wA j) Tp φ y)
      (bruhatRadicalMeasure (J j) (R j) (wA j))) hB
  obtain ⟨h1, h2, h3⟩ := hcore
  refine ⟨h1, h2, ?_⟩
  unfold constantTerm
  rw [← subgroupConstantTerm_congr_hom hiv]
  exact h3.trans ((Finset.sum_subtype (p := IsMinimal cs Q S)
    (Finset.univ.filter (IsMinimal cs Q S)) (fun w => by simp) (fun w =>
      bruhatCutoffSum hG hi D hK hρ Q S (intersectionSubset cs Q S w)
        (intersectionSubset cs S Q w⁻¹) (innerAdelicPoint F G (n w).val) Tp φ x)).symm)

end Langlands.Global.ArthurTruncation.Idempotence
