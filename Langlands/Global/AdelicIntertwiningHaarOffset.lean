import Langlands.Global.AdelicIntertwiningStabilizer
import Langlands.Global.AdelicIntertwiningRadicalIntersection
import Langlands.Global.EisensteinConstantTerm.Core
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.PositiveSplitCharacterParameter
import Langlands.Analysis.Local.AutomorphismHaarModulusContinuity
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex

/-! # A fixed exponent for the Haar factor of the intertwining integral -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.Automorphic.GroupSchemeFunctions
  PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {q : Q ⟶ G} {l : M ⟶ P} {l' : M' ⟶ Q}
  (iU : U ⟶ P) (iV : V ⟶ Q)
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))
local notation "H" => intertwiningAdelicStabilizer p iU (iV ≫ q) w

omit [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The specified Weyl conjugacy on an arbitrary actual target Levi point. -/
theorem IsWeylConjugation.adelic_comp_eq (hw : IsWeylConjugation p l q l' w c)
    (m : AdelicGroupPoints F M') :
    map F P G p (map F M P l (map F M' M c m)) =
      (innerAdelicPoint F G w)⁻¹ * map F Q G q (map F M' Q l' m) *
        innerAdelicPoint F G w := by
  rw [← map_comp_apply_of_hom (p := l) c, ← map_comp_apply_of_hom (p := p) (c ≫ l),
    Category.assoc, hw.comp_eq]
  change m ≫ (l' ≫ q ≫ (G.innerIso w).inv).hom.hom = _
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  exact comp_innerIso_inv_adelic w _

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The target Levi action by conjugation preserves the actual closed stabilizer. -/
theorem conjAdelic_mem_intertwiningAdelicStabilizer_iff
    (hw : IsWeylConjugation p l q l' w c)
    (hU : (SubgroupFunctor.range iU).IsNormal) (hV : (SubgroupFunctor.range iV).IsNormal)
    (m : AdelicGroupPoints F M') (x : Vₐ) :
    EisensteinConstantTerm.conjAdelic q iV hV (map F M' Q l' m) x ∈ H ↔ x ∈ H := by
  let wA := innerAdelicPoint F G w
  let a := map F Q G q (map F M' Q l' m)
  let mP := map F M P l (map F M' M c m)
  let aP := map F P G p mP
  have hComp : aP = wA⁻¹ * a * wA := hw.adelic_comp_eq m
  have hIff (y : AdelicGroupPoints F G) :
      aP * y * aP⁻¹ ∈ parabolicUnipotentImage F p iU ↔ y ∈ parabolicUnipotentImage F p iU := by
    change (_ ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p))) ↔
      y ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p))
    refine ⟨?_, fun hy => conj_mem_adelicPoints_range p iU hU mP hy⟩
    intro hy
    have h := conj_mem_adelicPoints_range p iU hU mP⁻¹ hy
    change map F P G p mP⁻¹ * (aP * y * aP⁻¹) * (map F P G p mP⁻¹)⁻¹ ∈
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)) at h
    simpa only [map_inv, ← show aP = map F P G p mP from rfl, inv_inv,
      mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  rw [mem_intertwiningAdelicStabilizer_iff, mem_intertwiningAdelicStabilizer_iff]
  change wA⁻¹ * (a * x.val * a⁻¹) * wA ∈ parabolicUnipotentImage F p iU ↔ _
  rw [show wA⁻¹ * (a * x.val * a⁻¹) * wA = aP * (wA⁻¹ * x.val * wA) * aP⁻¹ by
    rw [hComp]
    group]
  exact hIff _

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} {a : A.toGrp ⟶ M'}

/-- Conjugation by the actual positive split component in the target radical. -/
def positiveIntertwiningRadicalAction (hV : (SubgroupFunctor.range iV).IsNormal)
    (x : intrinsicSubgroup F A) : Vₐ ≃ₜ* Vₐ :=
  EisensteinConstantTerm.conjAdelic q iV hV (positivePointMap F Q A (a ≫ l') x)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- This action preserves the closed stabilizer on the same actual subgroup. -/
theorem positiveIntertwiningRadicalAction_mem_stabilizer
    (hw : IsWeylConjugation p l q l' w c)
    (hU : (SubgroupFunctor.range iU).IsNormal) (hV : (SubgroupFunctor.range iV).IsNormal)
    (x : intrinsicSubgroup F A) (v : Vₐ) :
    positiveIntertwiningRadicalAction (q := q) (l' := l') (a := a) iV hV x v ∈ H ↔ v ∈ H := by
  unfold positiveIntertwiningRadicalAction
  rw [positivePointMap_apply, map_comp_apply_of_hom]
  exact conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hU hV _ v

omit [IsAffineHom G.X.hom] in
/-- A continuous homomorphism acting by conjugation on the target radical and
preserving the full stabilizer induces continuous Haar moduli on both groups. -/
theorem intertwiningConjugationFamily {X : Type*} [Group X] [TopologicalSpace X]
    [LocallyCompactSpace X] (hV : (SubgroupFunctor.range iV).IsNormal)
    (τ : X →ₜ* AdelicGroupPoints F Q)
    (hPres : ∀ x v, EisensteinConstantTerm.conjAdelic q iV hV (τ x) v ∈ H ↔ v ∈ H)
    (hVclosed : IsClosed (Vₐ : Set (AdelicGroupPoints F G))) (hH : IsClosed (H : Set Vₐ)) :
    haveI : LocallyCompactSpace Vₐ := hVclosed.locallyCompactSpace
    haveI : LocallyCompactSpace H := hH.locallyCompactSpace
    let α := fun x => EisensteinConstantTerm.conjAdelic q iV hV (τ x)
    let αH := fun x => subgroupAutomorphism H (α x) (hPres x)
    (∀ x y, α (x * y) = (α y).trans (α x)) ∧
    (∀ x y, αH (x * y) = (αH y).trans (αH x)) ∧
    α 1 = ContinuousMulEquiv.refl Vₐ ∧ αH 1 = ContinuousMulEquiv.refl H ∧
    Continuous (fun x => (mulEquivHaarChar (α x) : ℝ)) ∧
    Continuous (fun x => (mulEquivHaarChar (αH x) : ℝ)) := by
  intro α αH
  let : LocallyCompactSpace Vₐ := hVclosed.locallyCompactSpace
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : PolishSpace Vₐ := hVclosed.polishSpace
  let : PolishSpace H := hH.polishSpace
  let target := (map F Q G q).comp τ
  have hAct (x : X) (v : Vₐ) : (α x v).val = target x * v.val * (target x)⁻¹ := rfl
  have hInv (x : X) (v : Vₐ) : ((α x).symm v).val = (target x)⁻¹ * v.val * target x := by
    change map F Q G q ((τ x)⁻¹) * v.val *
      (map F Q G q ((τ x)⁻¹))⁻¹ = _
    rw [map_inv, inv_inv]
    rfl
  have hMul (x y : X) : α (x * y) = (α y).trans (α x) := by
    apply ContinuousMulEquiv.ext
    intro v
    apply Subtype.ext
    change (α (x * y) v).val = (α x (α y v)).val
    rw [hAct, hAct, hAct, map_mul]
    group
  have hOne : α 1 = ContinuousMulEquiv.refl Vₐ := by
    apply ContinuousMulEquiv.ext
    intro v
    apply Subtype.ext
    rw [hAct, map_one]
    simp
  have hHMul (x y : X) : αH (x * y) = (αH y).trans (αH x) := by
    apply ContinuousMulEquiv.ext
    intro v
    apply Subtype.ext
    change α (x * y) v.val = α x (α y v.val)
    rw [hMul]
    rfl
  have hHOne : αH 1 = ContinuousMulEquiv.refl H := by
    apply ContinuousMulEquiv.ext
    intro v
    apply Subtype.ext
    change α 1 v.val = v.val
    rw [hOne]
    rfl
  have hαc : Continuous (fun x : X × Vₐ => α x.1 x.2) := by
    have h : Continuous (fun z : X × Vₐ => (α z.1 z.2).val) := by
      simp only [hAct]
      exact ((target.continuous.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)).mul (target.continuous.comp continuous_fst).inv
    exact h.subtype_mk _
  have hαinv : Continuous (fun x : X × Vₐ => (α x.1).symm x.2) := by
    have h : Continuous (fun z : X × Vₐ => ((α z.1).symm z.2).val) := by
      simp only [hInv]
      exact ((target.continuous.comp continuous_fst).inv.mul
        (continuous_subtype_val.comp continuous_snd)).mul (target.continuous.comp continuous_fst)
    exact h.subtype_mk _
  have hαHc : Continuous (fun x : X × H => αH x.1 x.2) :=
    (hαc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hαHinv : Continuous (fun x : X × H => (αH x.1).symm x.2) :=
    (hαinv.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hVcont := Langlands.Haar.automorphismHaarModulusContinuity α Measure.haar hαc hαinv
  have hHcont := Langlands.Haar.automorphismHaarModulusContinuity αH Measure.haar hαHc hαHinv
  exact ⟨hMul, hHMul, hOne, hHOne, hVcont, hHcont⟩

variable [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  [IsClosedImmersion (iV ≫ q).hom.hom.left]

/-- The ratio between the radical and stabilizer Haar factors on the positive
split component is a single fixed character parameter of the target. -/
def IntertwiningHaarOffsetStatement
    (_r : ParabolicRootPresentation q l' a) (hw : IsWeylConjugation p l q l' w c)
    (hU : (SubgroupFunctor.range iU).IsNormal) (hV : (SubgroupFunctor.range iV).IsNormal) : Prop :=
  ∀ (hi : IsClosedSubgroup (iU ≫ p)) (hVu : IsUnipotent V),
    let hVclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
    let hH := (intertwiningStabilizer p iU (iV ≫ q) w
      (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) hi hVu).1
    haveI : LocallyCompactSpace Vₐ := hVclosed.locallyCompactSpace
    haveI : LocallyCompactSpace H := hH.locallyCompactSpace
    ∃ offset : ComplexCharacterParameter F Q,
      ∀ x : intrinsicSubgroup F A,
        let α := positiveIntertwiningRadicalAction (q := q) (l' := l') (a := a) iV hV x
        let αH := subgroupAutomorphism H α
          (positiveIntertwiningRadicalAction_mem_stabilizer (a := a) iU iV hw hU hV x)
        parameterPower F Q offset (positivePointMap F Q A (a ≫ l') x) =
          (((mulEquivHaarChar α / mulEquivHaarChar αH : ℝ≥0) : ℝ) : ℂ)

theorem intertwiningHaarOffset
    (r : ParabolicRootPresentation q l' a) (hw : IsWeylConjugation p l q l' w c)
    (hU : (SubgroupFunctor.range iU).IsNormal) (hV : (SubgroupFunctor.range iV).IsNormal) :
    IntertwiningHaarOffsetStatement iU iV r hw hU hV := by
  intro hi hVu hVclosed hH
  let : LocallyCompactSpace Vₐ := hVclosed.locallyCompactSpace
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let α := positiveIntertwiningRadicalAction (q := q) (l' := l') (a := a) iV hV
  let hα := positiveIntertwiningRadicalAction_mem_stabilizer (a := a) iU iV hw hU hV
  let αH := fun x => subgroupAutomorphism H (α x) (hα x)
  let Apos := intrinsicSubgroup F A
  obtain ⟨I, hI, ⟨e⟩⟩ := r.isCompatible.splitComponent.isCentralSplitTorus.1.1
  let : Fintype I := Fintype.ofFinite I
  let : LocallyCompactSpace Apos := positiveLocallyCompactSpace F A I e
  obtain ⟨hMul, hHMul, hOne, hHOne, hVcont, hHcont⟩ := intertwiningConjugationFamily
    iU iV hV (positivePointMap F Q A (a ≫ l')) hα hVclosed hH
  change (∀ x y, α (x * y) = (α y).trans (α x)) at hMul
  change (∀ x y, αH (x * y) = (αH y).trans (αH x)) at hHMul
  change α 1 = ContinuousMulEquiv.refl Vₐ at hOne
  change αH 1 = ContinuousMulEquiv.refl H at hHOne
  let charV : Apos →* ℝ≥0ˣ := {
    toFun := fun x => Units.mk0 (mulEquivHaarChar (α x)) (mulEquivHaarChar_pos _).ne'
    map_one' := by apply Units.ext; simp [hOne]
    map_mul' := fun x y => by
      apply Units.ext
      change mulEquivHaarChar (α (x * y)) = _
      simp only [hMul, mulEquivHaarChar_trans, Units.val_mul, Units.val_mk0, mul_comm] }
  let charH : Apos →* ℝ≥0ˣ := {
    toFun := fun x => Units.mk0 (mulEquivHaarChar (αH x)) (mulEquivHaarChar_pos _).ne'
    map_one' := by apply Units.ext; simp [hHOne]
    map_mul' := fun x y => by
      apply Units.ext
      change mulEquivHaarChar (αH (x * y)) = _
      simp only [hHMul, mulEquivHaarChar_trans, Units.val_mul, Units.val_mk0, mul_comm] }
  let ratio : Apos →* ℝ≥0ˣ := charV / charH
  have hR (x : Apos) : (ratio x : ℝ≥0) = mulEquivHaarChar (α x) / mulEquivHaarChar (αH x) := by
    exact Units.val_div_eq_div_val _ _
  have hRc : Continuous (fun x : Apos => ((ratio x : ℝ≥0) : ℝ)) := by
    simp only [hR, NNReal.coe_div]
    exact hVcont.div hHcont fun x => (NNReal.coe_pos.mpr (mulEquivHaarChar_pos (αH x))).ne'
  obtain ⟨_, _, proj, -, -, hproj, -⟩ := r.isCompatible.levi.exists_unipotentRadical_retraction
  have hsurj : Function.Surjective (characterRestrict l') := by
    intro χ
    refine ⟨characterRestrict proj χ, ?_⟩
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, hproj, characterRestrict_id]
    rfl
  have hrange : (characterRestrict (a ≫ l')).range = (characterRestrict a).range := by
    ext χ
    change (∃ x, characterRestrict (a ≫ l') x = χ) ↔ ∃ y, characterRestrict a y = χ
    simp only [characterRestrict_comp, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨characterRestrict l' x, hx⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, rfl⟩
  have hIndex : (characterRestrict (a ≫ l')).range.FiniteIndex := hrange.symm ▸
    r.isCompatible.splitComponent.finiteIndex_range_characterRestrict r.isCompatible.levi.isConnectedReductive
  obtain ⟨offset, hoff⟩ := positiveSplitCharacterParameter F Q A (a ≫ l')
    r.isCompatible.splitComponent.isCentralSplitTorus.1.1 hIndex ratio hRc
  exact ⟨offset, fun x => (hoff x).trans (congrArg (fun y : ℝ≥0 => ((y : ℝ) : ℂ)) (hR x))⟩

end Langlands.Global.AdelicGroupPoints
