import Langlands.Global.RankinSelberg.RealOrdinaryBlockAssembly
import Langlands.Global.RankinSelberg.RealLocalEqualGrowthStep

/-! # Canonical holomorphic coefficient families along real block deformations -/

noncomputable section

open Metric Set Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBlockParameters

open ArchimedeanLocal RealGodement RealGodementProfiles RealPrincipalSeries RealUnequalFamily
open RealJacquetFrobenius (charData)
open RealLocalWhittaker (regularFunctions)

local notation "G" => fun r : ℕ => Langlands.GeneralLinear (r + 1) ℝ

private def moveExponent (u z : ℂ) : ℂ := (u.re : ℂ) * z + (u.im : ℂ) * Complex.I

private theorem differentiable_moveExponent (u : ℂ) : Differentiable ℂ (moveExponent u) :=
  (differentiable_id.const_mul _).add_const _

private theorem deformBlocks_eq_map (ds : List RealBlock) (z : ℂ) :
    deformBlocks ds z = ds.map (fun d => blockOfParams (blockShape d) (moveExponent (blockExponent d) z)) := by
  unfold deformBlocks blockList
  exact List.ofFn_getElem_eq_map ds (fun d => blockOfParams (blockShape d) (moveExponent (blockExponent d) z))

private theorem ascending_character_families (ds : List RealBlock) :
    ∃ cs : List (Fin 2 × (ℂ → ℂ)), (∀ c ∈ cs, Differentiable ℂ c.2) ∧
      ∀ z, ascendingCharacters (deformBlocks ds z) = cs.map (fun c => charData c.1 (c.2 z)) := by
  induction ds with
  | nil => exact ⟨[], by simp, fun _ => rfl⟩
  | cons d ds ih =>
    obtain ⟨cs, hcs, hC⟩ := ih
    have hCons (z : ℂ) : deformBlocks (d :: ds) z =
        blockOfParams (blockShape d) (moveExponent (blockExponent d) z) :: deformBlocks ds z := by
      rw [deformBlocks_eq_map, deformBlocks_eq_map, List.map_cons]
    cases d with
    | character c =>
      refine ⟨(c.parity, moveExponent c.exponent) :: cs, ?_, fun z => ?_⟩
      · simpa only [List.forall_mem_cons] using And.intro (differentiable_moveExponent c.exponent) hcs
      · rw [hCons]
        change charData c.parity (moveExponent c.exponent z) :: ascendingCharacters (deformBlocks ds z) = _
        rw [hC z]
        rfl
    | induced d =>
      let w := d.weight.natAbs
      let hi : Fin 2 × (ℂ → ℂ) := ⟨RealGammaReflection.positionParity w,
        fun z => moveExponent d.exponent z + (w : ℂ) / 2⟩
      let lo : Fin 2 × (ℂ → ℂ) := ⟨0, fun z => moveExponent d.exponent z - (w : ℂ) / 2⟩
      have hhi : Differentiable ℂ hi.2 := (differentiable_moveExponent _).add_const _
      have hlo : Differentiable ℂ lo.2 := (differentiable_moveExponent _).sub_const _
      by_cases h : d.weight = 0
      · refine ⟨hi :: lo :: cs, ?_, ?_⟩
        · rw [List.forall_mem_cons, List.forall_mem_cons]
          exact ⟨hhi, hlo, hcs⟩
        intro z
        rw [hCons]
        change (if d.weight = 0 then [charData hi.1 (hi.2 z), charData lo.1 (lo.2 z)]
          else [charData lo.1 (lo.2 z), charData hi.1 (hi.2 z)]) ++ ascendingCharacters (deformBlocks ds z) = _
        rw [ite_eq_left h, hC z]
        rfl
      · refine ⟨lo :: hi :: cs, ?_, ?_⟩
        · rw [List.forall_mem_cons, List.forall_mem_cons]
          exact ⟨hlo, hhi, hcs⟩
        intro z
        rw [hCons]
        change (if d.weight = 0 then [charData hi.1 (hi.2 z), charData lo.1 (lo.2 z)]
          else [charData lo.1 (lo.2 z), charData hi.1 (hi.2 z)]) ++ ascendingCharacters (deformBlocks ds z) = _
        rw [ite_eq_right h, hC z]
        rfl

private theorem exists_ascending_parameters {r : ℕ} (ds : List RealBlock) (hr : realRank ds = r + 1) :
    ∃ (p : Fin (r + 1) → Fin 2) (w : ℂ → Fin (r + 1) → ℂ), Differentiable ℂ w ∧
      ∀ z, ascendingExpand (deformBlocks ds z) = characterList p (w z) := by
  obtain ⟨cs, hd, hcs⟩ := ascending_character_families ds
  have hLen : cs.length = r + 1 := by
    have h := congrArg List.length (hcs 0)
    rw [List.length_map, ← realRank_map_character] at h
    change realRank (ascendingExpand (deformBlocks ds 0)) = cs.length at h
    exact h.symm.trans <| (realRank_ascendingExpand _).trans ((realRank_deformBlocks _ _).trans hr)
  let c (i : Fin (r + 1)) := cs[i.cast hLen.symm]
  have he : List.ofFn c = cs := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hLen.symm
    · intro i hi hj
      rw [List.getElem_ofFn]
      rfl
  refine ⟨fun i => (c i).1, fun z i => (c i).2 z, ?_, fun z => ?_⟩
  · exact differentiable_pi.mpr fun i => hd (c i) (List.getElem_mem _)
  · simp only [ascendingExpand, hcs z, characterList, ← he, List.map_ofFn]
    rfl

/-- One coefficient at the original list has a holomorphic lift to the ascending character
models along the deformation, with a uniform toral gauge on the disk of radius three. -/
def RealCanonicalOrdinaryDeformationStatement : Prop :=
  RealUniformCanonicalRangePremise →
    ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    ∀ (a : ℝˣ) (W : G r → ℂ), W ∈ realWhittakerModel r ds a →
      ∃ U : ℂ → G r → ℂ, U 1 = W ∧
        (∀ z, U z ∈ realUniformWhittakerModel r (ascendingExpand (deformBlocks ds z)) a) ∧
        (∀ z, U z ∈ regularFunctions r a) ∧
        (∀ g, Differentiable ℂ (fun z => U z g)) ∧
        HasUniformGauge (ball 0 3) U

theorem realCanonicalOrdinaryDeformation : RealCanonicalOrdinaryDeformationStatement := by
  intro hRange r ds hr a W hW
  obtain ⟨p, w, hw, hPar⟩ := exists_ascending_parameters ds hr
  have hW₁ : W ∈ realUniformWhittakerModel r (characterList p (w 1)) a := by
    rw [← hPar, deformBlocks_one]
    apply uniformModel_le_ascendingExpand r ds hr a
    rwa [← realWhittakerModels_eq r ds hr a]
  obtain ⟨f, hf⟩ := hRange r (-a) p (w 1) (by simpa only [neg_neg] using hW₁)
  let φ := compactRestriction f.val
  have hφ : IsCompactProfile p φ := isCompactProfile_compactRestriction f.property
  let F := canonicalJacquetFamily (-a) hφ
  let U (z : ℂ) := F (w z)
  have hProps := canonicalJacquetFamily_properties (-a) hφ
  have hReg (v : Fin (r + 1) → ℂ) (Xs) : RealLocalWhittaker.iteratedRightDerivative r Xs (F v) ∈
      regularFunctions r a := by simpa only [neg_neg] using hProps.1 v Xs
  refine ⟨U, hf, ?_, fun z => hReg (w z) [], fun g => (hProps.2.2.1 [] g).comp hw, ?_⟩
  · intro z
    have hm := canonicalJacquetMap_mem_uniformModel (-a) p (w z)
      ⟨standardSection (w z) φ, standardSection_mem hφ (w z)⟩
    rw [hPar]
    simpa only [canonicalJacquetMap_standardSection (-a) hφ, neg_neg] using hm
  · let K := w '' closedBall (0 : ℂ) 3
    have hK : IsCompact K := (isCompact_closedBall _ _).image hw.continuous
    obtain ⟨N, hN⟩ := exists_uniform_derivativeGrowth hProps.2.1 hK (subset_univ K)
    have hG := hasUniformGauge_of_derivativeGrowth K F (fun v _ Xs => hReg v Xs) hN
    exact hG.comp w (fun z hz => mem_image_of_mem _ (ball_subset_closedBall hz))

private def parameterDiskProduct : Set (ℂ × ℂ) := ball 0 3 ×ˢ univ

private theorem isOpen_parameterDiskProduct : IsOpen parameterDiskProduct :=
  isOpen_ball.prod isOpen_univ

private theorem joint_family_gauge {r : ℕ} {W : ℂ → G r → ℂ}
    (hW : HasUniformGauge (ball 0 3) W) :
    HasUniformGauge parameterDiskProduct (fun u : ℂ × ℂ => W u.1) :=
  hW.comp Prod.fst (fun _ hu => hu.1)

private theorem joint_family_differentiable {r : ℕ} {W : ℂ → G r → ℂ}
    (hW : ∀ g, Differentiable ℂ (fun z => W z g)) :
    ∀ g, DifferentiableOn ℂ (fun u : ℂ × ℂ => W u.1 g) parameterDiskProduct :=
  fun g => ((hW g).comp differentiable_fst).differentiableOn

/-- The canonical families satisfy joint holomorphy and belong to the original models
on any locus where reverse ascending inclusion holds. -/
theorem realOrdinaryHolomorphicTestFamiliesOn_of_ascending (S : Set ℂ)
    (hRange : RealUniformCanonicalRangePremise)
    (hReverse : ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
      ∀ (a : ℝˣ) (z : ℂ), z ∈ S →
      realUniformWhittakerModel r (ascendingExpand (deformBlocks ds z)) a ≤
        realWhittakerModel r (deformBlocks ds z) a) :
    RealOrdinaryHolomorphicTestFamiliesOn S := by
  constructor
  · intro r t h ds es hr ht a D W V hW hV
    obtain ⟨U, hU, hUm, hUr, hUd, hUg⟩ := realCanonicalOrdinaryDeformation hRange r ds hr a W hW
    obtain ⟨U', hU', hU'm, hU'r, hU'd, hU'g⟩ := realCanonicalOrdinaryDeformation hRange t es ht (-a) V hV
    obtain ⟨σ, _, hInt⟩ := realUnequalOrdinaryFamily (E := ℂ × ℂ) (a := a) h D parameterDiskProduct
      (fun u => U u.1) (fun u => U' u.1) Prod.snd isOpen_parameterDiskProduct differentiable_snd
      (fun u => (hUr u.1).1) (fun u => (hU'r u.1).1)
      (fun u => (hUr u.1).2.1.continuous) (fun u => (hU'r u.1).2.1.continuous)
      (joint_family_differentiable hUd) (joint_family_differentiable hU'd)
      (joint_family_gauge hUg) (joint_family_gauge hU'g)
    exact ⟨U, U', σ, hU, hU', fun z _ => ⟨hUm z, hU'm z⟩,
      fun z hz => ⟨hReverse r ds hr a z hz.2 (hUm z), hReverse t es ht (-a) z hz.2 (hU'm z)⟩,
      hInt.mono fun u hu => ⟨⟨hu.1, mem_univ _⟩, hu.2⟩⟩
  · intro r _ ds es hr ht a D W V Φ hW hV
    obtain ⟨U, hU, hUm, hUr, hUd, hUg⟩ := realCanonicalOrdinaryDeformation hRange r ds hr a W hW
    obtain ⟨U', hU', hU'm, hU'r, hU'd, hU'g⟩ := realCanonicalOrdinaryDeformation hRange r es ht (-a) V hV
    obtain ⟨σ, _, hInt⟩ := realLocalEqualFamily (r := r) (E := ℂ × ℂ) a D parameterDiskProduct
      (fun u => U u.1) (fun u => U' u.1) Prod.snd Φ isOpen_parameterDiskProduct differentiable_snd
      (fun u => (hUr u.1).1) (fun u => (hU'r u.1).1)
      (fun u => (hUr u.1).2.1.continuous) (fun u => (hU'r u.1).2.1.continuous)
      (joint_family_differentiable hUd) (joint_family_differentiable hU'd)
      (joint_family_gauge hUg) (joint_family_gauge hU'g)
    exact ⟨U, U', σ, hU, hU', fun z _ => ⟨hUm z, hU'm z⟩,
      fun z hz => ⟨hReverse r ds hr a z hz.2 (hUm z), hReverse r es ht (-a) z hz.2 (hU'm z)⟩,
      hInt.mono fun u hu => ⟨⟨hu.1, mem_univ _⟩, hu.2⟩⟩

/-- If the ascending character models are contained in the original block models, the
canonical coefficient families satisfy the joint holomorphy premise for the exact tests. -/
theorem realOrdinaryHolomorphicTestFamilies_of_ascending
    (hRange : RealUniformCanonicalRangePremise)
    (hReverse : ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ a : ℝˣ,
      realUniformWhittakerModel r (ascendingExpand ds) a ≤ realWhittakerModel r ds a) :
    RealOrdinaryHolomorphicTestFamiliesStatement := by
  have h := realOrdinaryHolomorphicTestFamiliesOn_of_ascending univ hRange fun r ds hr a z _ =>
    hReverse r _ ((realRank_deformBlocks ds z).trans hr) a
  exact ⟨fun r t hlt ds es hr ht a D W V hW hV => (h.1 r t hlt ds es hr ht a D W V hW hV).of_univ,
    fun r hp ds es hr ht a D W V Φ hW hV => (h.2 r hp ds es hr ht a D W V Φ hW hV).of_univ⟩

end Langlands.Global.RankinSelbergGlobal.RealBlockParameters
