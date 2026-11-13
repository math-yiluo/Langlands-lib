import Langlands.Representation.LanglandsClassification.OppositeUntwistLeviRoots
import Langlands.Representation.LanglandsClassification.OppositeJacquetUntwistSelectionReduction
import Langlands.Representation.Exponents.NormalizedTemperedStandardReductionProof
import Langlands.Representation.Exponents.NestedLeviJacquetExponents
import Langlands.Representation.Exponents.UnramifiedJacquetExponentTwist
import Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityReduction
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Langlands.Representation.Exponents.MaximalLeviExponentTransport
import Langlands.Representation.Exponents.JacquetExponentRestriction
import Langlands.Representation.Geometric.LeviConjugatePiece
import Langlands.Representation.Intertwining.CentralActionQuotientFiniteness
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws
import Langlands.Representation.Plancherel.SplitTorusNormFormula
import Langlands.Representation.LanglandsClassification.LeviPositiveUnramifiedParameter
import Langlands.Representation.LanglandsClassification.UnramifiedFullParameter
import Langlands.GroupScheme.Rational.IntrinsicRootCone
import Langlands.GroupScheme.Rational.ParabolicRootPresentationIndependenceProof
import Langlands.GroupScheme.Rational.ParabolicCorootLiftUniqueness
import Langlands.GroupScheme.Rational.RestrictedSimpleRootCones
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Temperedness of unitary untwists from the opposite exponent criterion -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

section Cone

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {P M G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- Let `u` be a nonnegative combination of the characters in `S` lying in the real
span of a subset `K`. If a cocharacter `ζ` vanishes on `K` and is positive on
`S \ K`, then only characters of `K` occur in `u`. If moreover the negatives of
the characters of `K` are positive roots of a presentation, then minus the
restriction of `u` lies in the presentation's nonnegative cone. -/
theorem neg_restrict_mem_nonnegCone_of_mem_hull
    (r : ParabolicRootPresentation p l a)
    (S K : Set (characterLattice r.data.T)) (ζ : cocharacterLattice r.data.T)
    (hzero : ∀ α ∈ K, latticePairing r.data.T α ζ = 0)
    (hpos : ∀ α ∈ S, α ∉ K → 0 < latticePairing r.data.T α ζ)
    (hneg : ∀ α ∈ S, α ∈ K → -α ∈ positiveRelativeRoots r.data.i r.data.ν)
    {u : Vstar r.data.T}
    (hu : u ∈ PointedCone.hull ℝ
      ((fun α : characterLattice r.data.T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S))
    (hK : u ∈ Submodule.span ℝ
      ((fun α : characterLattice r.data.T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K)) :
    -rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) u ∈
      r.nonnegCone := by
  set L := rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
  set eta : V r.data.T := (1 : ℝ) ⊗ₜ[ℤ] ζ
  have hKeta' : ∀ w ∈ Submodule.span ℝ
      ((fun α : characterLattice r.data.T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K),
      pair r.data.T w eta = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨α, hα, rfl⟩ := hx
      simp [eta, hzero α hα]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  have hKeta := hKeta' u hK
  have key : ∀ w ∈ PointedCone.hull ℝ
      ((fun α : characterLattice r.data.T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S),
      0 ≤ pair r.data.T w eta ∧ (pair r.data.T w eta = 0 → -L w ∈ r.nonnegCone) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨α, hα, rfl⟩ := hx
      have hp : pair r.data.T ((1 : ℝ) ⊗ₜ[ℤ] α) eta = (latticePairing r.data.T α ζ : ℝ) := by
        simp [eta]
      rw [hp]
      by_cases hαK : α ∈ K
      · refine ⟨by simp [hzero α hαK], fun _ => ?_⟩
        have h := r.one_tmul_restrict_mem_nonnegCone (hneg α hα hαK)
        have hL : -L ((1 : ℝ) ⊗ₜ[ℤ] α) = (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ (-α)) := by
          rw [Preadditive.comp_neg, tmul_neg]
          rfl
        rw [hL]
        exact h
      · have h' : (0 : ℝ) < latticePairing r.data.T α ζ := by
          exact_mod_cast hpos α hα hαK
        exact ⟨h'.le, fun h0 => absurd h0 h'.ne'⟩
    | zero => simpa using r.zero_mem_nonnegCone
    | add x y _ _ hx hy =>
      simp only [map_add, LinearMap.add_apply, neg_add]
      refine ⟨add_nonneg hx.1 hy.1, fun h0 => ?_⟩
      have h1 : pair r.data.T x eta = 0 := by linarith [hx.1, hy.1]
      have h2 : pair r.data.T y eta = 0 := by linarith [hx.1, hy.1]
      exact r.add_mem_nonnegCone (hx.2 h1) (hy.2 h2)
    | smul c x _ hx =>
      have hc : (c • x : Vstar r.data.T) = (c : ℝ) • x := rfl
      rw [hc, map_smul, LinearMap.smul_apply, smul_eq_mul, map_smul, ← smul_neg]
      refine ⟨mul_nonneg c.2 hx.1, fun h0 => ?_⟩
      rcases mul_eq_zero.mp h0 with h | h
      · rw [h, zero_smul]
        exact r.zero_mem_nonnegCone
      · exact r.smul_mem_nonnegCone c.2 (hx.2 h)
  exact (key u hu).2 hKeta

end Cone

section NestedInjective

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance untwistCriterionAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)
  (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hmul : IsIso (subgroupMultiplication m n))
  (q : Q ⟶ G) (l : L ⟶ Q) (r : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmulQ : IsIso (subgroupMultiplication l r))
  (pL : PL ⟶ L) (mL : M ⟶ PL) (nL : NL ⟶ PL)
  (hpL : IsParabolicSubgroup pL) (hmL : IsRationalLeviSubgroup mL)
  (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
  (hmulL : IsIso (subgroupMultiplication mL nL))
  (hPQ : pointImage p ≤ pointImage q)
  (hM : mL ≫ pL ≫ l ≫ q = m ≫ p)
  (hPL : pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

include hG hPQ hM hPL in
/-- Every exponent of an inner Jacquet module of a subrepresentation of an outer
Jacquet module is an exponent of the fine ambient Jacquet module, on the same
split component of the common Levi. -/
theorem isNormalizedJacquetExponent_of_nested_injective
    {B : CommGroupScheme (Spec (CommRingCat.of k))} {b : B.toGrp ⟶ M}
    (hb : IsSplitComponent b) (χ : rationalPoints B.toGrp →* ℂˣ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints L))
      (inc : σ ⟶ (leviJacquetFunctor q l r hq hr hl hmulQ).obj π),
      Function.Injective (SmoothRep.hom inc) →
      IsNormalizedJacquetExponent pL mL nL hpL hmL hnL hmulL hb σ χ →
      IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  let : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
  intro σ inc hinc hχ
  rw [isNormalizedJacquetExponent_iff_leviEigencharacter] at hχ ⊢
  let e := Classical.choice
    (leviParabolicTransitivity k G hG P M N Q L U PL NL
      p m n hp hm hn hmul q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL).2
  let F := (leviJacquetFunctor pL mL nL hpL hnL hmL hmulL).map inc ≫ e.inv.app π
  have hF : Function.Injective (SmoothRep.hom F) :=
    (SmoothRep.equivOfIso (e.app π).symm).injective.comp
      (leviJacquetFunctor_map_injective pL mL nL hpL hmL hnL hmulL inc hinc)
  let f := SmoothRep.hom F
  let fB : Representation.IntertwiningMap
      (((leviJacquetFunctor pL mL nL hpL hnL hmL hmulL).obj σ).representation.comp
          (rationalPoints.map b))
      (((leviJacquetFunctor p m n hp hn hm hmul).obj π).representation.comp
        (rationalPoints.map b)) :=
    { toLinearMap := f.toLinearMap
      isIntertwining' t := f.isIntertwining' (rationalPoints.map b t) }
  obtain ⟨d, hd⟩ := hχ
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hd
  apply isGeneralizedEigencharacter_of_map_ne_zero fB χ d hx
  intro h
  change f x = 0 at h
  apply hx0
  exact hF (by simpa only [map_zero] using h)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Exponents along equal split-component maps agree. -/
theorem isNormalizedJacquetExponent_congr_component
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a₁ a₂ : A.toGrp ⟶ M} (h : a₁ = a₂)
    (h₁ : IsSplitComponent a₁) (h₂ : IsSplitComponent a₂)
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent p m n hp hm hn hmul h₁ π χ ↔
      IsNormalizedJacquetExponent p m n hp hm hn hmul h₂ π χ := by
  subst h
  rfl

end NestedInjective


open OppositeStandardJacquetFamily Nesting

set_option maxHeartbeats 4000000 in
theorem oppositeUntwistTemperedCriterion :
    OppositeUntwistTemperedCriterionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D hi hν hmin π x W hH S
  have hGK := isConnectedReductive_levi i ν hG hi hν x.1
  have hfam := leviTorus_neg_families i ν hG hi hν x.1
  have hiK := isMaximalSplitTorus_leviTorus i ν hi x.1
  have hminK := genericMinimalParabolic k _ hGK T (leviTorus i ν x.1) hiK (-ν) hfam.2.1
  have := hGK.isAffineHom
  have := hGK.smooth
  let : TopologicalSpace (rationalPoints (Standard.leviScheme i ν x.1.val)) :=
    RationalPointFamily.pointTopology
  have : LocallyCompactSpace (rationalPoints (Standard.leviScheme i ν x.1.val)) :=
    leviPoints_locallyCompactSpace S.p S.l S.hp S.hl
  have : NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν x.1.val)) :=
    leviPoints_nonarchimedeanGroup S.p S.l S.hp S.hl
  refine (normalizedTemperedStandardReduction k (Standard.leviScheme i ν x.1.val) hGK T
    (leviTorus i ν x.1) (-ν) hiK hfam.2.1 hminK W.untwist).mpr ⟨W.untwist_admissible, ?_⟩
  intro J' ζ' hζ' P' M' A' p' l' a' hp' hl' ha' hP hM hPdyn hMdyn
  have hJ' : J' ⊆ -x.1.val := hfam.1 ▸ hζ'.1
  have hJK : (negIndex i ν hJ').val ⊆ x.1.val := negIndex_subset i ν hJ'
  let φ := testLeviIso i ν hG hi hν p' l' hp' hl' hJ' hM
  have hφ : φ.hom ≫ leviInclusion i ν hG hi hν hJK = l' ≫ p' :=
    testLeviIso_hom_comp i ν hG hi hν p' l' hp' hl' hJ' hM
  let CK := StandardJacquetFamily.component i ν hG hi hν x.1
  let CJ := StandardJacquetFamily.component i ν hG hi hν (negIndex i ν hJ')
  have : IsAffineHom M'.X.hom := hl'.isConnectedReductive.isAffineHom
  obtain ⟨e, he⟩ := IsSplitComponent.exists_iso_comp CJ.ha ha' φ.symm
  let f' : A' ⟶ T := e.inv ≫ Additive.ofMul CJ.g
  have hgJ : CJ.g ≫ leviTorus i ν x.1 = CJ.a ≫ leviInclusion i ν hG hi hν hJK := by
    apply SubgroupFunctor.IsRepresentedBy.hom_ext
      (Standard.isRepresentedBy_leviHom i ν x.1.val)
    rw [Category.assoc, Category.assoc, leviTorus_comp, leviInclusion_comp]
    exact CJ.factor
  have hee : CommGroupScheme.groupHom e.inv ≫ CommGroupScheme.groupHom e.hom = 𝟙 _ := by
    change CommGroupScheme.groupHom (e.inv ≫ e.hom) = _
    rw [e.inv_hom_id]
    rfl
  have hea : CommGroupScheme.groupHom e.inv ≫ CJ.a = a' ≫ φ.hom := by
    have he' : CommGroupScheme.groupHom e.hom ≫ a' ≫ φ.hom = CJ.a := by
      rw [← Category.assoc, he, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    rw [← he', ← Category.assoc, hee, Category.id_comp]
  have hf' : CommGroupScheme.groupHom f' ≫ leviTorus i ν x.1 = a' ≫ l' ≫ p' := by
    change (CommGroupScheme.groupHom e.inv ≫ CJ.g) ≫ leviTorus i ν x.1 = _
    rw [Category.assoc, hgJ, ← Category.assoc, hea, Category.assoc, hφ]
  have hminle : Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ leviTorus i ν x.1) ≤
      SubgroupFunctor.range p' := by
    rw [hP, ← (standardParabolicEndpoints k _ hGK T (leviTorus i ν x.1) hiK (-ν)
      hfam.2.1).1]
    exact ((standardParabolicOrder k _ hGK T (leviTorus i ν x.1) hiK (-ν) hfam.2.1).1
      ∅ J' (Set.empty_subset _) hζ'.1).1.mp (Set.empty_subset _)
  let pres0 : ParabolicRootPresentation p' l' a' :=
    ⟨⟨T, leviTorus i ν x.1, -ν, J', f'⟩,
      { parabolic := hp'
        levi := hl'
        splitComponent := ha'
        maximalSplit := hiK
        generic := hfam.2.1
        subset_simpleRoots := hζ'.1
        parabolic_eq := hP
        levi_eq := hM
        factor_comp := hf'
        minimal := hminK
        minimal_le := hminle
        realization := ⟨ζ', hζ', hPdyn, hMdyn⟩ }⟩
  refine ⟨⟨pres0⟩, ?_⟩
  intro pres U r hr hmul χ hχ
  rw [(parabolicRootPresentationIndependence k _ hGK P' M' A' p' l' a' pres pres0).2.2]
  obtain ⟨y, hyK, hre, hspan⟩ : ∃ y : OppositeStandardJacquetFamily.exponents i ν hG hi hν π,
      y.1.val ⊆ x.1.val ∧
      Plancherel.SplitTorus.normalizedRealPart ha'.isCentralSplitTorus.1.1 χ =
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f')
          (OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D y -
            OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D x) ∧
      OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D y -
          OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D x ∈
        Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' x.1.val) := by
    let : TopologicalSpace (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M) :=
      leviPointTopology (StandardJacquetFamily.datum i ν hG hi hν x.1).l
        (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    have : LocallyCompactSpace (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M) :=
      leviPoints_locallyCompactSpace S.p S.l S.hp S.hl
    have : NonarchimedeanGroup (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M) :=
      leviPoints_nonarchimedeanGroup S.p S.l S.hp S.hl
    let OK := OppositeStandardJacquetFamily.datum i ν hG hi hν x.1
    let OJ := OppositeStandardJacquetFamily.datum i ν hG hi hν (negIndex i ν hJ')
    let ψ := positiveUnramifiedCharacter i ν hG hi hν π x
    let ψa : rationalPoints A'.toGrp →* ℂˣ :=
      ψ.val.toMonoidHom.comp (rationalPoints.map (a' ≫ l' ≫ p'))
    let χs := χ * ψa
    -- `χs` is an exponent of the retwisted unitary untwist, hence of the source.
    have h1 : IsNormalizedJacquetExponent p' l' r hp' hl' hr hmul ha'
        (W.untwist.twist ψ.val.toMonoidHom
          (positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x)) χs :=
      (isNormalizedJacquetExponent_unramifiedTwist_iff p' l' r hp' hl' hr hmul ha' ψ
        W.untwist χs).mpr (by convert hχ using 1; exact mul_inv_cancel_right χ ψa)
    have h2 : IsNormalizedJacquetExponent p' l' r hp' hl' hr hmul ha' W.source χs :=
      (isNormalizedJacquetExponent_iff_of_equiv p' l' r hp' hl' hr hmul ha' _ W.source
        (SmoothRep.equivOfIso W.recovery) χs).mp h1
    -- Pass to the opposite Jacquet module of `π` at the label `-J'`.
    have hPQ : pointImage OJ.p ≤ pointImage OK.p :=
      pointImage_opposite_p_le i ν hG hi hν hJK
    have hOK : OK.l ≫ OK.p = Standard.leviHom i ν x.1.val := datum_l_comp_p i ν hG hi hν x.1
    have hOJ : OJ.l ≫ OJ.p = Standard.leviHom i ν (negIndex i ν hJ').val :=
      datum_l_comp_p i ν hG hi hν _
    have hpK : p' ≫ OK.l ≫ OK.p = p' ≫ Standard.leviHom i ν x.1.val :=
      congrArg (fun g => p' ≫ g) hOK
    have hMcomp : l' ≫ p' ≫ OK.l ≫ OK.p = (φ.hom ≫ OJ.l) ≫ OJ.p := by
      have h1 : l' ≫ p' ≫ OK.l ≫ OK.p = l' ≫ p' ≫ Standard.leviHom i ν x.1.val :=
        congrArg (fun g => l' ≫ g) hpK
      have h2 : (φ.hom ≫ OJ.l) ≫ OJ.p =
          φ.hom ≫ Standard.leviHom i ν (negIndex i ν hJ').val :=
        (Category.assoc _ _ _).trans (congrArg (fun g => φ.hom ≫ g) hOJ)
      rw [h1, h2, ← Category.assoc, ← hφ, Category.assoc, leviInclusion_comp]
    have hPL : pointImage (p' ≫ OK.l ≫ OK.p) = pointImage (OK.l ≫ OK.p) ⊓ pointImage OJ.p := by
      have h := pointImage_comp_leviHom_of_standardParabolic i ν hG hi hν p' hJ' hP
      rw [hpK, hOK]
      exact h
    have h3 := isNormalizedJacquetExponent_of_nested_injective hG OJ.p (φ.hom ≫ OJ.l) OJ.r
      OJ.hp (OJ.hl.iso_comp φ) OJ.hr (isIso_subgroupMultiplication_iso_comp φ OJ.hmul)
      OK.p OK.l OK.r OK.hp OK.hl OK.hr OK.hmul p' l' r hp' hl' hr hmul hPQ hMcomp hPL π ha' χs
      W.source W.inclusion W.inclusion_injective h2
    have he2 : CommGroupScheme.groupHom e.hom ≫ a' ≫ φ.hom = CJ.a := by
      rw [← Category.assoc, he, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    have h4 : IsNormalizedJacquetExponent OJ.p OJ.l OJ.r OJ.hp OJ.hl OJ.hr OJ.hmul CJ.ha π
        (χs.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom))) := by
      rw [isNormalizedJacquetExponent_comp_splitPointsEquiv_iff OJ.p OJ.l OJ.r OJ.hp OJ.hl
        OJ.hr OJ.hmul e he2 CJ.ha (ha'.comp_iso φ) π χs,
        ← isNormalizedJacquetExponent_iso_comp_iff OJ.p OJ.l OJ.r OJ.hp OJ.hl OJ.hr OJ.hmul φ
          (OJ.hl.iso_comp φ) (isIso_subgroupMultiplication_iso_comp φ OJ.hmul)
          (ha'.comp_iso φ) ((ha'.comp_iso φ).comp_iso φ.symm) π χs]
      exact (isNormalizedJacquetExponent_congr_component OJ.p (φ.hom ≫ OJ.l) OJ.r OJ.hp
        (OJ.hl.iso_comp φ) OJ.hr (isIso_subgroupMultiplication_iso_comp φ OJ.hmul) π
        (show (a' ≫ φ.hom) ≫ φ.inv = a' from (Category.assoc _ _ _).trans
          ((congrArg (fun g => a' ≫ g) φ.hom_inv_id).trans (Category.comp_id a'))).symm
        ha' _ χs).mp h3
    let y : OppositeStandardJacquetFamily.exponents i ν hG hi hν π :=
      ⟨negIndex i ν hJ', ⟨χs.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom)), h4⟩⟩
    -- Real parts: `Re χ = Re χs - Re ψa`, computed through the torus `T`.
    have hA' : IsSplitTorus A'.toGrp := ha'.isCentralSplitTorus.1.1
    have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
    have hCJ : IsSplitTorus CJ.A.toGrp := CJ.ha.1.1.1
    have hCK : IsSplitTorus CK.A.toGrp := CK.ha.1.1.1
    have := hA'.isAffineHom
    have := hT.isAffineHom
    have := hCJ.isAffineHom
    have := hCK.isAffineHom
    have : IsAffine A'.X.left := isAffine_of_isAffineHom A'.X.hom
    have : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
    have : IsAffine CJ.A.X.left := isAffine_of_isAffineHom CJ.A.X.hom
    have : IsAffine CK.A.X.left := isAffine_of_isAffineHom CK.A.X.hom
    let : TopologicalSpace (rationalPoints T.toGrp) :=
      Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k T.X
    let : TopologicalSpace (rationalPoints CJ.A.toGrp) :=
      RationalPointFamily.splitComponentPointTopology CJ.ha
    have hTlevi : (rootPresentation i ν hG hi hν x.1).leviTorusHom = leviTorus i ν x.1 := by
      apply SubgroupFunctor.IsRepresentedBy.hom_ext
        (Standard.isRepresentedBy_leviHom i ν x.1.val)
      have h := (rootPresentation i ν hG hi hν x.1).leviTorusHom_comp
      have hlp : (StandardJacquetFamily.datum i ν hG hi hν x.1).l ≫
          (StandardJacquetFamily.datum i ν hG hi hν x.1).p = Standard.leviHom i ν x.1.val :=
        Standard.leviToParabolic_comp i ν x.1.val
      rw [hlp] at h
      exact h.trans (leviTorus_comp i ν x.1).symm
    have hψa : Plancherel.SplitTorus.normalizedRealPart hA' ψa =
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f')
          (OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D x) := by
      rw [← fullRealPart_positiveUnramifiedCharacter i ν hG hi hν π D x]
      have hfT : CommGroupScheme.groupHom f' ≫
          (rootPresentation i ν hG hi hν x.1).leviTorusHom = a' ≫ l' ≫ p' := by
        rw [hTlevi]
        exact hf'
      have hcomp : ψa = (ψ.val.toMonoidHom.comp
          (rationalPoints.map (rootPresentation i ν hG hi hν x.1).leviTorusHom)).comp
            (rationalPoints.map (CommGroupScheme.groupHom f')) := by
        apply MonoidHom.ext
        intro t
        have h2 : rationalPoints.map (a' ≫ l' ≫ p') t =
            rationalPoints.map (rootPresentation i ν hG hi hν x.1).leviTorusHom
              (rationalPoints.map (CommGroupScheme.groupHom f') t) :=
          (congrArg (fun g => rationalPoints.map g t) hfT).symm.trans
            (pointMap_comp_apply _ _ t)
        exact congrArg ψ.val.toMonoidHom h2
      rw [hcomp]
      exact Plancherel.SplitTorus.normalizedRealPart_comp_points hA' hT f'
        (ψ.val.toMonoidHom.comp
          (rationalPoints.map (rootPresentation i ν hG hi hν x.1).leviTorusHom))
        (isOpen_ker_leviUnramifiedTorusCharacter (rootPresentation i ν hG hi hν x.1) ψ)
    have hee' : CommGroupScheme.groupHom e.hom ≫ CommGroupScheme.groupHom e.inv = 𝟙 _ := by
      change CommGroupScheme.groupHom (e.hom ≫ e.inv) = _
      rw [e.hom_inv_id]
      rfl
    have hχs : Plancherel.SplitTorus.normalizedRealPart hA' χs =
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f')
          (OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D y) := by
      have hopen : IsOpen ((χs.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom))).ker :
          Set (rationalPoints CJ.A.toGrp)) :=
        ((isNormalizedJacquetExponent_iff_isOpen_ker_and OJ.p OJ.l OJ.r OJ.hp OJ.hl OJ.hr OJ.hmul
          CJ.ha π _).mp h4).1
      have hcomp : χs = (χs.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom))).comp
          (rationalPoints.map (CommGroupScheme.groupHom e.inv)) := by
        apply MonoidHom.ext
        intro t
        have h : rationalPoints.map (CommGroupScheme.groupHom e.hom)
            (rationalPoints.map (CommGroupScheme.groupHom e.inv) t) = t := by
          rw [← pointMap_comp_apply, hee]
          simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
        exact (congrArg χs h).symm
      have h5 : Plancherel.SplitTorus.normalizedRealPart hA' χs =
          rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv)
            (Plancherel.SplitTorus.normalizedRealPart hCJ
              (χs.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom)))) := by
        conv_lhs => rw [hcomp]
        exact Plancherel.SplitTorus.normalizedRealPart_comp_points hA' hCJ e.inv _ hopen
      have hy : Plancherel.SplitTorus.normalizedRealPart hCJ
          (χs.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom))) =
          rationalCharacterRestrictReal CJ.g
            (OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D y) :=
        (restrict_fullRealPart i ν hG hi hν π D y).symm
      rw [h5, hy, rationalCharacterRestrictReal_comp_apply]
      rfl
    have hre : Plancherel.SplitTorus.normalizedRealPart ha'.isCentralSplitTorus.1.1 χ =
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f')
          (OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D y -
            OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D x) := by
      have hmulRe : Plancherel.SplitTorus.normalizedRealPart hA' χs =
          Plancherel.SplitTorus.normalizedRealPart hA' χ +
            Plancherel.SplitTorus.normalizedRealPart hA' ψa :=
        Plancherel.SplitTorus.normalizedRealPart_mul hA' χ ψa
      rw [map_sub, ← hχs, ← hψa, hmulRe, add_sub_cancel_right]
    refine ⟨y, hJK, hre, ?_⟩
    -- Span: the split component `A_K` of `M_K` lies in `A'`, where `χ` is unitary.
    have := (isConnectedReductive_levi i ν hG hi hν (negIndex i ν hJ')).isAffineHom
    have hgK : CK.g ≫ leviTorus i ν x.1 = CK.a := by
      apply SubgroupFunctor.IsRepresentedBy.hom_ext
        (Standard.isRepresentedBy_leviHom i ν x.1.val)
      rw [Category.assoc, leviTorus_comp]
      exact CK.factor
    have hTJK : leviTorus i ν (negIndex i ν hJ') ≫ leviInclusion i ν hG hi hν hJK =
        leviTorus i ν x.1 := by
      apply SubgroupFunctor.IsRepresentedBy.hom_ext
        (Standard.isRepresentedBy_leviHom i ν x.1.val)
      rw [Category.assoc, leviInclusion_comp, leviTorus_comp, leviTorus_comp]
    have hbc : IsCentral (CK.g ≫ leviTorus i ν (negIndex i ν hJ')) := by
      apply IsCentral.of_comp (mono_leviInclusion i ν hG hi hν hJK)
      rw [Category.assoc, hTJK, hgK]
      exact CK.ha.1.2
    obtain ⟨h0, hh0⟩ := CJ.ha.exists_factor hCK hbc
    have hh0g : h0 ≫ CJ.g = CK.g := by
      have : Mono i.hom.hom := Over.mono_of_mono_left _
      apply Grp.hom_ext
      apply (cancel_mono i.hom.hom).mp
      change ((h0 ≫ CJ.g) ≫ i).hom.hom = (CK.g ≫ i).hom.hom
      rw [Category.assoc, CJ.factor, ← Category.assoc, hh0, Category.assoc, leviTorus_comp]
    let hK : CK.A ⟶ A' := Additive.ofMul h0 ≫ e.hom
    have hKg : CommGroupScheme.groupHom hK ≫ CommGroupScheme.groupHom f' = CK.g := by
      change (h0 ≫ CommGroupScheme.groupHom e.hom) ≫
        (CommGroupScheme.groupHom e.inv ≫ CJ.g) = CK.g
      rw [Category.assoc, ← Category.assoc (CommGroupScheme.groupHom e.hom), hee',
        Category.id_comp, hh0g]
    have hKa : CommGroupScheme.groupHom hK ≫ a' ≫ l' ≫ p' = CK.a := by
      rw [← hf', ← Category.assoc, hKg, hgK]
    have hres := normalizedJacquetExponent_restrict p' l' r hp' hl' hr hmul ha' CK.ha
      (rationalPoints.map (CommGroupScheme.groupHom hK)) (fun t => by
        have h := congrArg (fun g => rationalPoints.map g t) hKa
        simp only [pointMap_comp_apply] at h
        rw [splitComponentPointsMap_val]
        simp only [pointMap_comp_apply]
        exact h) W.untwist χ W.untwist_admissible hχ
    let : TopologicalSpace (rationalPoints CK.A.toGrp) :=
      RationalPointFamily.splitComponentPointTopology CK.ha
    have hwt := (isGeneralizedWeight_iff_isOpen_ker_and _ _ _ W.untwist.isSmooth).mp hres
    have hunit := CentralActionQuotient.eq_of_isGeneralizedEigencharacter_of_scalar _
      (unitaryComponentCharacter i ν hG hi hν π x) (fun b => LinearMap.ext (W.scalar b)) _ hwt.2
    have hzero : Plancherel.SplitTorus.normalizedRealPart hCK
        (χ.comp (rationalPoints.map (CommGroupScheme.groupHom hK))) = 0 := by
      rw [Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff _ _ hwt.1]
      intro t
      rw [hunit]
      exact norm_unitaryComponentCharacter i ν hG hi hν π x t
    have hχopen := ((isNormalizedJacquetExponent_iff_isOpen_ker_and p' l' r hp' hl' hr hmul ha'
      W.untwist χ).mp hχ).1
    have hcompK := Plancherel.SplitTorus.normalizedRealPart_comp_points hCK hA' hK χ hχopen
    have hKrestr : rationalCharacterRestrictReal CK.g
        (OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D y -
          OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D x) = 0 := by
      rw [← hKg, ← rationalCharacterRestrictReal_comp_apply, ← hre, ← hcompK, hzero]
    exact (rootPresentation i ν hG hi hν x.1).mem_selectedRootSpan_of_restrict_eq_zero hKrestr
  obtain ⟨⟨ζK, hζK⟩, -⟩ := standardCocharacter k G hG T i hi ν hν x.1.val x.1.property
  have hneg : ∀ α ∈ simpleRelativeRoots i ν, α ∈ x.1.val →
      -α ∈ positiveRelativeRoots pres0.data.i pres0.data.ν := by
    intro α _ hαK
    apply simpleRelativeRoots_subset_positive
    change -α ∈ simpleRelativeRoots (leviTorus i ν x.1) (-ν)
    rw [hfam.1]
    exact Set.neg_mem_neg.mpr hαK
  have hmem := neg_restrict_mem_nonnegCone_of_mem_hull pres0 (simpleRelativeRoots i ν)
    x.1.val ζK hζK.2.1 hζK.2.2 hneg (hH y hyK hspan) (Submodule.neg_mem _ hspan)
  rw [hre]
  simpa using hmem

end Langlands.Aubert.General.RepresentedParabolic
