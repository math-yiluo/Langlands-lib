import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicStandardUnipotentProduct
import Langlands.Global.EisensteinConstantTerm.Points

/-! # Maximal-parabolic constant terms of relatively cuspidal functions -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicSubgroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {U V W : SubgroupFunctor G}
  [hW : IsClosed (adelicPoints F G W : Set (AdelicGroupPoints F G))]
  [hV : IsClosed (adelicPoints F G V : Set (AdelicGroupPoints F G))]
  [CompactSpace (RationalQuotient F G W)] [CompactSpace (RationalQuotient F G V)]

local notation "A" => AdelicGroupPoints F G
local notation "G[" D "]" => adelicPoints F G D
local notation "Q[" D "]" => RationalQuotient F G D
local notation "Γ[" D "]" => rationalSubgroup F G D
local notation "μ[" D "]" => normalizedRationalQuotientHaarMeasure F G D

local instance : LocallyCompactSpace G[V] := hV.locallyCompactSpace
local instance : LocallyCompactSpace G[W] := hW.locallyCompactSpace
local instance : BorelSpace Q[V] := rationalQuotientBorelSpace F G V
local instance : BorelSpace Q[W] := rationalQuotientBorelSpace F G W

/-- If `V = U W` on actual adelic points and both subgroups are normalized by `V`, then
on continuous left `U(𝔸)`-invariant functions with left `V(F)` invariance, the averages
along `V` and `W` coincide. -/
theorem integral_eq_of_normal_product (hWV : W ≤ V) (hWn : W.IsNormalizedBy V)
    (hUn : U.IsNormalizedBy V)
    (hprod : ∀ v : G[V], ∃ u : G[U], ∃ w : G[W], v.val = u.val * w.val)
    (f : A → ℂ) (hf : Continuous f)
    (hfU : ∀ u : G[U], ∀ x, f (u.val * x) = f x)
    (hfR : ∀ r : Γ[V], ∀ x, f (r.val.val * x) = f x)
    (g : A) :
    (∫ q : Q[V], f ((Quotient.out q : G[V]).val * g) ∂μ[V]) =
      ∫ q : Q[W], f ((Quotient.out q : G[W]).val * g) ∂μ[W] := by
  let Γ := Γ[V]
  let Δ := Γ[W]
  let j := adelicInclusion F G hWV
  let ν := μ[V]
  let m := μ[W]
  have hj : Δ ≤ Γ.comap j := rationalSubgroup_le_comap_adelicInclusion F G hWV
  have hjc : Continuous j := continuous_subtype_val.subtype_mk _
  have hΓ : IsDiscrete (Γ : Set G[V]) := isDiscrete_rationalSubgroup F G V
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  let := LeftCosetSpace.isFiniteMeasureOnCompacts_count Γ hΓ
  let : (Measure.count : Measure Γ).IsHaarMeasure :=
    { toIsOpenPosMeasure := ⟨fun _ _ hs => Measure.count_ne_zero hs⟩ }
  let : IsProbabilityMeasure m :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G W
  let : IsProbabilityMeasure ν :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let : ν.Regular := (compactCompatibleNormalizedRationalQuotientMeasure F G V).property.2.regular
  have hconj := LeftCosetSpace.subgroupAverageConjugation Γ Δ j hj m (by
    rintro ⟨_, q, rfl⟩
    let a := adelicNormalizerConj F G hWn (rational F G V q⁻¹)
    have ha := adelicNormalizerConj_mem_rationalSubgroup_iff F G hWn q⁻¹
    refine ⟨a, ha, measurePreserving_rationalQuotientAutomorphism F G W a ha, fun w => ?_⟩
    apply Subtype.ext
    change (a w : A) = (rational F G V q : A)⁻¹ * w * (rational F G V q : A)
    simp [a])
  let fV : Q[V] → ℂ := LeftCosetSpace.lift Γ (fun v : G[V] => f (v.val * g)) (fun r v => by
    rw [Subgroup.coe_mul, mul_assoc]
    exact hfR r _)
  let fW : Q[W] → ℂ := LeftCosetSpace.lift Δ (fun w : G[W] => f (w.val * g)) (fun r w => by
    rw [Subgroup.coe_mul, mul_assoc]
    exact hfR ⟨j r.val, hj r.2⟩ _)
  have hfV : Continuous fV :=
    (LeftCosetSpace.continuous_iff Γ).mpr (hf.comp (continuous_subtype_val.mul continuous_const))
  have hVout (q : Q[V]) : f ((Quotient.out q : G[V]).val * g) = fV q :=
    congrArg fV (Quotient.out_eq q)
  have hWout (q : Q[W]) : f ((Quotient.out q : G[W]).val * g) = fW q :=
    congrArg fW (Quotient.out_eq q)
  let avg := LeftCosetSpace.compactSubgroupAverage Γ Δ j hj m hconj fV
  have hAvg : (∫ q, avg q ∂ν) = ∫ q, fV q ∂ν :=
    LeftCosetSpace.integral_compactSubgroupAverage Γ Δ j hj hjc m hconj
      (Γ.isClosed_of_isDiscrete hΓ) Measure.count ν
      (measurePreserving_rightTranslate_of_compactRationalQuotient F G V) hfV
  have hconst (q : Q[V]) : avg q = ∫ t, fW t ∂m := by
    obtain ⟨v, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
    obtain ⟨u, w, hv⟩ := hprod v
    change LeftCosetSpace.compactSubgroupAverage Γ Δ j hj m hconj fV
      (LeftCosetSpace.mk Γ v) = _
    rw [LeftCosetSpace.compactSubgroupAverage_mk]
    let e := LeftCosetSpace.rightTranslateHomeomorph Δ w
    have hpoint : LeftCosetSpace.subgroupFiberEval Γ Δ j hj fV v = fW ∘ e := by
      funext t
      obtain ⟨z, rfl⟩ := LeftCosetSpace.mk_surjective Δ t
      change f ((z.val * v.val) * g) = f ((z.val * w.val) * g)
      let u' : G[U] := ⟨z.val * u.val * z.val⁻¹, hUn _ _ _ (hWV _ z.2) u.2⟩
      have hmul : (z.val * (u.val * w.val)) * g = u'.val * ((z.val * w.val) * g) := by
        dsimp [u']
        group
      rw [hv, hmul, hfU u']
    rw [hpoint]
    exact (measurePreserving_rightTranslate_of_compactRationalQuotient F G W w).integral_comp
      e.measurableEmbedding _
  simp only [hVout, hWout]
  rw [← hAvg]
  simp [hconst, m]

end Langlands.Global.AdelicSubgroupPoints

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "A" => AdelicGroupPoints F G
local notation "rad(" P ")" => SubgroupFunctor.range (𝓕.iU P ≫ 𝓕.p P)

/-- The index of the maximal standard parabolic omitting a given simple root. -/
def omitSimpleRoot (α : characterLattice 𝓕.T) : Idx := ⟨Δ \ {α}, sdiff_subset⟩

/-- The index obtained by removing a simple root from the Levi index of `P`. -/
def removeSimpleRoot (P : Idx) (α : characterLattice 𝓕.T) : Idx :=
  ⟨P.val ∩ (𝓕.omitSimpleRoot α).val, inter_subset_left.trans P.2⟩

omit [NumberField F] in
theorem removeSimpleRoot_lt (P : Idx) {α : characterLattice 𝓕.T} (hα : α ∈ P.val) :
    𝓕.removeSimpleRoot P α < P := by
  refine lt_of_le_of_ne inter_subset_left fun h => ?_
  have h' : α ∈ (𝓕.removeSimpleRoot P α).val := h.symm ▸ hα
  exact h'.2.2 rfl

omit [NumberField F] in
private theorem radical_le_minimalParabolic (P : Idx) :
    rad(P) ≤ SubgroupFunctor.range (𝓕.p ⟨∅, empty_subset _⟩) := by
  let B : Idx := ⟨∅, empty_subset _⟩
  refine (𝓕.radical_le_of_le (Q := B) (P := P) (empty_subset _)).trans ?_
  rw [𝓕.range_radical_eq_standardUnipotent, (𝓕.isCompatible B).parabolic_eq]
  exact standardUnipotent_le_standardParabolic 𝓕.i 𝓕.ν _

/-- The rational points of each standard radical lie in the rational minimal parabolic. -/
theorem radical_rationalImage_le_minimalParabolic (P : Idx) :
    rationalImage F (𝓕.iU P ≫ 𝓕.p P) ≤ rationalImage F (𝓕.p ⟨∅, empty_subset _⟩) := by
  rintro _ ⟨q, rfl⟩
  let B : Idx := ⟨∅, empty_subset _⟩
  obtain ⟨v, hv⟩ := 𝓕.radical_le_minimalParabolic P _
    (show (𝓕.U P).affinePointsTarget (𝓕.iU P ≫ 𝓕.p P) (CommAlgCat.of F F) q ∈ rad(P).carrier _
      from ⟨q, rfl⟩)
  change (𝓕.P B).affinePointsTarget (𝓕.p B) (CommAlgCat.of F F) v = _ at hv
  refine (mem_rationalImage_iff _ _).mpr ⟨v, ?_⟩
  change map F (𝓕.P B) G (𝓕.p B) (rational F (𝓕.P B) v) =
    map F (𝓕.U P) G (𝓕.iU P ≫ 𝓕.p P) (rational F (𝓕.U P) q)
  rw [map_rational, map_rational, hv]

/-- The adelic minimal parabolic normalizes each actual standard radical. -/
theorem minimalParabolic_adelicImage_le_normalizer_radical (P : Idx) :
    let B : Idx := ⟨∅, empty_subset _⟩
    (map F (𝓕.P B) G (𝓕.p B)).toMonoidHom.range ≤
      Subgroup.normalizer ((map F (𝓕.U P) G (𝓕.iU P ≫ 𝓕.p P)).toMonoidHom.range : Set A) := by
  intro B
  let S := (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))
  change (SubgroupFunctor.range (𝓕.p B)).carrier S ≤
    Subgroup.normalizer ((rad(P)).carrier S : Set A)
  rw [Subgroup.le_normalizer_iff]
  intro p hp u hu
  have hBP : B ≤ P := empty_subset _
  have hp' := ((𝓕.le_iff_range_le B P).mp hBP) S hp
  rw [(𝓕.isCompatible P).parabolic_eq] at hp'
  rw [𝓕.range_radical_eq_standardUnipotent] at hu ⊢
  exact StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hp' hu

/-- For a continuous function invariant by `P₀(F)` and `U_P(𝔸)`, the constant term along
the maximal ambient parabolic omitting `α` equals the relative constant term along
the standard parabolic obtained by removing `α` from `P`. -/
def AdelicRelativeCuspidalConstantTermStatement : Prop :=
  ∀ (P : Idx) (α : characterLattice 𝓕.T), α ∈ P.val →
  ∀ f : A → ℂ, Continuous f →
  (∀ r ∈ rationalImage F (𝓕.p ⟨∅, empty_subset _⟩), ∀ x, f (r * x) = f x) →
  (∀ u : AdelicGroupPoints F (𝓕.U P), ∀ x, f (map F (𝓕.U P) G (𝓕.iU P ≫ 𝓕.p P) u * x) = f x) →
  𝓕.constantTerm (𝓕.omitSimpleRoot α) f = 𝓕.constantTerm (𝓕.removeSimpleRoot P α) f

theorem adelicRelativeCuspidalConstantTerm : AdelicRelativeCuspidalConstantTermStatement 𝓕 := by
  open AdelicSubgroupPoints in
  intro P α _ f hf hfR hfU
  let M := 𝓕.omitSimpleRoot α
  let Q := 𝓕.removeSimpleRoot P α
  have hQP : Q ≤ P := inter_subset_left
  have hQM : Q ≤ M := inter_subset_right
  let : IsClosed (adelicPoints F G rad(M) : Set A) :=
    isClosed_adelicPoints_range F G (𝓕.iU M ≫ 𝓕.p M)
  let : IsClosed (adelicPoints F G rad(Q) : Set A) :=
    isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let := 𝓕.compactSpace_radicalRationalQuotient M
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  have hprod (x : adelicPoints F G rad(Q)) :
      ∃ u : adelicPoints F G rad(P), ∃ w : adelicPoints F G rad(M), x.val = u.val * w.val := by
    have h := StandardConstantTerm.standardUnipotentProduct F G 𝓕.T 𝓕.i 𝓕.ν
      𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic P.val M.val P.2 M.2
    obtain ⟨x, hx⟩ := x
    change x ∈ (rad(Q)).carrier _ at hx
    rw [𝓕.range_radical_eq_standardUnipotent] at hx
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.mp (h _ hx)
    refine ⟨⟨u, ?_⟩, ⟨w, ?_⟩, huw.symm⟩
    · change u ∈ (rad(P)).carrier _
      rwa [𝓕.range_radical_eq_standardUnipotent]
    · change w ∈ (rad(M)).carrier _
      rwa [𝓕.range_radical_eq_standardUnipotent]
  have hUf (u : adelicPoints F G rad(P)) (x : A) : f (u.val * x) = f x := by
    obtain ⟨v, rfl⟩ := adelicRangeMap_surjective F (𝓕.iU P ≫ 𝓕.p P) u
    exact hfU v x
  have hRf (r : rationalSubgroup F G rad(Q)) (x : A) : f (r.val.val * x) = f x :=
    hfR _ (𝓕.radical_rationalImage_le_minimalParabolic Q
      ((mem_rationalSubgroup_range_iff (𝓕.iU Q ≫ 𝓕.p Q) r.val).mp r.2)) x
  funext g
  exact (integral_eq_of_normal_product (𝓕.radical_le_of_le hQM)
    (𝓕.radical_isNormalizedBy_of_le hQM) (𝓕.radical_isNormalizedBy_of_le hQP)
    hprod f hf hUf hRf g).symm

/-- Relative cuspidality implies vanishing of every maximal ambient constant term whose
omitted root belongs to the Levi index. -/
theorem maximal_constantTerm_eq_zero_of_isCuspidalAlong
    (P : Idx) {α : characterLattice 𝓕.T} (hα : α ∈ P.val)
    {f : A → ℂ} (hf : Continuous f)
    (hfR : ∀ r ∈ rationalImage F (𝓕.p ⟨∅, empty_subset _⟩), ∀ x, f (r * x) = f x)
    (hfU : ∀ u : AdelicGroupPoints F (𝓕.U P), ∀ x,
      f (map F (𝓕.U P) G (𝓕.iU P ≫ 𝓕.p P) u * x) = f x)
    (hc : 𝓕.IsCuspidalAlong P f) :
    𝓕.constantTerm (𝓕.omitSimpleRoot α) f = 0 :=
  (𝓕.adelicRelativeCuspidalConstantTerm P α hα f hf hfR hfU).trans
    (hc _ (𝓕.removeSimpleRoot_lt P hα))

end Langlands.Global.StandardParabolicFamily
