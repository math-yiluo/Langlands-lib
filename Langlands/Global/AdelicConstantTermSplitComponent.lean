import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicExponentPolynomials
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Rational.Characters

/-! # Split-component shifts commute with constant terms on intermediate parabolic quotients

For `Q ≤ P`, the commutator of an `A_P` point and a `U_Q` point lies in `U_P`.
Thus an input already left `U_P`-invariant has the required commutation identity
without any change of variables on `U_Q(F) \ U_Q(𝔸)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "rad(" J ")" => SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)

omit [NumberField F] in
/-- A point in the center of the actual standard Levi commutes with all points of the
containing parabolic modulo its actual radical. The assertion is on every test scheme. -/
theorem commutator_mem_radical_of_splitComponent (P : Idx)
    (X : Over (Spec (CommRingCat.of F))) (a : X ⟶ (𝓕.A P).toGrp.X)
    {x : X ⟶ G.X} (hx : x ∈ (SubgroupFunctor.range (𝓕.p P)).carrier X) :
    let b := a ≫ (𝓕.a P ≫ 𝓕.l P ≫ 𝓕.p P).hom.hom
    x * b * x⁻¹ * b⁻¹ ∈ rad(P).carrier X := by
  dsimp only
  set b : X ⟶ G.X := a ≫ (𝓕.a P ≫ 𝓕.l P ≫ 𝓕.p P).hom.hom with hb
  obtain ⟨z, hz, hP, hM⟩ := (𝓕.isCompatible P).realization
  let χ := CommGroupScheme.groupHom z ≫ 𝓕.i
  have hu : rad(P) = Dynamic.unipotent χ := by
    rw [𝓕.range_radical_eq_standardUnipotent]
    exact ((standardCocharacter F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit
      𝓕.ν 𝓕.generic P.1 P.2).2 z hz).2.2
  rw [hu]
  have hbM : b ∈ (SubgroupFunctor.range (𝓕.l P ≫ 𝓕.p P)).carrier X := by
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨a ≫ (𝓕.a P).hom.hom, ?_⟩
    simp only [hb, Grp.comp_hom_hom, Category.assoc]
  let c : (Dynamic.centralizer χ).carrier X := ⟨b, hM ▸ hbM⟩
  let y : (Dynamic.parabolic χ).carrier X := ⟨x, hP ▸ hx⟩
  let cP := Subgroup.inclusion (Dynamic.centralizer_le_parabolic χ X) c
  have hc : Commute (Dynamic.limitHom χ X y) c := by
    apply Subtype.ext
    have hzM : (Dynamic.limitHom χ X y : X ⟶ G.X) ∈
        (SubgroupFunctor.range (𝓕.l P ≫ 𝓕.p P)).carrier X :=
      hM.symm ▸ (Dynamic.limitHom χ X y).2
    obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hzM
    have hc := (commute_of_mem_center
      ((𝓕.isCompatible P).splitComponent.1.2 X a) m).symm
    have hmap := hc.map (((yonedaGrp.map (𝓕.l P ≫ 𝓕.p P)).app (op X)).hom)
    change (m ≫ (𝓕.l P ≫ 𝓕.p P).hom.hom) *
        ((a ≫ (𝓕.a P).hom.hom) ≫ (𝓕.l P ≫ 𝓕.p P).hom.hom) =
      ((a ≫ (𝓕.a P).hom.hom) ≫ (𝓕.l P ≫ 𝓕.p P).hom.hom) *
        (m ≫ (𝓕.l P ≫ 𝓕.p P).hom.hom) at hmap
    rw [hm] at hmap
    change (Dynamic.limitHom χ X y : X ⟶ G.X) * b = b *
      (Dynamic.limitHom χ X y : X ⟶ G.X)
    simpa only [hb, Grp.comp_hom_hom, Category.assoc] using hmap
  change ((y * cP * y⁻¹ * cP⁻¹ : (Dynamic.parabolic χ).carrier X) : X ⟶ G.X) ∈
    (Dynamic.unipotent χ).carrier X
  rw [← Subgroup.mem_subgroupOf, ← Dynamic.ker_limitHom, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, cP, Dynamic.limitHom_inclusion]
  rw [hc.eq, mul_inv_cancel_right, mul_inv_cancel]

/-- Left invariance by the adelic radical of `P`, as a predicate on ambient functions. -/
def IsRadicalInvariant (P : Idx) (f : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ (n : AdelicSubgroupPoints.adelicPoints F G rad(P)) (g : AdelicGroupPoints F G),
    f ((n : AdelicGroupPoints F G) * g) = f g

/-- For a radical-invariant function, changing the order of a nested radical point and
an outer split-component shift does not change the value. -/
theorem IsRadicalInvariant.unnormalizedAction_radical_mul {Q P : Idx} (hQP : Q ≤ P)
    {f : AdelicGroupPoints F G → ℂ} (hf : 𝓕.IsRadicalInvariant P f)
    (a : 𝓕.positiveSplitComponent P)
    (n : AdelicSubgroupPoints.adelicPoints F G rad(Q)) (g : AdelicGroupPoints F G) :
    𝓕.unnormalizedAction P a f ((n : AdelicGroupPoints F G) * g) =
      f ((n : AdelicGroupPoints F G) * (map F (𝓕.P P) G (𝓕.p P) a * g)) := by
  obtain ⟨a', -, ha'⟩ := a.2
  have hnQ : (n : AdelicGroupPoints F G) ∈
      (SubgroupFunctor.range (𝓕.p Q)).carrier _ := by
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp n.2
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨v ≫ (𝓕.iU Q).hom.hom, ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using hv
  have hnP := (𝓕.le_iff_range_le Q P).mp hQP _ hnQ
  have hcomm := 𝓕.commutator_mem_radical_of_splitComponent P _ a' hnP
  let b := map F (𝓕.P P) G (𝓕.p P) a
  have haG : b = map F (𝓕.A P).toGrp G (𝓕.a P ≫ 𝓕.l P ≫ 𝓕.p P) a' := by
    change map F (𝓕.A P).toGrp (𝓕.P P) (𝓕.a P ≫ 𝓕.l P) a' =
      (a : AdelicGroupPoints F (𝓕.P P)) at ha'
    change map F (𝓕.P P) G (𝓕.p P) a = _
    rw [← ha', ← map_comp_apply_of_hom, Category.assoc]
  let u : AdelicSubgroupPoints.adelicPoints F G rad(P) :=
    ⟨(n : AdelicGroupPoints F G) * b * (n : AdelicGroupPoints F G)⁻¹ * b⁻¹,
      by rw [haG]; exact hcomm⟩
  have heq : (n : AdelicGroupPoints F G) * (b * g) =
      (u : AdelicGroupPoints F G) * (b * ((n : AdelicGroupPoints F G) * g)) := by
    dsimp only [u]
    group
  change f (b * ((n : AdelicGroupPoints F G) * g)) = f ((n : AdelicGroupPoints F G) * (b * g))
  rw [heq, hf u]

/-- Taking the constant term along `Q ≤ P` commutes with plain translation by the positive
split component of `P`, on functions already left invariant by the adelic radical of `P`. -/
theorem constantTerm_unnormalizedAction_of_radicalInvariant
    {Q P : Idx} (hQP : Q ≤ P) (a : 𝓕.positiveSplitComponent P)
    {f : AdelicGroupPoints F G → ℂ} (hf : 𝓕.IsRadicalInvariant P f) :
    𝓕.constantTerm Q (𝓕.unnormalizedAction P a f) =
      𝓕.unnormalizedAction P a (𝓕.constantTerm Q f) := by
  funext g
  unfold constantTerm AdelicGroupPoints.subgroupConstantTerm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (fun q => IsRadicalInvariant.unnormalizedAction_radical_mul 𝓕 hQP hf a (Quotient.out q) g)

/-- Positive split-component shifts preserve radical invariance. -/
theorem IsRadicalInvariant.unnormalizedAction {P : Idx} {f : AdelicGroupPoints F G → ℂ}
    (hf : 𝓕.IsRadicalInvariant P f) (a : 𝓕.positiveSplitComponent P) :
    𝓕.IsRadicalInvariant P (𝓕.unnormalizedAction P a f) := by
  intro n g
  let b := map F (𝓕.P P) G (𝓕.p P) a
  have hb : b ∈ (SubgroupFunctor.range (𝓕.p P)).carrier _ :=
    SubgroupFunctor.mem_range.mpr ⟨(a : AdelicGroupPoints F (𝓕.P P)), rfl⟩
  have h : b * (n : AdelicGroupPoints F G) * b⁻¹ ∈
      AdelicSubgroupPoints.adelicPoints F G rad(P) := by
    generalize hn : (n : AdelicGroupPoints F G) = x
    have hx : x ∈ rad(P).carrier _ := hn ▸ n.2
    change b * x * b⁻¹ ∈ rad(P).carrier _
    rw [𝓕.range_radical_eq_standardUnipotent] at hx ⊢
    rw [(𝓕.isCompatible P).parabolic_eq] at hb
    exact StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hb hx
  have heq : b * ((n : AdelicGroupPoints F G) * g) =
      (b * (n : AdelicGroupPoints F G) * b⁻¹) * (b * g) := by group
  change f (b * ((n : AdelicGroupPoints F G) * g)) = f (b * g)
  rw [heq]
  exact hf ⟨_, h⟩ _

/-- Raw exponent differences preserve radical invariance. -/
theorem IsRadicalInvariant.unnormalizedExponentDifference {P : Idx}
    {f : AdelicGroupPoints F G → ℂ} (hf : 𝓕.IsRadicalInvariant P f)
    (a : 𝓕.positiveSplitComponent P) (lam : ComplexCharacterParameter F (𝓕.P P)) :
    𝓕.IsRadicalInvariant P (𝓕.unnormalizedExponentDifference P lam a f) := by
  intro n g
  have ht := IsRadicalInvariant.unnormalizedAction 𝓕 hf a
  simp only [unnormalizedExponentDifference_apply, hf n g, ht n g]

/-- Absolute integrability of the chosen-representative constant term at every ambient point.
In applications this follows from continuity and the appropriate rational invariance. -/
def HasIntegrableConstantTerm (Q : Idx) (f : AdelicGroupPoints F G → ℂ) : Prop :=
  haveI := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  ∀ g, Integrable (fun q : AdelicSubgroupPoints.RationalQuotient F G rad(Q) =>
    f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G rad(Q)) :
      AdelicGroupPoints F G) * g))
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G rad(Q))

/-- Raw exponent differences commute across the nested constant term. No preservation of the
rational lattice by the split-component shift is used. -/
theorem constantTerm_unnormalizedExponentDifference {Q P : Idx} (hQP : Q ≤ P)
    {f : AdelicGroupPoints F G → ℂ} (hf : 𝓕.IsRadicalInvariant P f)
    (a : 𝓕.positiveSplitComponent P) (lam : ComplexCharacterParameter F (𝓕.P P))
    (hi : 𝓕.HasIntegrableConstantTerm Q f) :
    𝓕.constantTerm Q (𝓕.unnormalizedExponentDifference P lam a f) =
      𝓕.unnormalizedExponentDifference P lam a (𝓕.constantTerm Q f) := by
  funext g
  rw [unnormalizedExponentDifference_apply]
  have hshift := congrFun (𝓕.constantTerm_unnormalizedAction_of_radicalInvariant hQP a hf) g
  change 𝓕.constantTerm Q (𝓕.unnormalizedAction P a f) g =
    𝓕.constantTerm Q f (map F (𝓕.P P) G (𝓕.p P) a * g) at hshift
  rw [unnormalizedAction, ← hshift]
  let U := rad(Q)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  let b := map F (𝓕.P P) G (𝓕.p P) a
  let c := parameterPower F (𝓕.P P) lam a
  let Fg (x : AdelicGroupPoints F G) (q : AdelicSubgroupPoints.RationalQuotient F G U) :=
    f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G U) : AdelicGroupPoints F G) * x)
  have hF : ∀ x, Integrable (Fg x) m := hi
  have heq (q : AdelicSubgroupPoints.RationalQuotient F G U) :
      𝓕.unnormalizedAction P a f
        (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G U) : AdelicGroupPoints F G) * g) =
      Fg (b * g) q := IsRadicalInvariant.unnormalizedAction_radical_mul 𝓕 hQP hf a (Quotient.out q) g
  unfold constantTerm AdelicGroupPoints.subgroupConstantTerm
  simp_rw [unnormalizedExponentDifference_apply, heq]
  change (∫ q, Fg (b * g) q - c * Fg g q ∂m) =
    (∫ q, Fg (b * g) q ∂m) - c * ∫ q, Fg g q ∂m
  rw [integral_sub (hF _) ((hF _).const_mul _), integral_const_mul]

/-- The integrability premise is preserved by a difference of split-component translates. -/
theorem HasIntegrableConstantTerm.unnormalizedExponentDifference {Q P : Idx} (hQP : Q ≤ P)
    {f : AdelicGroupPoints F G → ℂ} (hi : 𝓕.HasIntegrableConstantTerm Q f)
    (hf : 𝓕.IsRadicalInvariant P f) (a : 𝓕.positiveSplitComponent P)
    (lam : ComplexCharacterParameter F (𝓕.P P)) :
    𝓕.HasIntegrableConstantTerm Q (𝓕.unnormalizedExponentDifference P lam a f) := by
  let U := rad(Q)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  let b := map F (𝓕.P P) G (𝓕.p P) a
  let c := parameterPower F (𝓕.P P) lam a
  let Fg (x : AdelicGroupPoints F G) (q : AdelicSubgroupPoints.RationalQuotient F G U) :=
    f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G U) : AdelicGroupPoints F G) * x)
  have hF : ∀ x, Integrable (Fg x) m := hi
  intro g
  refine ((hF (b * g)).sub ((hF g).const_mul c)).congr (Filter.Eventually.of_forall fun q => ?_)
  change Fg (b * g) q - c * Fg g q = 𝓕.unnormalizedExponentDifference P lam a f
    (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G U) : AdelicGroupPoints F G) * g)
  rw [unnormalizedExponentDifference_apply,
    IsRadicalInvariant.unnormalizedAction_radical_mul 𝓕 hQP hf a (Quotient.out q) g]

/-- The constant term intertwines any finite ordered product of raw differences in
split-component directions of `P`, using the actual subgroup `U_Q` for `Q ≤ P`. -/
theorem constantTerm_list_prod_unnormalizedExponentDifference {Q P : Idx} (hQP : Q ≤ P)
    {f : AdelicGroupPoints F G → ℂ} (hf : 𝓕.IsRadicalInvariant P f)
    (hi : 𝓕.HasIntegrableConstantTerm Q f)
    (xs : List (𝓕.positiveSplitComponent P × ComplexCharacterParameter F (𝓕.P P))) :
    𝓕.constantTerm Q ((xs.map (fun x : 𝓕.positiveSplitComponent P × ComplexCharacterParameter F
      (𝓕.P P) => 𝓕.unnormalizedExponentDifference P x.2 x.1)).prod f) =
    (xs.map (fun x : 𝓕.positiveSplitComponent P × ComplexCharacterParameter F (𝓕.P P) =>
      𝓕.unnormalizedExponentDifference P x.2 x.1)).prod (𝓕.constantTerm Q f) := by
  induction xs using List.reverseRecOn generalizing f with
  | nil => simp
  | append_singleton xs x ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, Module.End.mul_apply]
    rw [ih (IsRadicalInvariant.unnormalizedExponentDifference 𝓕 hf x.1 x.2)
      (HasIntegrableConstantTerm.unnormalizedExponentDifference 𝓕 hQP hi hf x.1 x.2),
      𝓕.constantTerm_unnormalizedExponentDifference hQP hf x.1 x.2 hi]

/-- A constant term of a continuous rational-invariant input is invariant by its radical. -/
theorem isRadicalInvariant_constantTerm (P : Idx) (f : ContinuousRationalFunctions F G) :
    𝓕.IsRadicalInvariant P (𝓕.constantTerm P (evaluate F G f)) := by
  open AdelicSubgroupPoints in
  let : IsClosed (adelicPoints F G rad(P) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU P ≫ 𝓕.p P)
  let := 𝓕.compactSpace_radicalRationalQuotient P
  intro n g
  change subgroupConstantTerm F (𝓕.iU P ≫ 𝓕.p P) (evaluate F G f)
      ((n : AdelicGroupPoints F G) * g) =
    subgroupConstantTerm F (𝓕.iU P ≫ 𝓕.p P) (evaluate F G f) g
  rw [← AdelicSubgroupPoints.normalizedConstantTerm_range_eq_subgroupConstantTerm,
    ← AdelicSubgroupPoints.normalizedConstantTerm_range_eq_subgroupConstantTerm]
  exact AdelicSubgroupPoints.normalizedConstantTerm_subgroup_mul F G rad(P) f n g

/-- For `Q ≤ P`, the `P` constant term of a continuous rational-invariant input
has absolutely convergent `Q` constant term at every ambient point. -/
theorem hasIntegrableConstantTerm_constantTerm_of_le {Q P : Idx} (hQP : Q ≤ P)
    (f : ContinuousRationalFunctions F G) :
    𝓕.HasIntegrableConstantTerm Q (𝓕.constantTerm P (evaluate F G f)) := by
  open AdelicSubgroupPoints in
  let U := rad(P)
  let V := rad(Q)
  let : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU P ≫ 𝓕.p P)
  let : IsClosed (adelicPoints F G V : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let := 𝓕.compactSpace_radicalRationalQuotient P
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  let := rationalQuotientBorelSpace F G V
  let m := normalizedRationalQuotientHaarMeasure F G V
  let : IsProbabilityMeasure m := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  intro g
  let b (n : adelicPoints F G V) := normalizedConstantTerm F G U f ((n : AdelicGroupPoints F G) * g)
  have hb (gam : AdelicSubgroupPoints.rationalSubgroup F G V)
      (n : adelicPoints F G V) : b (gam.val * n) = b n := by
    obtain ⟨q, hq⟩ := gam.2
    have hq' : AdelicGroupPoints.rational F G q.val = (gam.val : AdelicGroupPoints F G) :=
      congrArg (fun v : adelicPoints F G V => (v : AdelicGroupPoints F G)) hq
    change normalizedConstantTerm F G U f (((gam.val : AdelicGroupPoints F G) * n) * g) = _
    rw [mul_assoc, ← hq']
    exact normalizedConstantTerm_rationalNormalizer_mul F G U
      (𝓕.radical_isNormalizedBy_of_le hQP) q f _
  let B := LeftCosetSpace.lift (AdelicSubgroupPoints.rationalSubgroup F G V) b hb
  have hB : Continuous B := LeftCosetSpace.continuous_lift _ _ _
    ((continuous_normalizedConstantTerm F G U f).comp (continuous_subtype_val.mul_const g))
  have hI := hB.integrable_of_hasCompactSupport («μ» := m) (HasCompactSupport.of_compactSpace _)
  refine hI.congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G V)
      (Quotient.out x) = x := Quotient.out_eq x
  change B x = 𝓕.constantTerm P (evaluate F G f)
    (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g)
  calc
    B x = b (Quotient.out x) := congrArg B hx.symm
    _ = _ := normalizedConstantTerm_range_eq_subgroupConstantTerm F G (𝓕.iU P ≫ 𝓕.p P) f _

end Langlands.Global.StandardParabolicFamily
