import Langlands.Global.ArthurTruncation
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicHarishChandraDecomposition
import Langlands.Global.AdelicRelativeCuspidalConstantTerm
import Langlands.Global.AdelicEisensteinParabolicRangeTransport

/-! # Vanishing and invariance of Arthur's alternating constant terms -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSubgroupPoints HarishChandraDecomposition ConstantTermComposition

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

local notation "Δ" => simpleFinset ν hG hi
local notation "J" => Finset (characterLattice T)
local notation "A" => AdelicGroupPoints F G
local notation "U₀(" S ")" => Standard.unipotentHom i ν S

/-- Arthur's alternating sum of constant terms on the interval `R ⊆ P ⊆ S`,
with the signs of the ambient truncation operator. -/
def alternatingConstantTerm (R S : J) (f : A → ℂ) (y : A) : ℂ :=
  ∑ P ∈ S.powerset.filter (R ⊆ ·),
    (-1 : ℂ) ^ ((Δ).card - P.card) * constantTerm F i ν (P : Set (characterLattice T)) f y

omit [Mono i.hom.hom.left] in
private theorem canonical_constantTerm [IsAffine G.X.left] (Q : StandardIndex F G i ν)
    (f : A → ℂ) :
    (StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν).constantTerm Q f =
      constantTerm F i ν Q.val f := by
  let fam := StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
  have he : fam.iU Q ≫ fam.p Q = Standard.unipotentHom i ν Q.val :=
    Standard.unipotentToParabolic_comp i ν Q.val
  funext y
  exact subgroupConstantTerm_eq_of_range_eq _ _ (congrArg SubgroupFunctor.range he) f y

include hν in
private theorem alternatingConstantTerm_eq_sum [IsAffine G.X.left]
    {S : J} (hS : S ⊆ Δ) (R : J) (f : A → ℂ) :
    let fam := StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
    alternatingConstantTerm (ν := ν) hG hi R S f =
      ∑ P ∈ S.powerset.filter (R ⊆ ·), (-1 : ℂ) ^ ((Δ).card - P.card) •
        fam.constantTerm (fam.finsetIndex P) f := by
  intro fam
  funext y
  rw [alternatingConstantTerm, Finset.sum_apply]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hPΔ := (Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1).trans hS
  have hP₀ : (P : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun α hα =>
    (mem_simpleFinset hG hi).mp (hPΔ hα)
  rw [Pi.smul_apply, smul_eq_mul, canonical_constantTerm hG hi hν]
  change _ = (-1 : ℂ) ^ ((Δ).card - P.card) *
    constantTerm F i ν ((P : Set (characterLattice T)) ∩ simpleRelativeRoots i ν) f y
  rw [Set.inter_eq_left.mpr hP₀]

private theorem sum_interval_eq_alternatingSum
    {I : Type u} [DecidableEq I] {M : Type u} [AddCommGroup M] [Module ℂ M]
    {D R S : Finset I} (hRS : R ⊆ S) (hSD : S ⊆ D) (c : Finset I → M) :
    (∑ P ∈ S.powerset.filter (R ⊆ ·), (-1 : ℂ) ^ (D.card - P.card) • c P) =
      (-1 : ℂ) ^ (D.card - S.card) • alternatingSum (fun P => c (R ∪ P)) (S \ R) := by
  rw [← Finset.Icc_eq_filter_powerset, Finset.Icc_eq_image_powerset hRS, Finset.sum_image]
  · unfold alternatingSum
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hPS := Finset.mem_powerset.mp hP
    have hdisj : Disjoint R P := Finset.disjoint_of_subset_right hPS Finset.disjoint_sdiff
    have h₁ : (R ∪ P).card = R.card + P.card := Finset.card_union_of_disjoint hdisj
    have h₂ : (S \ R).card = S.card - R.card := Finset.card_sdiff_of_subset hRS
    have h₃ : ((S \ R) \ P).card = (S \ R).card - P.card := Finset.card_sdiff_of_subset hPS
    have h₄ := Finset.card_le_card hSD
    have h₅ := Finset.card_le_card hPS
    have h₆ := Finset.card_le_card hRS
    have hsign : D.card - (R ∪ P).card = D.card - S.card + ((S \ R) \ P).card := by omega
    rw [hsign, pow_add, smul_smul]
  · intro P hP Q hQ heq
    have hP' := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hP) Finset.disjoint_sdiff
    have hQ' := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hQ) Finset.disjoint_sdiff
    simpa only [Finset.union_sdiff_cancel_left hP', Finset.union_sdiff_cancel_left hQ'] using
      congrArg (fun x => x \ R) heq

private theorem constantTerm_finsetSum [IsAffine G.X.left]
    (fam : StandardParabolicFamily F G) (P : StandardIndex F G fam.i fam.ν)
    {I : Type u} (s : Finset I) (c : I → ℂ) (Q : I → StandardIndex F G fam.i fam.ν)
    (f : ContinuousRationalFunctions F G) :
    fam.constantTerm P (∑ j ∈ s, c j • fam.constantTerm (Q j) (evaluate F G f)) =
      ∑ j ∈ s, c j • fam.constantTerm (fam.interIndex P (Q j)) (evaluate F G f) := by
  let V := SubgroupFunctor.range (fam.iU P ≫ fam.p P)
  let : IsClosed (adelicPoints F G V : Set A) := isClosed_adelicPoints_range F G (fam.iU P ≫ fam.p P)
  let : CompactSpace (RationalQuotient F G V) := fam.compactSpace_radicalRationalQuotient P
  let := rationalQuotientBorelSpace F G V
  simp_rw [← fam.constantTerm_constantTerm P _ f]
  funext x
  change (∫ z : RationalQuotient F G V,
      (∑ j ∈ s, c j • fam.constantTerm (Q j) (evaluate F G f))
        ((Quotient.out z : adelicPoints F G V).val * x)
      ∂normalizedRationalQuotientHaarMeasure F G V) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _]
  · exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  · intro j _
    exact (StandardParabolicFamily.integrable_out_of_isRationalInvariant (fam.continuous_constantTerm _ f)
      (fam.isRationalInvariant_constantTerm P _ f) x).const_mul _

include hν in
/-- A maximal constant term of the alternating sum vanishes when its omitted
simple root belongs to the interval difference. -/
theorem constantTerm_alternatingConstantTerm_eq_zero {R S : J} (hRS : R ⊆ S) (hS : S ⊆ Δ)
    {α : characterLattice T} (hα : α ∈ S \ R) (f : ContinuousRationalFunctions F G) :
    constantTerm F i ν (simpleRelativeRoots i ν \ {α})
      (alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f)) = 0 := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let fam := StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
  let P := fam.omitSimpleRoot α
  change constantTerm F i ν P.val (alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f)) = 0
  rw [← canonical_constantTerm hG hi hν P, alternatingConstantTerm_eq_sum hG hi hν hS R,
    constantTerm_finsetSum fam P, sum_interval_eq_alternatingSum hRS hS]
  change (-1 : ℂ) ^ ((Δ).card - S.card) •
    alternatingSum (fun Q => fam.constantTerm (fam.interIndex P (fam.finsetIndex (R ∪ Q)))
      (evaluate F G f)) (S \ R) = 0
  suffices alternatingSum (fun Q => fam.constantTerm (fam.interIndex P (fam.finsetIndex (R ∪ Q)))
      (evaluate F G f)) (S \ R) = 0 by rw [this, smul_zero]
  refine alternatingSum_eq_zero hα _ fun Q _ => ?_
  congr 1
  apply Subtype.ext
  ext β
  change β ∈ (simpleRelativeRoots i ν \ {α}) ∩
      ((↑(R ∪ insert α Q) : Set (characterLattice T)) ∩ simpleRelativeRoots i ν) ↔
    β ∈ (simpleRelativeRoots i ν \ {α}) ∩
      ((↑(R ∪ Q) : Set (characterLattice T)) ∩ simpleRelativeRoots i ν)
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff,
    Finset.mem_coe, Finset.mem_union, Finset.mem_insert]
  tauto

include hν in
/-- The alternating sum is left invariant under the adelic unipotent radical
of the upper standard parabolic. -/
theorem alternatingConstantTerm_radical_mul {R S : J} (hS : S ⊆ Δ)
    (f : ContinuousRationalFunctions F G) (u : A)
    (hu : u ∈ adelicPoints F G (SubgroupFunctor.range (U₀((S : Set (characterLattice T)))))) (x : A) :
    alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f) (u * x) =
      alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f) x := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let fam := StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
  rw [alternatingConstantTerm_eq_sum hG hi hν hS R]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun P hP => congrArg ((_ : ℂ) • ·) ?_
  let Q := fam.finsetIndex P
  let B := fam.finsetIndex S
  let V := SubgroupFunctor.range (fam.iU Q ≫ fam.p Q)
  have hQB : Q ≤ B := fun α hα => ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1 hα.1, hα.2⟩
  let : IsClosed (adelicPoints F G V : Set A) := isClosed_adelicPoints_range F G (fam.iU Q ≫ fam.p Q)
  let := fam.compactSpace_radicalRationalQuotient Q
  have hB : B.val = (S : Set (characterLattice T)) := Set.inter_eq_left.mpr fun α hα =>
    (mem_simpleFinset hG hi).mp (hS hα)
  have huB : u ∈ adelicPoints F G (SubgroupFunctor.range (fam.iU B ≫ fam.p B)) := by
    change u ∈ adelicPoints F G (SubgroupFunctor.range
      (Standard.unipotentToParabolic i ν B.val ≫ Standard.parabolicHom i ν B.val))
    rwa [Standard.unipotentToParabolic_comp, hB]
  have huQ : u ∈ adelicPoints F G V := (fam.radical_le_of_le hQB) _ huB
  have heq (y : A) : fam.constantTerm Q (evaluate F G f) y = normalizedConstantTerm F G V f y :=
    (normalizedConstantTerm_range_eq_subgroupConstantTerm F G (fam.iU Q ≫ fam.p Q) f y).symm
  rw [heq, heq]
  exact normalizedConstantTerm_subgroup_mul F G V f ⟨u, huQ⟩ x

include hν in
/-- The alternating sum is invariant under the rational points of any standard radical. -/
theorem alternatingConstantTerm_isRationalInvariant {R S : J} (hS : S ⊆ Δ)
    (P : StandardIndex F G i ν) (f : ContinuousRationalFunctions F G) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsRationalInvariant F G (SubgroupFunctor.range (U₀(P.val)))
      (alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let fam := StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
  have he : fam.iU P ≫ fam.p P = Standard.unipotentHom i ν P.val :=
    Standard.unipotentToParabolic_comp i ν P.val
  change IsRationalInvariant F G (SubgroupFunctor.range (U₀(P.val))) _
  rw [← he, alternatingConstantTerm_eq_sum hG hi hν hS R]
  intro c hc x
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun Q _ => congrArg ((_ : ℂ) • ·) ?_
  exact fam.isRationalInvariant_constantTerm P (fam.finsetIndex Q) f c hc x

/-- Cancellation along maximal parabolics omitting a root of the interval
difference, and adelic and rational unipotent invariance. -/
def ArthurAlternatingConstantTermStatement : Prop :=
  ∀ R S : J, R ⊆ S → S ⊆ Δ → ∀ f : ContinuousRationalFunctions F G,
    let g := alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f)
    (∀ α ∈ S \ R, constantTerm F i ν (simpleRelativeRoots i ν \ {α}) g = 0) ∧
    (∀ u ∈ adelicPoints F G (SubgroupFunctor.range (U₀((S : Set (characterLattice T))))),
      ∀ x, g (u * x) = g x) ∧
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    ∀ P : StandardIndex F G i ν, IsRationalInvariant F G (SubgroupFunctor.range (U₀(P.val))) g

include hν in
theorem arthurAlternatingConstantTerm : ArthurAlternatingConstantTermStatement (ν := ν) hG hi := by
  intro R S hRS hS f
  refine ⟨?_, ?_, ?_⟩
  · intro α hα
    exact constantTerm_alternatingConstantTerm_eq_zero hG hi hν hRS hS hα f
  · intro u hu x
    exact alternatingConstantTerm_radical_mul hG hi hν hS f u hu x
  · intro P
    exact alternatingConstantTerm_isRationalInvariant hG hi hν hS P f

end Langlands.Global.ArthurTruncation
