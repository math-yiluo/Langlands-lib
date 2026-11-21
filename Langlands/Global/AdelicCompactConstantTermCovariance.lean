import Langlands.Automorphic.GroupSchemeConstantTermConjugation
import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Compact-radical constant terms of continuous rational-invariant functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G Q U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]

section Comparison

variable (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "V" => SubgroupFunctor.range j
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "Quot" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "ν" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V

local instance closedAdelicRangeForConstantTerm :
    IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) :=
  AdelicSubgroupPoints.isClosed_adelicPoints_range F G j

local instance constantTermQuotientBorel : BorelSpace Quot :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F G V

/-- The representative-based integral equals the descended constant-term integral
on continuous rational-invariant functions. -/
theorem subgroupConstantTerm_eq_continuousConstantTerm
    (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) :
    subgroupConstantTerm F j (evaluate F G f) g = constantTerm F G V ν f g := by
  unfold subgroupConstantTerm constantTerm
  congr 1
  funext x
  exact congrArg (constantTermIntegrand F G V f g) (Quotient.out_eq x)

/-- On a compact radical quotient, the actual constant term is a continuous
function of the external adelic argument. -/
theorem continuous_subgroupConstantTerm
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]
    (f : ContinuousRationalFunctions F G) :
    Continuous (subgroupConstantTerm F j (evaluate F G f)) := by
  let : IsProbabilityMeasure ν :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  rw [show subgroupConstantTerm F j (evaluate F G f) =
    constantTerm F G V ν f from funext (subgroupConstantTerm_eq_continuousConstantTerm j f)]
  have hcont : Continuous (fun x : AdelicGroupPoints F G × Quot =>
      constantTermIntegrand F G V f x.1 x.2) := by
    rw [← (IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)).continuous_comp_iff]
    change Continuous (fun x : AdelicGroupPoints F G × AdelicSubgroupPoints.adelicPoints F G V =>
      evaluate F G f ((x.2 : AdelicGroupPoints F G) * x.1))
    exact f.property.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have hIntegral : Continuous (fun g =>
      ∫ x in Set.univ, constantTermIntegrand F G V f g x ∂ν) :=
    continuous_parametric_integral_of_continuous hcont isCompact_univ
  change Continuous (fun g => ∫ x, constantTermIntegrand F G V f g x ∂ν)
  simpa only [Measure.restrict_univ] using hIntegral

end Comparison

section Normalizer

variable (q : Q ⟶ G) (iU : U ⟶ Q) [IsClosedImmersion (iU ≫ q).hom.hom.left]

local notation "V" => SubgroupFunctor.range (iU ≫ q)

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
  [IsClosedImmersion (iU ≫ q).hom.hom.left] in
private theorem radical_comap_innerIso_le_of_normal
    (hN : (SubgroupFunctor.range iU).IsNormal)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Q.X) :
    V ≤ SubgroupFunctor.comap (G.innerIso (x ≫ q.hom.hom)).hom V := by
  intro T z hz
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  rw [SubgroupFunctor.mem_comap]
  rw [Grp.comp_hom_hom, Category.assoc, Category.assoc, ← Grp.comp_hom_hom,
    comp_innerIso_hom_comp q x, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc]
  have h : (y ≫ iU.hom.hom) ≫ (Q.innerIso x).hom.hom.hom ∈
      (SubgroupFunctor.range iU).carrier T := by
    rw [comp_innerIso_hom]
    exact hN T _ _ trivial ⟨y, rfl⟩
  obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp h
  exact SubgroupFunctor.mem_range.mpr ⟨y', by rw [Grp.comp_hom_hom, ← Category.assoc, hy']⟩

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
  [IsClosedImmersion (iU ≫ q).hom.hom.left] in
private theorem radical_comap_innerIso_eq_of_normal
    (hN : (SubgroupFunctor.range iU).IsNormal)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Q.X) :
    SubgroupFunctor.comap (G.innerIso (x ≫ q.hom.hom)).hom V = V := by
  apply le_antisymm ?_ (radical_comap_innerIso_le_of_normal q iU hN x)
  have h := radical_comap_innerIso_le_of_normal q iU hN x⁻¹
  rw [GrpObj.inv_comp, innerIso_inv_hom] at h
  intro T z hz
  have h' := h T ((SubgroupFunctor.mem_comap).mp hz)
  rw [SubgroupFunctor.mem_comap, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
    Grp.id_hom_hom, Category.comp_id] at h'
  exact h'

/-- A rational point of the ambient parabolic acts trivially on the left
of the constant term along its normal radical. -/
theorem subgroupConstantTerm_rational_parabolic_mul
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (f : ContinuousRationalFunctions F G)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Q.X) (g : AdelicGroupPoints F G) :
    subgroupConstantTerm F (iU ≫ q) (evaluate F G f)
        (innerAdelicPoint F G (x ≫ q.hom.hom) * g) =
      subgroupConstantTerm F (iU ≫ q) (evaluate F G f) g := by
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ q)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iU ≫ q)
      hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  rw [subgroupConstantTerm_eq_continuousConstantTerm, subgroupConstantTerm_eq_continuousConstantTerm]
  have h := constantTerm_comap_innerIso F G (x ≫ q.hom.hom) V V
    (radical_comap_innerIso_eq_of_normal q iU hU.1.isNormal x).symm f
    (innerAdelicPoint F G (x ≫ q.hom.hom) * g)
  rwa [inv_mul_cancel_left] at h

end Normalizer

/-- The compact unipotent constant term of a continuous rational-invariant
function is continuous and invariant under the rational points of the
parabolic. -/
def CompactConstantTermCovarianceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G Q U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
    (q : Q ⟶ G) (iU : U ⟶ Q) [IsClosedImmersion (iU ≫ q).hom.hom.left],
    LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ f : ContinuousRationalFunctions F G,
      Continuous (subgroupConstantTerm F (iU ≫ q) (evaluate F G f)) ∧
      ∀ (x : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Q.X) (g : AdelicGroupPoints F G),
        subgroupConstantTerm F (iU ≫ q) (evaluate F G f)
            (innerAdelicPoint F G (x ≫ q.hom.hom) * g) =
          subgroupConstantTerm F (iU ≫ q) (evaluate F G f) g

theorem compactConstantTermCovariance : CompactConstantTermCovarianceStatement.{u} := by
  intro F _ _ G Q U _ _ _ q iU _ hU f
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (SubgroupFunctor.range (iU ≫ q))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iU ≫ q)
      hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  exact ⟨continuous_subgroupConstantTerm (iU ≫ q) f,
    subgroupConstantTerm_rational_parabolic_mul q iU hU f⟩

end Langlands.Global.AdelicGroupPoints
