import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket
import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceStatement

/-! # The intrinsic semistandard coefficient fiber of the actual comparison -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types true

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.CoefficientFiber

open ActualCommonLeviCoherence DynamicCommonLeviComposition

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {p : SemistandardSpectralIndex i}
  {hG : IsConnectedReductive G}
  (r : CocharacterPresentation hG p) (d : CompactData p)
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hχ : Dynamic.centralizer χ = p.levi)

set_option hygiene false in
local notation "H" => rationalPoints G

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem parabolic_eq :
    DynamicOppositeStandardIntertwining.parabolic r.hom = parabolic p :=
  congrArg (fun P : SubgroupFunctor G => P.carrier (Over.mk (𝟙 _))) r.parabolic_eq

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem radical_eq :
    DynamicOppositeStandardIntertwining.radical r.hom = radical p :=
  congrArg (fun U : SubgroupFunctor G => U.carrier (Over.mk (𝟙 _))) r.radical_eq

/-- The intrinsic parabolic presented over a cocharacter with the same
all-test Levi. Its compact factorization is exactly that of the intrinsic index. -/
def comparisonParabolic : ParabolicPresentation χ d.compact where
  cocharacter := r.hom
  centralizer_eq := r.levi_eq.trans hχ.symm
  iwasawa := by
    intro g
    obtain ⟨x, k, hx⟩ := d.factorization g
    exact ⟨⟨x, (parabolic_eq r).symm ▸ x.property⟩, k, hx⟩

include hχ in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The two actual Levi subgroups are identical inside the ambient rational
points, in the inverse-conjugation convention at the identity point. -/
theorem leviMembership (x : H) :
    x ∈ levi p ↔ (1 : H)⁻¹ * x * 1 ∈ DynamicOppositeStandardIntertwining.levi χ := by
  have he := congrArg (fun L : SubgroupFunctor G => L.carrier (Over.mk (𝟙 _))) hχ
  simp only [inv_one, one_mul, mul_one, DynamicOppositeStandardIntertwining.levi, he]

/-- The actual inducing object on the intrinsic Levi, pulled back along the
identity of its point subgroup with the dynamic one. -/
abbrev intrinsicInducing (A : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi χ)) :=
  (conjugationFunctor 1 (leviMembership χ hχ)).obj A

set_option hygiene false in
local notation "D₀" => commonDecomposition χ r.hom (r.levi_eq.trans hχ.symm)
set_option hygiene false in
local notation "D₁" => decomposition p
set_option hygiene false in
local notation "hU₀" => DynamicOppositeStandardIntertwining.radical_isClosed r.hom
set_option hygiene false in
local notation "hU₁" => isClosed_radical p
set_option hygiene false in
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular r.hom hG
set_option hygiene false in
local notation "hδ₁" => radical_isUnimodular hG r

/-- The source-normalized positive Levi coefficient fiber goes to the
intrinsic coefficient fiber by identity translation and the published
value-preserving normalization comparison. -/
def fiberEquiv (A : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi χ)) :
    (leviProductInducedCoefficientObject D₀ hU₀ A).representation.Equiv
      (productInducedCoefficientObject D₁ hU₁ (intrinsicInducing χ hχ A)).representation := by
  let P := comparisonParabolic r d χ hχ
  letI := ActualCommonLeviTensor.quotientCompact d.compact d.isCompact r.hom P.iwasawa
  letI := Induction.compactSpace_leftQuotient_of_compact_representatives
    (parabolic p) d.isCompact (fun x => by
      obtain ⟨q, k, hx⟩ := d.factorization x
      exact ⟨q, q.property, k, k.property, hx⟩)
  have hp : ∀ x : H, x ∈ parabolic p ↔
      (1 : H)⁻¹ * x * 1 ∈ DynamicOppositeStandardIntertwining.parabolic r.hom := by
    intro x
    simp only [inv_one, one_mul, mul_one, parabolic_eq r]
  have hu : ∀ x : H, x ∈ radical p ↔
      (1 : H)⁻¹ * x * 1 ∈ DynamicOppositeStandardIntertwining.radical r.hom := by
    intro x
    simp only [inv_one, one_mul, mul_one, radical_eq r]
  exact (CoefficientConjugation.leviCoefficientLeftTranslation D₀ D₁ 1 hp
    (leviMembership χ hχ) hu hU₀ hU₁ hδ₀ hδ₁ A).trans
      (productInducedCoefficientLeviEquiv D₁ hU₁ (intrinsicInducing χ hχ A) hδ₁).symm

end Langlands.HarishChandraSchwartz.RationalSemistandard.CoefficientFiber
