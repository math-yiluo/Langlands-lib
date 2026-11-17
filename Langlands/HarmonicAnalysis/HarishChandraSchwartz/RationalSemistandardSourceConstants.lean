import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.Representation.Plancherel.RationalPlancherelConstantFinite
import Langlands.Representation.Plancherel.RationalSourceGammaAmbientHaar
import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.GroupScheme.Rational.SemistandardWeylTransporters
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.BruhatTits.SpecialCompact.Properties

/-! # Actual source constants for intrinsic semistandard spectral indices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G)

/-- An actual cocharacter presentation of the entire intrinsic all-test triple.
It is auxiliary input, never a coordinate of the spectral index. -/
structure CocharacterPresentation (p : SemistandardSpectralIndex i) where
  cocharacter : cocharacterLattice S
  index_eq : SemistandardSpectralIndex.ofCocharacter hG cocharacter = p

namespace CocharacterPresentation

/-- Conditional choice uses exactly the published intrinsic dynamic coverage target. -/
def ofCoverage (h : SemistandardSpectralDynamicCoverageStatement.{u})
    (hi : IsMaximalSplitTorus i) (p : SemistandardSpectralIndex i) :
    CocharacterPresentation hG p :=
  ⟨Classical.choose (h F G hG S i hi p), Classical.choose_spec (h F G hG S i hi p)⟩

variable {hG} {p : SemistandardSpectralIndex i} (r : CocharacterPresentation hG p)

/-- The original morphism into the ambient group used by the scalar package. -/
abbrev hom : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G :=
  CommGroupScheme.groupHom r.cocharacter ≫ i

theorem parabolic_eq : Dynamic.parabolic r.hom = p.parabolic :=
  congrArg SemistandardSpectralIndex.parabolic r.index_eq

theorem levi_eq : Dynamic.centralizer r.hom = p.levi :=
  congrArg SemistandardSpectralIndex.levi r.index_eq

theorem radical_eq : Dynamic.unipotent r.hom = p.radical :=
  congrArg SemistandardSpectralIndex.radical r.index_eq

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

/-- The actual centralizer scheme is a model of this exact intrinsic Levi. -/
def leviModel : LeviModel p where
  scheme := parameterScheme r.hom
  inclusion := Dynamic.Affine.centralizerHom r.hom
  represents := by
    rw [← r.levi_eq]
    exact Dynamic.Affine.isRepresentedBy_centralizerHom r.hom
  closed := Dynamic.Affine.isClosedSubgroup_centralizerHom r.hom
  reductive := parameterScheme_isConnectedReductive r.hom hG

/-- The dynamic and intrinsic literal point subgroups agree inside the ambient group. -/
def literalLeviHomeomorph : DynamicOppositeStandardIntertwining.levi r.hom ≃ₜ* levi p where
  toMulEquiv := MulEquiv.subgroupCongr
    (congrArg (fun M : SubgroupFunctor G => M.carrier (Over.mk (𝟙 _))) r.levi_eq)
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem literalLeviHomeomorph_coe (x : DynamicOppositeStandardIntertwining.levi r.hom) :
    (r.literalLeviHomeomorph x : rationalPoints G) = (x : rationalPoints G) := rfl

end CocharacterPresentation

section SourceConstants

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

namespace SourceConstants

variable {hG} {p : SemistandardSpectralIndex i} (r : CocharacterPresentation hG p)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

/-- The actual common-compact source gamma, with its original Haar normalization. -/
def gamma : ℝ≥0∞ := RationalDynamicSource.gamma r.hom K hK

/-- The actual source product of rank-one constants divided by source gamma. -/
def c : ℝ≥0∞ := RationalDynamicSource.plancherelConstant i r.cocharacter K hK

def gammaReal : ℝ := RationalDynamicSource.gammaReal r.hom K hK

def cReal : ℝ := RationalDynamicSource.plancherelConstantReal i r.cocharacter K hK

/-- Finiteness and nonvanishing of the actual gamma are proved by the source Haar theory. -/
theorem gamma_pos_ne_top : 0 < gamma r K hK ∧ gamma r K hK ≠ ⊤ := by
  let := hG.smooth
  obtain ⟨hz, ht⟩ := RationalDynamicSource.gamma_ne_zero_ne_top_of_smooth K hK r.hom
  exact ⟨pos_iff_ne_zero.mpr hz, ht⟩

theorem gammaReal_pos : 0 < gammaReal r K hK := by
  let := hG.smooth
  exact RationalDynamicSource.gammaReal_pos_of_smooth K hK r.hom

/-- Actual splitness, not an arbitrary positive scalar, supplies the finite rank-one product. -/
theorem c_pos_ne_top (hi : IsMaximalSplitTorus i) :
    0 < c r K hK ∧ c r K hK ≠ ⊤ := by
  let := hG.smooth
  let := hG.connectedSpace
  exact RationalDynamicSource.plancherelConstant_pos_ne_top i r.cocharacter K hK
    hi.isSplitSubtorus.1

theorem cReal_pos (hi : IsMaximalSplitTorus i) : 0 < cReal r K hK := by
  let := hG.smooth
  let := hG.connectedSpace
  exact RationalDynamicSource.plancherelConstantReal_pos_of_isSplitTorus
    i r.cocharacter K hK hi.isSplitSubtorus.1

/-- The exact unquotiented VI.3/VII.2 coefficient. Every cardinal is an actual
geometric carrier; geometric finiteness is needed by the positivity theorem. -/
def unquotientedWeight : ℝ :=
  ((cReal r K hK) ^ 2)⁻¹ * (gammaReal r K hK)⁻¹ *
    ((Nat.card (semistandardLeviRelativeWeylSubgroup i p.toLevi) : ℝ) /
      ((Nat.card (relativeWeylGroup i) : ℝ) *
        (Nat.card (SemistandardSpectralParabolicFiber i p.toLevi) : ℝ)))

/-- Positivity consumes exactly the separately owned geometric fiber-finiteness
statement; ambient and Levi Weyl finiteness follow from published reductive theory. -/
theorem unquotientedWeight_pos (hi : IsMaximalSplitTorus i)
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) :
    0 < unquotientedWeight r K hK := by
  let := hG.finite_relativeWeylGroup i hi
  obtain ⟨hP, hnP⟩ := hfin F G hG S i hi p.toLevi
  let := hP
  let := hnP
  have hW : (0 : ℝ) < Nat.card (relativeWeylGroup i) := by
    exact_mod_cast Nat.card_pos
  have hM : (0 : ℝ) < Nat.card (semistandardLeviRelativeWeylSubgroup i p.toLevi) := by
    exact_mod_cast Nat.card_pos
  have hpar : (0 : ℝ) < Nat.card (SemistandardSpectralParabolicFiber i p.toLevi) := by
    exact_mod_cast Nat.card_pos
  exact mul_pos
    (mul_pos (inv_pos.mpr (sq_pos_of_pos (cReal_pos r K hK hi)))
      (inv_pos.mpr (gammaReal_pos r K hK)))
    (div_pos hM (mul_pos hW hpar))

end SourceConstants

/-- The actual common-Levi source constants must agree for all semistandard
parabolics, at the displayed common source-special compact. The target does
not assume any comparison or positivity conclusion. -/
def SourceConstantParabolicIndependenceStatement : Prop :=
  IsMaximalSplitTorus i →
  ∀ (nu : cocharacterLattice S), IsGenericCocharacter i nu →
    ∀ (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))),
      BruhatTits.SpecialCompact.SpecialCompactProperties F i nu
        (K : Subgroup (rationalPoints G)) →
      ∀ (p q : SemistandardSpectralIndex i)
        (r : CocharacterPresentation hG p) (s : CocharacterPresentation hG q),
        p.levi = q.levi →
          SourceConstants.gamma r K hK = SourceConstants.gamma s K hK ∧
          SourceConstants.c r K hK = SourceConstants.c s K hK

end SourceConstants

end Langlands.HarishChandraSchwartz.RationalSemistandard
