import Langlands.Representation.Plancherel.RationalUniversalTensorFinitenessProof
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetFinitenessStatement
import Langlands.Representation.Plancherel.UnramifiedRationalCoefficientAlgebra
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Aubert.General.UnramifiedInducedTrace
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! Admissibility of the actual universal tensor and conjugate induced pieces. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe uL uI uH uV u

section UniversalTensor

variable {L : Type uL} [Group L] [TopologicalSpace L]
  [LocallyCompactSpace L] [NonarchimedeanGroup L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
  [IsNoetherianRing (unramifiedRegularFunctions ν)]
  (hν : ∀ i, Continuous (ν i))
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance tensorAdmissibilityAddCommGroup (V : Type*) [AddCommGroup V] [Module ℂ V] :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] V) := TensorProduct.addCommGroup

include hν in
/-- Compact fixed-space scalar extension, compact-open cofinality and the
Noetherian property give all-open admissibility of the actual universal tensor. -/
theorem isAdmissible_universalUnramifiedRepresentation
    (σ : Representation ℂ L E) (hσ : IsAdmissible σ) :
    IsAdmissible (universalUnramifiedRepresentation ν σ) := by
  refine ⟨isSmooth_universalUnramifiedRepresentation_of_continuous ν hν σ hσ.1, ?_⟩
  intro K
  obtain ⟨J, hJ, hJK⟩ := compactOpenSubgroupBasis L (K : Set L) K.mem_nhds_one
  let := (universalTensorFixed_finite_projective ν hν σ J.toSubgroup hJ (hσ.2 J)).1
  exact finite_fixedVectors_of_le (show J.toSubgroup ≤ K.toSubgroup from hJK)

end UniversalTensor

namespace UnramifiedNormalized

section NormalizedInduction

variable {L : Type uL} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
  [IsNoetherianRing (unramifiedRegularFunctions ν)]
  {H : Type uH} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {Q N V : Subgroup H}
  (d : Aubert.General.IsSemidirectDecomposition Q N V)
  (hV : IsClosed (V : Set H)) (hd : Continuous d.projection)
  {E : Type uV} [AddCommGroup E] [Module (unramifiedRegularFunctions ν) E]

include hd

/-- The original coefficient algebra is retained while inflating and applying
the actual positive full-parabolic half normalization. -/
theorem isAdmissible_inducingRepresentation
    (σ : Representation (unramifiedRegularFunctions ν) N E) (hσ : IsAdmissible σ) :
    IsAdmissible (inducingRepresentation ν d hV σ) := by
  apply (isAdmissible_twist_iff _ _
    (inductionCharacter ν V Q hV d.le_normalizer).isOpen_ker).mpr
  apply (isAdmissible_comp_iff_of_open_surjective σ d.projection hd
    (d.isOpenMap_projection hd) ?_).mpr hσ
  intro n
  exact ⟨Subgroup.inclusion d.levi_le n, d.projection_levi n⟩

/-- Full normalized induction over this same coefficient algebra preserves
admissibility when the actual inducing quotient is compact. -/
theorem isAdmissible_inducedRepresentation
    [CompactSpace (Induction.LeftQuotient Q)]
    (σ : Representation (unramifiedRegularFunctions ν) N E) (hσ : IsAdmissible σ) :
    IsAdmissible (inducedRepresentation ν d hV σ) :=
  Induction.smoothInduced_isAdmissible_of_compactSpace Q _
    (isAdmissible_inducingRepresentation ν d hV hd σ hσ)

end NormalizedInduction
end UnramifiedNormalized

namespace RationalNormalized

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance conjugateAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance conjugatePointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance conjugateFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance rationalConjugateTensorAddCommGroup (V : Type*) [AddCommGroup V] [Module ℂ V] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] V) := TensorProduct.addCommGroup

/-- The complete rational-norm universal tensor is admissible over its actual
Noetherian regular algebra, in the all-open-subgroups convention. -/
theorem universalRepresentation_isAdmissible
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsAdmissible σ) :
    IsAdmissible (universalRepresentation r σ) := by
  let := regularAlgebra_isNoetherianRing r
  let := (isClosed_parabolicLeviPointSubgroup r).locallyCompactSpace
  exact isAdmissible_universalUnramifiedRepresentation _
    (continuous_parabolicLeviRationalNormCharacters r) σ hσ

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance conjugateOutputLocallyCompact : LocallyCompactSpace (outputLeviPoints χ) := by
  have hc : IsClosed (outputLeviPoints χ : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (Dynamic.centralizer χ)
      (Dynamic.Affine.centralizerHom χ)
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
      (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
  exact hc.locallyCompactSpace

variable {N : Subgroup (rationalPoints G)} (hN : N ≤ outputLeviPoints χ)
  (w : rationalPoints G)
  (hw : ∀ x : rationalPoints G,
    x ∈ N ↔ w⁻¹ * x * w ∈ parabolicLeviPointSubgroup p l)

/-- The original B-tensor, acted on through literal conjugation and the
canonical nested-subgroup identification inside the actual output Levi. -/
def conjugateOutputLeviRepresentation
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :
    Representation (RegularAlgebra r) (N.subgroupOf (outputLeviPoints χ))
      (RegularAlgebra r ⊗[ℂ] E) :=
  (universalRepresentation r σ).comp
    ((Aubert.General.subgroupOfContinuousEquiv hN).trans
      (Aubert.General.conjugationEquiv w hw)).toMonoidHom

/-- The same universal coefficient module stays admissible after actual
conjugation; no coefficient algebra for the output Levi is substituted. -/
theorem conjugateOutputLeviRepresentation_isAdmissible
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsAdmissible σ) :
    IsAdmissible (conjugateOutputLeviRepresentation r χ hN w hw σ) :=
  isAdmissible_comp_continuousMulEquiv (universalRepresentation r σ)
    ((Aubert.General.subgroupOfContinuousEquiv hN).trans
      (Aubert.General.conjugationEquiv w hw))
    (universalRepresentation_isAdmissible r σ hσ)

variable {Q V : Subgroup (outputLeviPoints χ)}
  (d : Aubert.General.IsSemidirectDecomposition Q (N.subgroupOf (outputLeviPoints χ)) V)
  (hV : IsClosed (V : Set (outputLeviPoints χ)))

/-- The actual full normalized induction in the literal output Levi of the
conjugate original universal tensor, over the original complete norm algebra. -/
abbrev conjugateOutputInducedRepresentation
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  UnramifiedNormalized.inducedRepresentation (parabolicLeviRationalNormCharacters r)
    d hV (conjugateOutputLeviRepresentation r χ hN w hw σ)

/-- The surviving conjugate induced family has finite fixed modules over the
same B. Conjugate Levi geometry, the continuous semidirect projection and the
compact inducing quotient remain geometric inputs, not finiteness premises. -/
theorem conjugateOutputInducedRepresentation_isAdmissible
    (hd : Continuous d.projection) [CompactSpace (Induction.LeftQuotient Q)]
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsAdmissible σ) :
    IsAdmissible (conjugateOutputInducedRepresentation r χ hN w hw d hV σ) := by
  let := regularAlgebra_isNoetherianRing r
  exact UnramifiedNormalized.isAdmissible_inducedRepresentation
    (parabolicLeviRationalNormCharacters r) d hV hd _
    (conjugateOutputLeviRepresentation_isAdmissible r χ hN w hw σ hσ)

end RationalNormalized
end Langlands.Plancherel
