import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.GroupScheme.SplitUnipotentQuotientSection
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # The depth-zero reduction map of supplied KP models

For a supplied relative-component model and a supplied quotient of its neutral
special fibre, this module constructs the composite of KP 13.2.6,
`G^0(R) → H(f) → Gred(f)`, computes its kernel and proves its surjectivity
over a Henselian local base with perfect residue field. No model, radical or
quotient existence assertion is made.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace RelativeComponentModelData

/-- Integral sections of the neutral model are identified with their image
`G^0(R)` in the original generic rational points. -/
def neutralSectionsEquiv (D : RelativeComponentModelData R K G) :
    D.neutral.integralSections ≃* D.neutral.integralPoints :=
  MonoidHom.ofInjective D.neutral.integralPointMap_injective

@[simp]
theorem neutralSectionsEquiv_apply (D : RelativeComponentModelData R K G)
    (x : D.neutral.integralSections) :
    (D.neutralSectionsEquiv x : rationalPoints G) = D.neutral.integralPointMap x :=
  rfl

end RelativeComponentModelData

section Local

variable [IsLocalRing R]

local instance neutralSpecialFibre_affineHom (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (pullback.snd D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- The specified projection on residue-field points, `H(f) → Gred(f)`. -/
def projectionPoints :
    rationalPoints D.neutral.specialFibre →* rationalPoints Q.quotient :=
  rationalPoints.map Q.projection

/-- If the projection is the represented fppf quotient by the specified
radical, its kernel on residue-field points is the radical's points. -/
theorem ker_projectionPoints
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    Q.projectionPoints.ker = Q.radicalPoints := by
  ext x
  rw [MonoidHom.mem_ker, radicalPoints, MonoidHom.mem_range]
  have h := mem_range_kernelι_iff Q.projection x
  rw [hQ.2.2.2, SubgroupFunctor.mem_range] at h
  exact h.symm

/-- Over a perfect residue field, the projection is surjective on
residue-field points when the specified radical is a unipotent radical and the
projection is its represented fppf quotient (KP Proposition 2.4.3). -/
theorem projectionPoints_surjective [PerfectField (IsLocalRing.ResidueField R)]
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    Function.Surjective Q.projectionPoints := by
  let : Smooth Q.radical.X.hom := hrad.smooth
  let : IsAffineHom Q.radical.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed _ _ Q.radicalInclusion
      hrad.isClosedSubgroup
  have hsplit : RelativeRoot.IsSplitUnipotent Q.radical :=
    perfectFieldUnipotentSplit _ Q.radical hrad.connectedSpace hrad.isUnipotent
  obtain ⟨s, hs⟩ := HomogeneousQuotient.fppf_section_of_split_unipotent_torsors
    D.neutral.specialFibre Q.radical Q.radicalInclusion
    splitUnipotentAffineTorsorStatement hrad.isClosedSubgroup hsplit
    Q.quotient Q.projection hQ
  intro y
  refine ⟨y ≫ s, ?_⟩
  change (y ≫ s) ≫ Q.projection.hom.hom = y
  rw [Category.assoc, hs, Category.comp_id]

/-- The composite `G^0(R) → H(f) → Gred(f)` of KP 13.2.6, on integral
sections of the supplied neutral model. -/
def reductiveReduction :
    D.neutral.integralSections →* rationalPoints Q.quotient :=
  Q.projectionPoints.comp D.neutral.reduction

/-- The kernel of the composite is the reduction preimage of the radical's
residue-field points. -/
theorem ker_reductiveReduction
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    Q.reductiveReduction.ker = Q.positiveSections := by
  rw [reductiveReduction, ← MonoidHom.comap_ker, Q.ker_projectionPoints hQ]
  rfl

/-- The reduction map on the generic-point image `G^0(R)`. -/
def parahoricReduction :
    D.neutral.integralPoints →* rationalPoints Q.quotient :=
  Q.reductiveReduction.comp D.neutralSectionsEquiv.symm.toMonoidHom

@[simp]
theorem parahoricReduction_neutralSectionsEquiv (x : D.neutral.integralSections) :
    Q.parahoricReduction (D.neutralSectionsEquiv x) = Q.reductiveReduction x := by
  simp [parahoricReduction]

/-- On `G^0(R)`, the kernel of the reduction to the specified quotient is the
subgroup `G(K)^{0+}` of `SpecialFibreQuotientData.positivePoints`. -/
theorem ker_parahoricReduction
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    Q.parahoricReduction.ker = Q.positivePoints.subgroupOf D.neutral.integralPoints := by
  ext g
  obtain ⟨x, rfl⟩ := D.neutralSectionsEquiv.surjective g
  rw [MonoidHom.mem_ker, parahoricReduction_neutralSectionsEquiv, ← MonoidHom.mem_ker,
    Q.ker_reductiveReduction hQ, Subgroup.mem_subgroupOf,
    RelativeComponentModelData.neutralSectionsEquiv_apply, positivePoints,
    Subgroup.mem_map_iff_mem D.neutral.integralPointMap_injective]

end SpecialFibreQuotientData

end Local

section Henselian

variable [HenselianLocalRing R] [PerfectField (IsLocalRing.ResidueField R)]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- Over a Henselian local base with perfect residue field, the composite
`G^0(R) → Gred(f)` is surjective (KP Lemma 8.1.3 and Proposition 2.4.3). -/
theorem reductiveReduction_surjective
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    Function.Surjective Q.reductiveReduction :=
  (Q.projectionPoints_surjective hrad hQ).comp
    (D.neutral.reduction_surjective D.neutral_smooth)

/-- The same surjectivity on the generic-point image `G^0(R)`. -/
theorem parahoricReduction_surjective
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    Function.Surjective Q.parahoricReduction :=
  (Q.reductiveReduction_surjective hrad hQ).comp D.neutralSectionsEquiv.symm.surjective

/-- KP 13.2.6 for the supplied data: reduction identifies the quotient of
`G^0(R)` by the kernel of `parahoricReduction` with `Gred(f)`. That kernel is
`G(K)^{0+} ∩ G^0(R)` by `ker_parahoricReduction`. -/
def depthZeroQuotientEquiv
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    D.neutral.integralPoints ⧸ Q.parahoricReduction.ker ≃* rationalPoints Q.quotient :=
  QuotientGroup.quotientKerEquivOfSurjective _ (Q.parahoricReduction_surjective hrad hQ)

end SpecialFibreQuotientData

end Henselian

end Langlands.BruhatTits.IntegralModels
