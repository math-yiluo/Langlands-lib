import Langlands.Shimura.PEL.HarrisTaylorCMDivisionAssembly
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof
import Langlands.AlgebraicGeometry.ArtinianLiftingSmooth
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion

/-! # Infinitesimal and valuative criteria for division-case CM representability -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "componentwise" => ComponentwiseAdmissibleCMBase D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The spectrum of a noetherian ring with a given structure morphism to
`Spec F` is a componentwise admissible test. Admissibility comes from
`componentwiseAdmissibleCMBase_of_relativeDual` and the Library theorems
`relativeDualSchemeExistence` and `relativeDualSchemeGeometry`. -/
def specTest (B : Type) [CommRing B] [IsNoetherianRing B]
    (β : Spec (CommRingCat.of B) ⟶ Spec (.of F)) : DisBases :=
  ⟨Over.mk β,
    have : IsLocallyNoetherian (Over.mk β).left :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of B)))
    componentwiseAdmissibleCMBase_of_relativeDual D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0} (Over.mk β)⟩

/-- The test morphism `Spec B ⟶ Spec B'` induced by a ring map `φ : B' →+* B`,
where `Spec B` carries the composite structure morphism. -/
def specTestMap {B' B : Type} [CommRing B'] [CommRing B] [IsNoetherianRing B']
    [IsNoetherianRing B] (φ : B' →+* B) (β : Spec (CommRingCat.of B') ⟶ Spec (.of F)) :
    specTest D C preservation composition unitCoherence associativity comparison symmetry
        stability square universality B (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶
      specTest D C preservation composition unitCoherence associativity comparison symmetry
        stability square universality B' β :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl)

/-- Infinitesimal lifting for the normalized class presheaf at a small level:
along every surjection `φ : B' → B` of local Artinian rings whose kernel is
killed by the maximal ideal of `B'`, and for every structure morphism
`Spec B' ⟶ Spec F`, restriction of classes from `Spec B'` to `Spec B` is
surjective. -/
def CMLevelArtinianLiftingStatement (U : SmallCMLevel D) : Prop :=
  ∀ (B' B : Type) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] (φ : B' →+* B), Function.Surjective φ →
      maximalIdeal B' * RingHom.ker φ = ⊥ →
      ∀ β : Spec (CommRingCat.of B') ⟶ Spec (.of F),
        Function.Surjective (((moduli).obj U).map
          (specTestMap D C preservation composition unitCoherence associativity comparison
            symmetry stability square universality φ β).op)

/-- Existence part of the valuative criterion for the normalized class presheaf
at a small level, tested on discrete valuation rings: for every discrete
valuation ring `V` with fraction field `K` and every structure morphism
`Spec V ⟶ Spec F`, restriction of classes from `Spec V` to `Spec K` is
surjective. -/
def CMLevelDiscreteValuativeExistenceStatement (U : SmallCMLevel D) : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (β : Spec (CommRingCat.of V) ⟶ Spec (.of F)),
      Function.Surjective (((moduli).obj U).map
        (specTestMap D C preservation composition unitCoherence associativity comparison
          symmetry stability square universality (algebraMap V K) β).op)

/-- Representation data at a fixed small level by a scheme with an immersion
into finite projective space over `F`. No smoothness, properness or
admissibility of the scheme is included. -/
structure CMLevelQuasiProjectiveRepresentation (U : SmallCMLevel D) where
  scheme : Over (Spec (.of F))
  dim : ℕ
  embedding : scheme.left ⟶ ProjectiveSpace F dim
  isImmersion : IsImmersion embedding
  embedding_comp : embedding ≫ projectiveSpaceToSpec F dim = scheme.hom
  represents :
    admissibleTestPoints D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality scheme ≅ (moduli).obj U

variable {D C preservation composition unitCoherence associativity comparison symmetry
  stability square universality dualityNaturality polarizationStability compatibility h htor}

namespace CMLevelQuasiProjectiveRepresentation

variable {U : SmallCMLevel D}
  (R : CMLevelQuasiProjectiveRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

/-- Points of the representing scheme lift along any test morphism on which
restriction of classes is surjective. -/
theorem exists_lift {T T' : DisBases} (r : T ⟶ T')
    (hr : Function.Surjective (((moduli).obj U).map r.op)) (a : T.obj ⟶ R.scheme) :
    ∃ c : T'.obj ⟶ R.scheme, r.hom ≫ c = a := by
  obtain ⟨x', hx'⟩ := hr (R.represents.hom.app (Opposite.op T) ⟨a⟩)
  refine ⟨(R.represents.inv.app (Opposite.op T') x').down, ?_⟩
  have key := NatTrans.naturality_apply R.represents.inv r.op x'
  rw [hx'] at key
  have h2 := Iso.hom_inv_id_app_apply R.represents (Opposite.op T) ⟨a⟩
  exact (congrArg ULift.down (h2.symm.trans key)).symm

instance locallyOfFiniteType : LocallyOfFiniteType R.scheme.hom := by
  have := R.isImmersion
  rw [← R.embedding_comp]
  infer_instance

instance quasiCompact : QuasiCompact R.scheme.hom := by
  have := R.isImmersion
  have : IsLocallyNoetherian (ProjectiveSpace F R.dim) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceToSpec F R.dim)
  have : CompactSpace (ProjectiveSpace F R.dim) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceToSpec F R.dim)
  have : IsNoetherian (ProjectiveSpace F R.dim) := {}
  have : TopologicalSpace.NoetherianSpace R.scheme.left :=
    R.embedding.isEmbedding.isInducing.noetherianSpace
  infer_instance

instance isSeparated : IsSeparated R.scheme.hom := by
  have := R.isImmersion
  rw [← R.embedding_comp]
  infer_instance

theorem smooth (hlift : CMLevelArtinianLiftingStatement D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor U) :
    Smooth R.scheme.hom := by
  apply ArtinianLiftingSmooth.smooth_of_liftsArtinian
  intro B' B _ _ _ _ _ _ φ hφ hker α β hαβ _
  let a : (specTest D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality B (Spec.map (CommRingCat.ofHom φ) ≫ β)).obj ⟶
      R.scheme := Over.homMk α hαβ
  obtain ⟨c, hc⟩ := R.exists_lift _ (hlift B' B φ hφ hker β) a
  refine ⟨c.left, Over.w c, ?_⟩
  exact congrArg CommaMorphism.left hc

theorem universallyClosed (hval : CMLevelDiscreteValuativeExistenceStatement D C
    preservation composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor U) :
    UniversallyClosed R.scheme.hom := by
  apply universallyClosed_of_forall_isDiscreteValuationRing_hasLift
  intro S hS
  let a : (specTest D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality S.K
        (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ S.i₂)).obj ⟶
      R.scheme := Over.homMk S.i₁ S.commSq.w
  obtain ⟨c, hc⟩ := R.exists_lift _ (hval S.R S.K S.i₂) a
  exact ⟨⟨{ l := c.left
            fac_left := congrArg CommaMorphism.left hc
            fac_right := Over.w c }⟩⟩

theorem isProper (hval : CMLevelDiscreteValuativeExistenceStatement D C
    preservation composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor U) :
    IsProper R.scheme.hom := by
  have := R.universallyClosed hval
  constructor

/-- Quasi-projective representation data, infinitesimal lifting and
discrete valuative existence give geometric representation data on the same
scheme. -/
def toGeometric
    (hlift : CMLevelArtinianLiftingStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U)
    (hval : CMLevelDiscreteValuativeExistenceStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor U) :
    CMLevelGeometricRepresentation D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U where
  scheme := R.scheme
  smooth := R.smooth hlift
  proper := R.isProper hval
  dim := R.dim
  embedding := R.embedding
  isImmersion := R.isImmersion
  embedding_comp := R.embedding_comp
  represents := R.represents

end CMLevelQuasiProjectiveRepresentation

/-- Conversely, geometric representation data forgets to quasi-projective
representation data on the same scheme. -/
def CMLevelGeometricRepresentation.toQuasiProjective {U : SmallCMLevel D}
    (R : CMLevelGeometricRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U) :
    CMLevelQuasiProjectiveRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U where
  scheme := R.scheme
  dim := R.dim
  embedding := R.embedding
  isImmersion := R.isImmersion
  embedding_comp := R.embedding_comp
  represents := R.represents

/-- A proper representer forces discrete valuative existence for the presheaf. -/
theorem CMLevelGeometricRepresentation.discreteValuativeExistence {U : SmallCMLevel D}
    (R : CMLevelGeometricRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U) :
    CMLevelDiscreteValuativeExistenceStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U := by
  intro V K _ _ _ _ _ _ β x
  have := R.proper
  let T := specTest D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality K
      (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ β)
  let T' := specTest D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality V β
  let a : T.obj ⟶ R.scheme := (R.represents.inv.app (Opposite.op T) x).down
  let S : ValuativeCommSq R.scheme.hom :=
    { R := V, K := K, i₁ := a.left, i₂ := β, commSq := ⟨Over.w a⟩ }
  have hE : ValuativeCriterion.Existence R.scheme.hom := by
    have hU : UniversallyClosed R.scheme.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hU
    exact hU.1
  obtain ⟨⟨l⟩⟩ := hE S
  let c : T'.obj ⟶ R.scheme := Over.homMk l.l l.fac_right
  refine ⟨R.represents.hom.app (Opposite.op T') ⟨c⟩, ?_⟩
  have key := NatTrans.naturality_apply R.represents.hom
    (specTestMap D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality (algebraMap V K) β).op ⟨c⟩
  refine key.symm.trans ?_
  have hc : (⟨(specTestMap D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality (algebraMap V K) β).hom ≫ c⟩ :
        ULift (T.obj ⟶ R.scheme)) = ⟨a⟩ := by
    congr 1
    ext
    exact l.fac_left
  refine (congrArg (R.represents.hom.app (Opposite.op T)) hc).trans ?_
  exact Iso.inv_hom_id_app_apply R.represents (Opposite.op T) x

/-- Assembly of geometric representability from quasi-projective
representability, infinitesimal lifting and discrete valuative existence at
every small level. -/
theorem cmGeometricRepresentabilityStatement_of_criteria
    (hrep : ∀ U : SmallCMLevel D, Nonempty (CMLevelQuasiProjectiveRepresentation D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor U))
    (hlift : ∀ U : SmallCMLevel D, CMLevelArtinianLiftingStatement D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor U)
    (hval : ∀ U : SmallCMLevel D, CMLevelDiscreteValuativeExistenceStatement D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor U) :
    CMGeometricRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor := fun U =>
  let ⟨R⟩ := hrep U
  ⟨R.toGeometric (hlift U) (hval U)⟩

/-- The division-case target follows from the three division-case criteria.
None of the three hypotheses is proved here. -/
theorem divisionCMRepresentabilityStatement_of_criteria
    (hrep : D.IsDivision → ∀ U : SmallCMLevel D, Nonempty
      (CMLevelQuasiProjectiveRepresentation D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U))
    (hlift : D.IsDivision → ∀ U : SmallCMLevel D, CMLevelArtinianLiftingStatement D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor U)
    (hval : D.IsDivision → ∀ U : SmallCMLevel D, CMLevelDiscreteValuativeExistenceStatement
      D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor U) :
    DivisionCMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor :=
  divisionCMRepresentabilityStatement_of_geometric D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0}
    fun hD => cmGeometricRepresentabilityStatement_of_criteria (hrep hD) (hlift hD) (hval hD)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
