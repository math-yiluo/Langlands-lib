import Langlands.Shimura.PEL.HarrisTaylorCMDivisionRepresentabilityStatement
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Assembly of the division-case CM representability target -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.AlgebraicGeometry

universe u

/-- A proper scheme with an immersion into finite projective space over the
same affine base is `IsHProjective`: the immersion is universally closed,
since projective space is separated, so it has closed range. -/
theorem IsHProjective.of_isImmersion_of_isProper {R : Type u} [CommRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] (m : ℕ)
    (i : X ⟶ ProjectiveSpace R m) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec R m = p) :
    IsHProjective p := by
  refine ⟨m, i, ?_, hi⟩
  have : UniversallyClosed (i ≫ projectiveSpaceToSpec R m) := by
    rw [hi]
    infer_instance
  have : UniversallyClosed i :=
    UniversallyClosed.of_comp_of_isSeparated i (projectiveSpaceToSpec R m)
  exact .of_isPreimmersion i i.isClosedMap.isClosed_range

/-- Conversely an `IsHProjective` morphism is proper and has an immersion into
finite projective space over its base. -/
theorem IsHProjective.exists_isImmersion {R : Type u} [CommRing R]
    {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of R)} (hp : IsHProjective p) :
    ∃ (m : ℕ) (i : X ⟶ ProjectiveSpace R m),
      IsImmersion i ∧ i ≫ projectiveSpaceToSpec R m = p := by
  obtain ⟨m, i, hclosed, hi⟩ := hp
  have : IsClosedImmersion i := hclosed
  exact ⟨m, i, inferInstance, hi⟩

end Langlands.AlgebraicGeometry

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

/-- The lifted functor of points of an arbitrary scheme over `Spec F`,
restricted to the componentwise admissible test category. The scheme itself
need not be an admissible object. -/
def admissibleTestPoints (X : Over (Spec (.of F))) : DisBasesᵒᵖ ⥤ Type 1 :=
  (ObjectProperty.ι (componentwise)).op ⋙ uliftYoneda.{1}.obj X

/-- For an admissible object, the lifted Yoneda presheaf in the full
subcategory is the restricted functor of points of the underlying scheme. -/
def uliftYonedaIsoAdmissibleTestPoints (X : DisBases) :
    uliftYoneda.{1}.obj X ≅
      admissibleTestPoints D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality X.obj :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      (Equiv.ulift.trans
        (((ObjectProperty.fullyFaithfulι (componentwise)).homEquiv).trans
          Equiv.ulift.symm)))
    (fun f => by
      ext g
      rfl)

/-- Representation data at a fixed small level in the form produced by a
quasi-projective construction: an arbitrary scheme over `Spec F`, smooth and
proper over `F`, with an immersion into finite projective space over `F`, and
a natural isomorphism from its restricted functor of points to the existing
class presheaf. No admissibility of the scheme is included. -/
structure CMLevelGeometricRepresentation (U : SmallCMLevel D) where
  scheme : Over (Spec (.of F))
  smooth : Smooth scheme.hom
  proper : IsProper scheme.hom
  dim : ℕ
  embedding : scheme.left ⟶ ProjectiveSpace F dim
  isImmersion : IsImmersion embedding
  embedding_comp : embedding ≫ projectiveSpaceToSpec F dim = scheme.hom
  represents :
    admissibleTestPoints D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality scheme ≅ (moduli).obj U

/-- The geometric form of representability at every small level. -/
def CMGeometricRepresentabilityStatement : Prop :=
  ∀ U : SmallCMLevel D,
    Nonempty (CMLevelGeometricRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U)

/-- Every exact representation gives geometric representation data: forget
admissibility, keep the same scheme, and use the closed immersion as an
immersion. -/
def CMLevelRepresentation.toGeometric {U : SmallCMLevel D}
    (R : CMLevelRepresentation D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U) :
    CMLevelGeometricRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U where
  scheme := R.base.obj
  smooth := R.smooth
  proper := IsHProjective.isProper R.projective
  dim := Classical.choose (IsHProjective.exists_isImmersion R.projective)
  embedding := Classical.choose (Classical.choose_spec (IsHProjective.exists_isImmersion R.projective))
  isImmersion := (Classical.choose_spec
    (Classical.choose_spec (IsHProjective.exists_isImmersion R.projective))).1
  embedding_comp := (Classical.choose_spec
    (Classical.choose_spec (IsHProjective.exists_isImmersion R.projective))).2
  represents := (uliftYonedaIsoAdmissibleTestPoints D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    R.base).symm ≪≫ R.represents

/-- Under the two relative dual statements, geometric representation data is
an exact representation: the smooth scheme is componentwise admissible by
`smoothComponentwiseAdmissibleCMBase_of_relativeDual`, and properness with the
immersion gives `IsHProjective`. -/
def CMLevelGeometricRepresentation.toRepresentation
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {U : SmallCMLevel D}
    (R : CMLevelGeometricRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U) :
    CMLevelRepresentation D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U :=
  let := R.smooth
  let := R.proper
  let := R.isImmersion
  { base := ⟨R.scheme, smoothComponentwiseAdmissibleCMBase_of_relativeDual D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality existence geometry R.scheme⟩
    smooth := R.smooth
    projective := IsHProjective.of_isImmersion_of_isProper R.scheme.hom R.dim
      R.embedding R.embedding_comp
    represents := uliftYonedaIsoAdmissibleTestPoints D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      ⟨R.scheme, smoothComponentwiseAdmissibleCMBase_of_relativeDual D C
        preservation composition unitCoherence associativity comparison symmetry
        stability square universality existence geometry R.scheme⟩ ≪≫ R.represents }

/-- At a fixed small level, the exact pointwise target is equivalent to the
existence of geometric representation data, given the two relative dual
statements. -/
theorem cmLevelRepresentabilityStatement_iff_geometric
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (U : SmallCMLevel D) :
    CMLevelRepresentabilityStatement D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U ↔
      Nonempty (CMLevelGeometricRepresentation D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U) :=
  ⟨fun ⟨R⟩ => ⟨R.toGeometric⟩, fun ⟨R⟩ => ⟨R.toRepresentation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor existence geometry⟩⟩

/-- The exact consequent of the target is equivalent to its geometric form
under the two relative dual statements. -/
theorem cmRepresentabilityStatement_iff_geometric
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    CMRepresentabilityStatement D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor ↔
      CMGeometricRepresentabilityStatement D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor :=
  forall_congr' fun U => cmLevelRepresentabilityStatement_iff_geometric D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor existence geometry U

/-- Conditional assembly of the division-case target from the relative dual
statements and division-case geometric representability. This proves neither
premise and is not a proof of `DivisionCMRepresentabilityStatement`. -/
theorem divisionCMRepresentabilityStatement_of_geometric
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hgeom : D.IsDivision →
      CMGeometricRepresentabilityStatement D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor) :
    DivisionCMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor := fun hD =>
  (cmRepresentabilityStatement_iff_geometric D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor existence geometry).mpr (hgeom hD)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
