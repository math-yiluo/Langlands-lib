import Langlands.Representation.Unitary.CentralSubgroupForm
import Langlands.Representation.Induction.IrreducibilityReflection
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof
import Langlands.Representation.Unitary.Twist

/-! # Positive forms for the actual opposite-scalar coefficient representation -/

noncomputable section

universe u uV uG uI

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicOppositeSquareIntegrableForm

open Aubert.General DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

section General

variable {H : Type uG} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
  (hδ : IsUnimodularModulus U hU) (hr : Continuous h.projection)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

include hδ hr in
/-- Irreducibility reflection for the actual Levi-inflated unramified
induction, before specializing to rational point groups. -/
theorem irreducible_of_unramifiedLeviInduction
    (A : SmoothRep.{0, uG, uV} ℂ M) (z : unramifiedCharacters ν)
    (hi : (UnramifiedLeviInduction h hU ν z A).IsIrreducible) :
    A.IsIrreducible := by
  let B := A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)
  have hn : ((normalizedInductionFunctor h hU).obj B).IsIrreducible :=
    (Langlands.isIrreducible_iff_of_equiv (normalizedInductionLeviEquiv h hU hδ B)).mpr hi
  have ht := isIrreducible_of_normalizedInduction h hU B hr hn
  exact (isIrreducible_twist_iff z.val.toMonoidHom A.representation).mp ht

end General

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance leviLocallyCompact : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

local instance leviSecondCountable : SecondCountableTopology (levi χ) :=
  TopologicalSpace.Subtype.secondCountableTopology (levi χ : Set (RationalPoint F G.X))

local instance centerQuotientMeasurable :
    MeasurableSpace (levi χ ⧸ Subgroup.center (levi χ)) := borel _

local instance centerQuotientBorel :
    BorelSpace (levi χ ⧸ Subgroup.center (levi χ)) := ⟨rfl⟩

/-- Irreducibility of one actual unramified induced twist reflects
irreducibility of the original coefficient representation. -/
theorem irreducible_of_twistedInduction (hG : IsConnectedReductive G)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : unramifiedCharacters (normCharacters χ))
    (hi : (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible) :
    A.IsIrreducible :=
  irreducible_of_unramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) (projection_continuous χ) (leviNormCharacters χ)
    A (parameterTransport χ z) hi

/-- The nonempty irreducibility locus in the exact scalar target makes the
untwisted coefficient representation irreducible. -/
theorem irreducible_of_locus (hG : IsConnectedReductive G)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    {D : Set (unramifiedCharacters (normCharacters χ))} (hne : D.Nonempty)
    (hi : ∀ z ∈ D, (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible) :
    A.IsIrreducible := by
  obtain ⟨z, hz⟩ := hne
  exact irreducible_of_twistedInduction χ hG A z (hi z hz)

/-- A positive invariant form on the original Levi carrier, constructed from
precisely the square-integrability and irreducibility-locus premises of the
actual scalar target. -/
def squareIntegrableForm (hG : IsConnectedReductive G)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    {D : Set (unramifiedCharacters (normCharacters χ))} (hne : D.Nonempty)
    (hi : ∀ z ∈ D, (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (μM : Measure (levi χ ⧸ C)) [μM.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM) :
    InvariantPositiveForm A.representation :=
  squareIntegrableCentralSubgroupForm C hC
    (compactOpenCofinal_of_nonarchimedean (levi χ))
    (DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one χ hG)
    (irreducible_of_locus χ hG A hne hi) μM hsq

end Langlands.Plancherel.DynamicOppositeSquareIntegrableForm
