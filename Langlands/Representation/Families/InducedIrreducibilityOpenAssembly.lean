import Langlands.Representation.Families.InducedIrreducibilityOpenReduction
import Langlands.Representation.Families.ActualLeviUnramifiedInducedFamily
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement

/-! # Renard VI.8.4 from admissibility, compactness and uniform detection -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenAssembly

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme
open Plancherel CompactCompressionPrincipalOpen LocalizedMatrixPrincipalOpen

universe u v uS uG uV uW

/-- Full specialization depends on the character only through its ring map. -/
theorem isFullSpecialization_of_toRingHom_eq {S : Type uS} [CommRing S] [Algebra ℂ S]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : SmoothRep.{0, uG, uV} ℂ G} [Module S A] [SMulCommClass ℂ S A]
    {D : SmoothRep.{0, uG, uW} ℂ G} {χ : S →ₐ[ℂ] ℂ} {φ : S →+* ℂ}
    (h : χ.toRingHom = φ)
    (hD : letI : Algebra S ℂ := φ.toAlgebra
      ∃ (f : A.representation.IntertwiningMap D.representation)
        (hf : ∀ (s : S) (v : A), f (s • v) = algebraMap S ℂ s • f v),
        Function.Bijective
          (Compact.CoefficientSpecialization.scalarExtension S A.representation
            D.representation f hf)) :
    IsFullSpecialization S A χ D := by
  subst h
  exact hD

/-- The actual universal induced family is a global coefficient family for the
induced unramified twists, once the inducing representation is admissible and
the parabolic quotient is compact. -/
theorem universalFamily_isGlobalCoefficientFamily
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    {G P M U : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      haveI : LocallyOfFiniteType M.X.hom := by
        have := hl.isConnectedReductive.smooth
        infer_instance
      ∀ [CompactSpace (Induction.LeftQuotient (pointImage p))]
        (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)), ρ.IsAdmissible →
        IsGlobalCoefficientFamily (ActualLevi.universalFamily p l r hp hl hr hmul ρ) M
          (ActualLevi.regularAlgebraEquiv p l hp hl).symm
          (ActualLevi.fiber p l r hp hl hr hmul ρ) := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : LocallyOfFiniteType M.X.hom := by
    have := hl.isConnectedReductive.smooth
    infer_instance
  intro _ ρ hρ
  refine ⟨fun K hK => ?_, fun ψ => ?_⟩
  · obtain ⟨hfin, hfree⟩ :=
      ActualLevi.universalFamily_fixed_finite_free p l r hp hl hr hmul ρ hρ K hK
    exact ⟨hfree, hfin⟩
  · refine isFullSpecialization_of_toRingHom_eq
      (φ := UnramifiedNormalized.evaluation (ActualLevi.normFamily p l hp hl)
        (ActualLevi.parameterEquiv p l hp hl ψ)) ?_
      (ActualLevi.universalFamily_specialization p l r hp hl hr hmul ρ ψ)
    ext b
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coefficientCharacter_apply,
      ActualLevi.regularAlgebraEquiv_symm_apply, UnramifiedNormalized.evaluation_apply]

/-- **Renard VI.8.4**, reduced to Jacquet's admissibility theorem, compactness of
parabolic quotients and uniform detection of the induced twists. -/
theorem inducedIrreducibilityOpen_of_statements
    (hadm : RationalPointsIrreducibleAdmissibleStatement.{u, v})
    (hcpt : ArbitraryParabolicQuotientCompactStatement.{u})
    (hdet : InducedTwistsUniformDetectionStatement.{u, v}) :
    InducedIrreducibilityOpenStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  intro ρ hρ
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) := hcpt k G hG P p hp
  have hadmρ : ρ.IsAdmissible := hadm k M hl.isConnectedReductive ρ hρ
  exact InducedIrreducibilityOpenReduction.exists_principal_neighborhood_of_detection
    hdet k G hG P M U p l r hp hl hr hmul ρ hρ (ActualLevi.coefficientAlgebra p l hp hl)
    (ActualLevi.universalFamily p l r hp hl hr hmul ρ)
    (ActualLevi.regularAlgebraEquiv p l hp hl).symm
    (universalFamily_isGlobalCoefficientFamily hG p l r hp hl hr hmul ρ hadmρ)

/-- The three propositions from which the proof of Renard VI.8.4 is assembled. -/
structure Inputs : Prop where
  admissible : RationalPointsIrreducibleAdmissibleStatement.{u, v}
  quotientCompact : ArbitraryParabolicQuotientCompactStatement.{u}
  uniformDetection : InducedTwistsUniformDetectionStatement.{u, v}

/-- **Renard VI.8.4** from the packaged inputs. -/
theorem inducedIrreducibilityOpen_of_inputs (h : Inputs.{u, v}) :
    InducedIrreducibilityOpenStatement.{u, v} :=
  inducedIrreducibilityOpen_of_statements h.admissible h.quotientCompact h.uniformDetection

end Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenAssembly
