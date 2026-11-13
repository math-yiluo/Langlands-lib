import Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionReduction
import Langlands.Representation.CuspidalSupport.BernsteinInductionFromRestriction
import Langlands.Representation.Category.ConstituentSerre

/-! # Assembling Bernstein induction and restriction from two global inputs -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- The full induction-restriction proposition follows from Bernstein
category decomposition and block characterization. Both premises are explicit. -/
def BernsteinInductionRestrictionAssemblyStatement : Prop :=
  BernsteinDecompositionStatement.{uF, max uF uV} →
    BernsteinBlockCharacterizationStatement.{uF, uV} →
      BernsteinInductionRestrictionStatement.{uF, uV}

section Local

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance inductionRestrictionAssemblyAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance inductionRestrictionAssemblyTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- An actual inertial-support presentation places the irreducible object
in the whole saturated block of that class, by subquotient transitivity. -/
theorem bernsteinSaturatedBlockProperty_of_inertialSupport
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (hπs : IsBernsteinInertialSupport i ν family s π) :
    bernsteinSaturatedBlockProperty i ν family s π := by
  obtain ⟨a, ha, hπa⟩ := hπs
  intro τ hτ hτπ
  exact ⟨a, ha, hτ,
    smoothSubquotientTransitivity ℂ _ (bernsteinInduction i ν family a) π τ hτπ hπa.2⟩

/-- Orthogonality of the actual Bernstein blocks implies uniqueness of
inertial support. No support-association premise is required here. -/
theorem bernsteinInertialSupportUniqueness_of_offDiagonalHomsZero
    (hoff : Renard.OffDiagonalHomsZero
      (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, max uF uV} i ν family s)) :
    BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family := by
  intro π s t hs ht
  by_contra hst
  have hπs := (bernsteinBlockProperty_iff_saturated s π).mpr
    (bernsteinSaturatedBlockProperty_of_inertialSupport i ν family π s hs)
  have hπt := (bernsteinBlockProperty_iff_saturated t π).mpr
    (bernsteinSaturatedBlockProperty_of_inertialSupport i ν family π t ht)
  have hzero : IsZero π := (IsZero.iff_id_eq_zero π).mpr
    (hoff s t hst π π hπs hπt (𝟙 π))
  obtain ⟨a, _, hπa⟩ := hs
  exact SmoothRep.not_isSubquotient_of_isZero hzero hπa.1
    (SmoothRep.IsSubrepresentation.isSubquotient ⟨𝟙 π, Function.injective_id⟩)

/-- The literal fibre predicate passes to every actual subquotient. -/
theorem bernsteinLeviFibreProperty_of_isSubquotient
    (J : Finset (SimpleRoot i ν))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J))
    (hρ : bernsteinLeviFibreProperty i ν family J a ρ)
    (hτρ : SmoothRep.IsSubquotient τ ρ) :
    bernsteinLeviFibreProperty i ν family J a τ := by
  intro π hπ hπτ
  exact hρ π hπ (smoothSubquotientTransitivity ℂ _ ρ τ π hπτ hτρ)

/-- Restriction of ambient block members into the literal fibre, together
with category decomposition, implies induction of all smooth fibred inputs. -/
theorem bernsteinInduction_mem_block_of_fibre_restriction
    (hdec : Renard.IsCategoryDecomposition
      (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, max uF uV} i ν family s))
    (J : Finset (SimpleRoot i ν))
    (hres : ∀ (c : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
      bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family c) V →
        bernsteinLeviFibreProperty i ν family J c
          ((jacquetFunctor (family.decomposition J) (family.closedUnipotent J)).obj V))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J))
    (hρ : bernsteinLeviFibreProperty i ν family J a ρ) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj ρ) := by
  exact bernsteinInduction_mem_block_of_restriction i ν family hdec
    (bernsteinInertialSupportUniqueness_of_offDiagonalHomsZero i ν family hdec.2) J
    (fun c τ => bernsteinLeviFibreProperty i ν family J c τ)
    (fun c τ hτ hF => bernsteinInduction_mem_block_of_irreducible_fibre
      i ν family J c τ hτ hF)
    (fun c V hV τ _ hτV => bernsteinLeviFibreProperty_of_isSubquotient
      i ν family J c _ τ (hres c V hV) hτV)
    a ρ (fun τ _ hτρ => bernsteinLeviFibreProperty_of_isSubquotient
      i ν family J a ρ τ hρ hτρ)

end Local

/-- The conditional assembly of the exact published target. The two
additional hypotheses remain obligations, rather than newly supplied facts. -/
theorem bernsteinInductionRestriction_of_decomposition_and_characterization :
    BernsteinInductionRestrictionAssemblyStatement.{uF, uV} := by
  intro hdec hchar F _ _ _ _ G _ _ T i ν
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family J a
  dsimp only
  constructor
  · intro ρ hρ
    exact bernsteinInduction_mem_block_of_fibre_restriction i ν family
      (hdec F G T i ν family) J
      (fun c V hV => bernsteinLeviFibreProperty_of_blockCharacterization
        i ν family hchar J c V hV) a ρ hρ
  · intro V hV
    exact bernsteinLeviFibreProperty_of_blockCharacterization i ν family hchar J a V hV

end Langlands.CuspidalSupport
