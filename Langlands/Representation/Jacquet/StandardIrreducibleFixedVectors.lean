import Langlands.Representation.Jacquet.IrreducibleFixedVectorGeneration
import Langlands.Representation.Jacquet.StandardPrescribedInductionGeneration
import Langlands.Representation.Jacquet.RationalInducedFixedVectors

/-! # Irreducible constituents at the prescribed standard level -/

noncomputable section

set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.Jacquet

open GroupScheme CuspidalSupport Aubert.General Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open BruhatTits.SpecialCompact

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance standardIrreducibleFixedAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardIrreducibleFixedTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Nonzero fixed vectors of actual normalized standard induction of irreducible
coefficients generate that induction at the same specified normal level. -/
theorem fixedVectorGenerated_standardInduction_of_irreducible_of_nontrivial_fixedVectors
    (I : Finset (SimpleRoot i ν))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G)) (hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
    (hKK₀ : K.toSubgroup ≤ K₀)
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwasawa : ∀ x : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, x = m * n * k)
    (hBasis : ∃ (B : CommGroupScheme (Spec (CommRingCat.of F))) (q : B.toGrp ⟶ T.toGrp),
      IsCompatibleStandardSplitComponent i ν (rootSet i ν I) B q ∧
        StandardParabolicBasisMember i ν (rootSet i ν I) q K.toSubgroup)
    (A : SmoothRep.{0, uF, uV} ℂ (levi i ν I)) (hA : A.IsIrreducible)
    (hfix : Nontrivial (fixedVectors ((normalizedInductionFunctor (family.decomposition I)
      (family.closedUnipotent I)).obj A).representation K.toSubgroup)) :
    fixedVectorGenerated K.toSubgroup
      ((normalizedInductionFunctor (family.decomposition I)
        (family.closedUnipotent I)).obj A) := by
  have hcoeff := (nontrivial_standardInduction_fixedVectors_iff i ν family I K hK K₀
    hnormal hIwasawa hBasis.choose_spec.choose_spec.2.1 A).mp hfix
  apply fixedVectorGenerated_standardInduction_of_coefficientGeneration i ν family I
    K hK K₀ hK₀ hKK₀ hIwasawa hBasis A
  exact (irreducibleFixedVectorGeneration _ _ A hA).mpr hcoeff

/-- For irreducible coefficients, each irreducible actual constituent has
nonzero fixed vectors exactly when its normalized induction does. This is a
level-dependent property; its proof below retains VI.9.4 explicitly. -/
def standardConstituentFixedVectorVisibility
    (I : Finset (SimpleRoot i ν)) (K : OpenSubgroup (rationalPoints G)) : Prop :=
  ∀ (A : SmoothRep.{0, uF, uV} ℂ (levi i ν I)), A.IsIrreducible →
    ∀ (D : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)), D.IsIrreducible →
      SmoothRep.IsSubquotient D ((normalizedInductionFunctor (family.decomposition I)
        (family.closedUnipotent I)).obj A) →
        (Nontrivial (fixedVectors ((normalizedInductionFunctor (family.decomposition I)
          (family.closedUnipotent I)).obj A).representation K.toSubgroup) ↔
          Nontrivial (fixedVectors D.representation K.toSubgroup))

/-- The exact VI.9.4 subquotient-generation statement, at the induction carrier
universe, gives the constituent comparison at the prescribed standard level. -/
theorem standardConstituentFixedVectorVisibility_of_subquotientGeneration
    (hGeneration : StandardFixedVectorSubquotientGenerationStatement.{uF, max uF uV})
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G)) (hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
    (hKK₀ : K.toSubgroup ≤ K₀)
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwasawa : ∀ x : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, x = m * n * k)
    (hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
      ∃ (B : CommGroupScheme (Spec (CommRingCat.of F))) (q : B.toGrp ⟶ T.toGrp),
        IsCompatibleStandardSplitComponent i ν J B q ∧
          StandardParabolicBasisMember i ν J q K.toSubgroup)
    (I : Finset (SimpleRoot i ν)) :
    standardConstituentFixedVectorVisibility.{uF, uV} i ν family I K := by
  intro A hA D hD hDA
  constructor
  · intro hfix
    have hgen := fixedVectorGenerated_standardInduction_of_irreducible_of_nontrivial_fixedVectors
      i ν family I K hK K₀ hK₀ hKK₀ hnormal hIwasawa
      (hIwahori (rootSet i ν I) (rootSet_subset i ν I)) A hA hfix
    have hDgen := hGeneration F G family.connectedReductive T i family.maximalSplitTorus ν
      family.genericCocharacter
      (fun J hJ => (standardCocharacter F G family.connectedReductive T i
        family.maximalSplitTorus ν family.genericCocharacter J hJ).1)
      K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
      _ hgen D hDA
    exact (irreducibleFixedVectorGeneration _ _ D hD).mp hDgen
  · exact SmoothRep.nontrivial_fixedVectors_of_isSubquotient K hK hDA

section RationalInertia

variable [LocallyOfFiniteType G.X.hom]

local instance standardIrreducibleLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance standardIrreducibleLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance standardIrreducibleLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X
local instance standardIrreducibleLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance

/-- The constituent comparison, combined with the actual full-unramified
fixed-space equivalence, compares constituents of rationally inertially related
coefficients in one fixed standard Levi. No ambient association is inferred. -/
theorem nontrivial_fixedVectors_constituents_iff_of_rationalInertiaRelated
    (I : Finset (SimpleRoot i ν))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hvisibility : standardConstituentFixedVectorVisibility.{uF, uV} i ν family I K)
    (A B : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (hA : A.IsIrreducible) (hB : B.IsIrreducible)
    (hAB : IsRationalInertiaRelated (bernsteinLeviScheme i ν I) A B)
    (D E : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hD : D.IsIrreducible) (hE : E.IsIrreducible)
    (hDA : SmoothRep.IsSubquotient D (rationalStandardInduction i ν family I A))
    (hEB : SmoothRep.IsSubquotient E (rationalStandardInduction i ν family I B)) :
    Nontrivial (fixedVectors D.representation K.toSubgroup) ↔
      Nontrivial (fixedVectors E.representation K.toSubgroup) := by
  have hAlit : (bernsteinLiteralLeviRep i ν I A).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation
      (leviRationalPointHomeomorph i ν I).symm).mpr hA
  have hBlit : (bernsteinLiteralLeviRep i ν I B).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff B.representation
      (leviRationalPointHomeomorph i ν I).symm).mpr hB
  exact (hvisibility _ hAlit D hD hDA).symm.trans
    ((nontrivial_inductionFixedVectors_iff_of_rationalInertiaRelated
      i ν family I K hK hAB).trans (hvisibility _ hBlit E hE hEB))

end RationalInertia

end Langlands.Jacquet
