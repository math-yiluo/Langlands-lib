import Langlands.Representation.Induction.FiniteTwistTrace
import Langlands.Representation.Induction.UnramifiedCompactStabilizer
import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport
import Langlands.Representation.Aubert.General.UnramifiedInducedTrace
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Compact open fixed spaces of actual unramified parabolic inductions -/

noncomputable section

set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- For a compact quotient, a character trivial on all compact subgroups of the
inducing group leaves the compact open induced fixed space linearly equivalent. -/
def compactTrivialTwistInducedFixedVectorsEquiv
    (P : Subgroup G) (hP : IsClosed (P : Set G))
    [CompactSpace (LeftQuotient P)] (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (χ : P →* ℂˣ)
    (hχ : ∀ H : Subgroup P, IsCompact (H : Set P) → H ≤ χ.ker) :
    fixedVectors (smoothInduced P (twist χ σ)) K.toSubgroup ≃ₗ[ℂ]
      fixedVectors (smoothInduced P σ) K.toSubgroup := by
  let t := (exists_finset_doubleCoset_representatives P K).choose
  have ht := (exists_finset_doubleCoset_representatives P K).choose_spec
  exact (fixedTwistEvaluationEquiv P σ K hK t ht.1 ht.2 χ
    (fun x => hχ _ (isCompact_conjOpenSubgroup P hP K hK x))).trans
      (fixedEvaluationEquiv P σ K hK t ht.1 ht.2).symm

end Langlands.Induction

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}

/-- Twisting a Levi action by a character trivial on compact subgroups after
inflation preserves the compact open fixed space of normalized induction. -/
def normalizedInductionCompactTrivialTwistFixedVectorsEquiv
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hP : IsClosed (P : Set G)) [CompactSpace (Induction.LeftQuotient P)]
    (A : SmoothRep.{0,uG,uV} ℂ M) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (hχP : ∀ H : Subgroup P, IsCompact (H : Set P) →
      H ≤ (χ.comp h.projection).ker) :
    fixedVectors ((normalizedInductionFunctor h hU).obj (A.twist χ hχ)).representation
      K.toSubgroup ≃ₗ[ℂ]
    fixedVectors ((normalizedInductionFunctor h hU).obj A).representation
      K.toSubgroup := by
  change fixedVectors (Induction.smoothInduced P
    (inducingRepresentation h hU (A.twist χ hχ))) K.toSubgroup ≃ₗ[ℂ] _
  rw [inducingRepresentation_twist]
  exact Induction.compactTrivialTwistInducedFixedVectorsEquiv P hP
    (inducingRepresentation h hU A) K hK (χ.comp h.projection) hχP

end Langlands.Aubert.General

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance rationalInducedFixedVectorsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance rationalInducedFixedVectorsTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance rationalInducedLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance rationalInducedLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance rationalInducedLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyOfFiniteType G.X.hom]

local instance rationalInducedLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance

/-- Actual normalized standard induction of an arbitrary smooth action of the
represented standard Levi scheme, through the canonical point homeomorphism. -/
abbrev rationalStandardInduction (I : Finset (SimpleRoot i ν))
    (A : SmoothRep.{0,uF,uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I))) :
    SmoothRep.{0,uF,max uF uV} ℂ (rationalPoints G) :=
  (normalizedInductionFunctor (family.decomposition I) (family.closedUnipotent I)).obj
    (bernsteinLiteralLeviRep i ν I A)

/-- A full unramified twist on the actual standard Levi scheme preserves the
compact open fixed space of its actual normalized induction up to a linear
equivalence. No cuspidality, irreducibility or admissibility is assumed. -/
def rationalUnramifiedInductionFixedVectorsEquiv
    (I : Finset (SimpleRoot i ν))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (χ : unramifiedCharacters
      (fun c => (rationalNormCharacters (bernsteinLeviScheme i ν I) c).toMul))
    (A : SmoothRep.{0,uF,uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I))) :
    fixedVectors (rationalStandardInduction i ν family I
      (rationalUnramifiedTwist (bernsteinLeviScheme i ν I) χ A)).representation
        K.toSubgroup ≃ₗ[ℂ]
      fixedVectors (rationalStandardInduction i ν family I A).representation
        K.toSubgroup := by
  let h := family.decomposition I
  let r : parabolic i ν I →* rationalPoints (bernsteinLeviScheme i ν I) :=
    (leviRationalPointHomeomorph i ν I).symm.toMulEquiv.toMonoidHom.comp h.projection
  have hr : Continuous r :=
    (leviRationalPointHomeomorph i ν I).symm.continuous.comp
      (continuous_standard_projection i ν standardCocharacter
        family.connectedReductive family.maximalSplitTorus family.genericCocharacter I)
  have hP : IsClosed (parabolic i ν I : Set (rationalPoints G)) :=
    isClosed_standard_parabolic i ν standardCocharacter
      family.connectedReductive family.maximalSplitTorus family.genericCocharacter I
  letI : CompactSpace (Induction.LeftQuotient (parabolic i ν I)) :=
    compactSpace_leftQuotient_parabolic i ν BruhatTits.dynamicParabolicQuotientCompact
      standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter I
  let χM : levi i ν I →* ℂˣ :=
    χ.val.toMonoidHom.comp (leviRationalPointHomeomorph i ν I).symm.toMulEquiv.toMonoidHom
  have hχM : IsOpen (χM.ker : Set (levi i ν I)) :=
    (isOpen_rationalUnramifiedCharacter_ker (bernsteinLeviScheme i ν I) χ).preimage
      (leviRationalPointHomeomorph i ν I).symm.continuous
  exact normalizedInductionCompactTrivialTwistFixedVectorsEquiv h
    (family.closedUnipotent I) hP (bernsteinLiteralLeviRep i ν I A) K hK χM hχM
    (Induction.compactSubgroup_le_unramifiedPullback_ker
      (fun c => (rationalNormCharacters (bernsteinLeviScheme i ν I) c).toMul)
      (fun c => (rationalNormContinuousCharacter (bernsteinLeviScheme i ν I) c).continuous)
      r hr χ)

/-- Actual rational inertia equivalence in one fixed standard Levi gives an
equivalence of compact open fixed spaces of normalized induction. -/
def rationalInertiaInductionFixedVectorsEquiv
    (I : Finset (SimpleRoot i ν))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    {A B : SmoothRep.{0,uF,uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I))}
    (hAB : IsRationalInertiaRelated (bernsteinLeviScheme i ν I) A B) :
    fixedVectors (rationalStandardInduction i ν family I A).representation K.toSubgroup ≃ₗ[ℂ]
      fixedVectors (rationalStandardInduction i ν family I B).representation K.toSubgroup := by
  let χ := hAB.choose
  let e : B ≅ rationalUnramifiedTwist (bernsteinLeviScheme i ν I) χ A :=
    Classical.choice hAB.choose_spec
  let e' := (normalizedInductionFunctor (family.decomposition I)
    (family.closedUnipotent I)).mapIso
      ((SmoothRep.pullbackFunctor (leviRationalPointHomeomorph i ν I).symm).mapIso e.symm)
  exact (rationalUnramifiedInductionFixedVectorsEquiv i ν family I K hK χ A).symm.trans
    (fixedVectorsEquiv (SmoothRep.equivOfIso e') K.toSubgroup)

/-- Nontriviality of induced compact open fixed vectors is constant on the
actual rational inertia orbit of an arbitrary action of the fixed Levi. -/
theorem nontrivial_inductionFixedVectors_iff_of_rationalInertiaRelated
    (I : Finset (SimpleRoot i ν))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    {A B : SmoothRep.{0,uF,uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I))}
    (hAB : IsRationalInertiaRelated (bernsteinLeviScheme i ν I) A B) :
    Nontrivial (fixedVectors (rationalStandardInduction i ν family I A).representation
      K.toSubgroup) ↔
    Nontrivial (fixedVectors (rationalStandardInduction i ν family I B).representation
      K.toSubgroup) :=
  (rationalInertiaInductionFixedVectorsEquiv i ν family I K hK hAB).toEquiv.nontrivial_congr

end Langlands.CuspidalSupport
