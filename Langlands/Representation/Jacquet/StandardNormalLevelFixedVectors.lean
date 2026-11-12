import Langlands.Representation.Induction.NormalLevelNormalizedFixedVectors
import Langlands.Representation.Jacquet.StandardBernsteinFixedVectorReduction
import Langlands.Representation.Jacquet.StandardFixedVectorGeneration
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport
import Langlands.Representation.Aubert.General.RationalOppositeChamber

/-! # Actual standard induction at a prescribed normal compact open level -/

noncomputable section

set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.GroupScheme

section Opposite

variable {F : Type uF} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The actual opposite standard unipotent subgroup meets the standard
parabolic trivially, on every test scheme. Only one standard cocharacter
and negation stability of relative roots are needed. -/
theorem eq_one_of_mem_standardOppositeUnipotent_of_mem_standardParabolic
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {J : Set (characterLattice T)}
    (hstandard : ∃ ζ, IsStandardCocharacter i ν J ζ)
    {W : Over (Spec (CommRingCat.of F))} {x : W ⟶ G.X}
    (hxUbar : x ∈ (standardUnipotent i (-ν) (Neg.neg '' J)).carrier W)
    (hxP : x ∈ (standardParabolic i ν J).carrier W) : x = 1 := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨ζ, hζ⟩ := hstandard
  have hminus := (mem_standardUnipotent i (-ν)).mp hxUbar (-ζ)
    (hζ.neg i ν hneg)
  rw [groupHom_neg_comp_eq_oppositeCocharacter i ζ] at hminus
  exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
    (CommGroupScheme.groupHom ζ ≫ i) hminus
    ((mem_standardParabolic i ν).mp hxP ζ hζ)

end Opposite

end Langlands.GroupScheme

namespace Langlands.Jacquet

open GroupScheme CuspidalSupport Aubert.General Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open BruhatTits.SpecialCompact

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance standardNormalLevelAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardNormalLevelTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The actual standard Levi projection preserves the specified literal
intersection whenever the specified level has its Iwahori decomposition. -/
theorem standard_projection_mem_of_iwahoriIntersection
    (I : Finset (SimpleRoot i ν)) (K : Subgroup (rationalPoints G))
    (hIwahori : HasIwahoriIntersectionDecomposition K (levi i ν I)
      (unipotent i ν I) (standardOppositeUnipotentPoints i ν (rootSet i ν I)))
    (p : parabolic i ν I) (hp : (p : rationalPoints G) ∈ K) :
    (((family.decomposition I).projection p : levi i ν I) : rationalPoints G) ∈ K := by
  apply (family.decomposition I).projection_mem_of_iwahoriIntersection hIwahori
    (fun x hxP hxUbar => ?_) p hp
  exact eq_one_of_mem_standardOppositeUnipotent_of_mem_standardParabolic i ν
    (relativeRootNegation F G family.connectedReductive T i family.maximalSplitTorus)
    (standardCocharacter F G family.connectedReductive T i family.maximalSplitTorus
      ν family.genericCocharacter (rootSet i ν I) (rootSet_subset i ν I)).1 hxUbar hxP

include family in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The minimal-standard factorization gives the actual product `G=P_I K₀`. -/
theorem standard_parabolic_factorization_of_minimal
    (I : Finset (SimpleRoot i ν)) (K₀ : Subgroup (rationalPoints G))
    (hIwasawa : ∀ x : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, x = m * n * k) :
    ∀ x : rationalPoints G, ∃ p : parabolic i ν I, ∃ k : K₀,
      x = (p : rationalPoints G) * (k : rationalPoints G) := by
  intro x
  obtain ⟨m, hm, n, hn, k, hk, he⟩ :=
    standard_factorization_of_minimal i ν family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter (rootSet i ν I)
      (standardCocharacter F G family.connectedReductive T i family.maximalSplitTorus
        ν family.genericCocharacter (rootSet i ν I) (rootSet_subset i ν I)).1
      K₀ hIwasawa x
  exact ⟨⟨m * n, (parabolic i ν I).mul_mem
    ((family.decomposition I).levi_le hm) ((family.decomposition I).unipotent_le hn)⟩,
    ⟨k, hk⟩, he⟩

/-- Actual restriction of normalized standard induced fixed vectors to `K₀`,
with values in the literal `K ∩ M_I` fixed space. -/
def standardNormalLevelEvaluation
    (I : Finset (SimpleRoot i ν))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup (levi i ν I)
      (unipotent i ν I) (standardOppositeUnipotentPoints i ν (rootSet i ν I)))
    (A : SmoothRep.{0, uF, uV} ℂ (levi i ν I)) :
    fixedVectors ((normalizedInductionFunctor (family.decomposition I)
      (family.closedUnipotent I)).obj A).representation K.toSubgroup →ₗ[ℂ]
        (K₀ → fixedVectors A.representation (K.toSubgroup.comap (levi i ν I).subtype)) :=
  normalLevelNormalizedEvaluation (family.decomposition I) (family.closedUnipotent I)
    (isClosed_standard_parabolic i ν standardCocharacter family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter I) K hK
    (standard_projection_mem_of_iwahoriIntersection i ν family I K.toSubgroup hIwahori)
    K₀ hnormal A

/-- At the target's prescribed normal level, normalized standard induction
has nonzero fixed vectors exactly when its literal Levi coefficient does. -/
theorem nontrivial_standardInduction_fixedVectors_iff
    (I : Finset (SimpleRoot i ν))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwasawa : ∀ x : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, x = m * n * k)
    (hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup (levi i ν I)
      (unipotent i ν I) (standardOppositeUnipotentPoints i ν (rootSet i ν I)))
    (A : SmoothRep.{0, uF, uV} ℂ (levi i ν I)) :
    Nontrivial (fixedVectors ((normalizedInductionFunctor (family.decomposition I)
      (family.closedUnipotent I)).obj A).representation K.toSubgroup) ↔
      Nontrivial (fixedVectors A.representation (K.toSubgroup.comap (levi i ν I).subtype)) :=
  nontrivial_fixedVectors_normalizedInduction_iff (family.decomposition I)
    (family.closedUnipotent I)
    (isClosed_standard_parabolic i ν standardCocharacter family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter I) K hK
    (standard_projection_mem_of_iwahoriIntersection i ν family I K.toSubgroup hIwahori)
    K₀ hnormal (standard_parabolic_factorization_of_minimal i ν family I K₀ hIwasawa) A

end Langlands.Jacquet
