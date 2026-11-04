import Langlands.Representation.Exponents.NormalizedJacquetSplitComponent
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Normalized exponents for arbitrary represented parabolics

Renard 2026, VII.1.1 (printed p.220/PDF p.226), with the normalization of
VI.1.2 (printed pp.135–136/PDF pp.141–142). All subgroups are literal images
of the specified group-scheme maps on rational points.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {G H P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- The literal image of a group-scheme homomorphism on rational points. -/
abbrev pointImage (j : H ⟶ G) : Subgroup (rationalPoints G) :=
  (rationalPoints.map j).range

/-- Split-component points mapped into the actual Levi point image. -/
def splitComponentPointsMap (j : M ⟶ G) {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : A.toGrp ⟶ M) : rationalPoints A.toGrp →* pointImage j :=
  (rationalPoints.map j).rangeRestrict.comp (rationalPoints.map a)

@[simp] theorem splitComponentPointsMap_val (j : M ⟶ G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)
    (t : rationalPoints A.toGrp) :
    (splitComponentPointsMap j a t : rationalPoints G) =
      rationalPoints.map j (rationalPoints.map a t) := rfl

/-- Centrality passes from the actual split component to the Levi image. -/
theorem splitComponentPointsMap_mem_center (j : M ⟶ G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (t : rationalPoints A.toGrp) :
    splitComponentPointsMap j a t ∈ Subgroup.center (pointImage j) := by
  apply Subgroup.map_center_le_center (rationalPoints.map j).rangeRestrict_surjective
  exact ⟨rationalPoints.map a t, ha.isCentralSplitTorus.isCentral.map_mem_center t, rfl⟩

/-- The Levi image normalizes the radical image, by the radical's all-test normality. -/
theorem pointImage_le_normalizer (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    pointImage (l ≫ p) ≤ Subgroup.normalizer (pointImage (r ≫ p) : Set (rationalPoints G)) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨m, rfl⟩ _ ⟨z, rfl⟩
  have hz : rationalPoints.map r z ∈ (SubgroupFunctor.range r).carrier (Over.mk (𝟙 _)) :=
    ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := hr.1.isNormal (Over.mk (𝟙 _))
    (rationalPoints.map l m) (rationalPoints.map r z) (Subgroup.mem_top _) hz
  refine ⟨w, ?_⟩
  change rationalPoints.map p (rationalPoints.map r w) =
    rationalPoints.map p (rationalPoints.map l m) *
      rationalPoints.map p (rationalPoints.map r z) *
        (rationalPoints.map p (rationalPoints.map l m))⁻¹
  rw [show rationalPoints.map r w = _ from hw, map_mul, map_mul, map_inv]

section Transport

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ] {B : Type w} [Group B] [TopologicalSpace B]
  {N L N' L' : Subgroup Γ}

/-- Equality of the actual subgroups and the point map preserves normalized weights.
Both Levi groups carry the topology induced from the same ambient group. -/
theorem normalizedGeneralizedWeight_congr
    (hN : IsClosed (N : Set Γ)) (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (hN' : IsClosed (N' : Set Γ)) (hLN' : L' ≤ Subgroup.normalizer (N' : Set Γ))
    (π : SmoothRep.{0, u, v} ℂ Γ) (rho : B →* L) (rho' : B →* L')
    (hrho : ∀ t : B, rho t ∈ Subgroup.center L)
    (hrho' : ∀ t : B, rho' t ∈ Subgroup.center L')
    (eN : N = N') (eL : L = L')
    (erho : (MulEquiv.subgroupCongr eL).toMonoidHom.comp rho = rho') (χ : B →* ℂˣ) :
    IsGeneralizedWeight ((normalizedJacquetFunctor N L hN hLN).obj π).representation rho χ hrho ↔
      IsGeneralizedWeight ((normalizedJacquetFunctor N' L' hN' hLN').obj π).representation
        rho' χ hrho' := by
  cases eN
  cases eL
  have heq : rho = rho' := by
    ext t
    exact congrArg (fun f : B →* L => (f t : Γ)) erho
  subst rho'
  rfl

end Transport

section Topology

variable [TopologicalSpace k] [IsAffineHom G.X.hom]

local instance ambientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- A closed subgroup's literal point image is closed for the canonical topology. -/
theorem isClosed_pointImage [T2Space k] (j : H ⟶ G) (hj : IsClosedSubgroup j) :
    IsClosed (pointImage j : Set (rationalPoints G)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact isClosed_rationalPoint_subgroup k (SubgroupFunctor.range j) j
    ⟨inferInstance, rfl⟩ hj

/-- Continuity into the subgroup topology is continuity of the actual composite map. -/
theorem continuous_splitComponentPointsMap (j : M ⟶ G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) :
    letI := RationalPointFamily.splitComponentPointTopology ha
    Continuous (splitComponentPointsMap j a) := by
  have := ha.isAffine
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := RationalPointFamily.splitComponentPointTopology ha
  exact continuous_induced_rng.mpr (continuous_rationalPointMap k (a ≫ j).hom.hom)

/-- Closedness for the literal image of a composite of closed subgroup maps. -/
theorem isClosed_pointImage_comp [T2Space k] (p : P ⟶ G) (j : H ⟶ P)
    (hp : IsClosedSubgroup p) (hj : IsClosedSubgroup j) :
    IsClosed (pointImage (j ≫ p) : Set (rationalPoints G)) := by
  have : IsClosedImmersion p.hom.hom.left := hp
  have : IsClosedImmersion j.hom.hom.left := hj
  apply isClosed_pointImage
  change IsClosedImmersion (j.hom.hom.left ≫ p.hom.hom.left)
  infer_instance

section Jacquet

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- Actual normalized Jacquet restriction for the specified parabolic and Levi.
The matching multiplication isomorphism records the chosen decomposition.
Its construction needs only the radical's closedness and the Levi's normalization. -/
abbrev jacquetFunctor
    (_hl : IsRationalLeviSubgroup l) (_hmul : IsIso (subgroupMultiplication l r)) :
    SmoothRep.{0, u, v} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p)) :=
  normalizedJacquetFunctor (pointImage (r ≫ p)) (pointImage (l ≫ p))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr)

/-- The action is the actual coinvariant action times the inverse half Haar modulus. -/
theorem jacquetFunctor_obj_splitComponentPointsMap_apply
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (t : rationalPoints A.toGrp) (x : π) :
    ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
        (splitComponentPointsMap (l ≫ p) a t)
        (Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x) =
      ((HaarModulus.closedInverseHalfCharacter (pointImage (r ≫ p))
          (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
          (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr)
          (splitComponentPointsMap (l ≫ p) a t) : ℂˣ) : ℂ) •
        Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1
          (π.representation (splitComponentPointsMap (l ≫ p) a t) x) :=
  normalizedJacquetFunctor_obj_apply _ _ _ _ π _ x

/-- The compact-open union of uniform generalized character spaces in `r_P π`. -/
def normalizedJacquetWeightSpace (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    Subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π).representation :=
  generalizedWeightSpace ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
    (splitComponentPointsMap (l ≫ p) a) χ
    (splitComponentPointsMap_mem_center (l ≫ p) ha)

/-- A smooth split-component character with nonzero normalized Jacquet weight space. -/
def IsNormalizedJacquetExponent (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) : Prop :=
  letI := RationalPointFamily.splitComponentPointTopology ha
  IsGeneralizedWeight ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
    (splitComponentPointsMap (l ≫ p) a) χ
    (splitComponentPointsMap_mem_center (l ≫ p) ha)

/-- Renard's `Exp(A, r_P π)` for the specified arbitrary parabolic. -/
def normalizedJacquetExponents (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Set (rationalPoints A.toGrp →* ℂˣ) :=
  {χ | IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ}

theorem mem_normalizedJacquetExponents (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    χ ∈ normalizedJacquetExponents p l r hp hl hr hmul ha π ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ :=
  Iff.rfl

theorem isNormalizedJacquetExponent_iff_isOpen_ker_and (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ↔
      @IsOpen _ (RationalPointFamily.splitComponentPointTopology ha)
        (χ.ker : Set (rationalPoints A.toGrp)) ∧
        normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ ≠ ⊥ :=
  Iff.rfl

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
include hp hl in
/-- The literal Levi image is closed in the canonical ambient point topology. -/
theorem isClosed_leviPoints :
    IsClosed (pointImage (l ≫ p) : Set (rationalPoints G)) :=
  isClosed_pointImage_comp p l hp.isClosedSubgroup hl.isClosedSubgroup

/-- Membership retains Renard's compact-open fixed-space union and one uniform power. -/
theorem mem_normalizedJacquetWeightSpace_fixed (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ)
    (x : (jacquetFunctor p l r hp hr hl hmul).obj π) :
    x ∈ normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ ↔
      ∃ K : HarishChandraSchwartz.CompactOpenSubgroup (pointImage (l ≫ p)),
        x ∈ fixedVectors ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
          K.toSubgroup ∧
        ∃ d : ℕ, ∀ t : rationalPoints A.toGrp,
          ((((jacquetFunctor p l r hp hr hl hmul).obj π).representation
            (splitComponentPointsMap (l ≫ p) a t) - (χ t : ℂ) • 1) ^ d) x = 0 := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  exact mem_generalizedWeightSpace _ _ χ _ x

/-- The compact-open condition is automatic because the actual Jacquet module is smooth. -/
theorem mem_normalizedJacquetWeightSpace (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ)
    (x : (jacquetFunctor p l r hp hr hl hmul).obj π) :
    x ∈ normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ ↔
      ∃ d : ℕ, ∀ t : rationalPoints A.toGrp,
        ((((jacquetFunctor p l r hp hr hl hmul).obj π).representation
          (splitComponentPointsMap (l ≫ p) a t) - (χ t : ℂ) • 1) ^ d) x = 0 := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  exact mem_generalizedWeightSpace_of_isSmooth _ χ _
    ((jacquetFunctor p l r hp hr hl hmul).obj π).isSmooth x

/-- The nonzero weight-space condition is the generic uniform eigencharacter condition. -/
theorem normalizedJacquetWeightSpace_ne_bot_iff (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ ≠ ⊥ ↔
      IsGeneralizedEigencharacter
        (((jacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
          (splitComponentPointsMap (l ≫ p) a)) χ := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  exact generalizedWeightSpace_ne_bot_iff _ χ _
    ((jacquetFunctor p l r hp hr hl hmul).obj π).isSmooth

/-- Continuity makes the eigencharacter's open-kernel condition automatic. -/
theorem isNormalizedJacquetExponent_iff (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ↔
      IsGeneralizedEigencharacter
        (((jacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
          (splitComponentPointsMap (l ≫ p) a)) χ := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let := RationalPointFamily.splitComponentPointTopology ha
  exact isGeneralizedWeight_iff _ ((jacquetFunctor p l r hp hr hl hmul).obj π).isSmooth _
    (continuous_splitComponentPointsMap (l ≫ p) ha)
    (splitComponentPointsMap_mem_center (l ≫ p) ha) χ

/-- Comparison with the published standard-family definition on explicitly matching
radical/Levi point images and split-component maps. No conjugacy or standard reduction
is asserted. The topology and the quotient action are transported by these equalities. -/
theorem isNormalizedJacquetExponent_iff_standard (ha : IsSplitComponent a)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (j : M ⟶ G) (hj : (standardLevi i ν (RationalPointFamily.rootSet i ν I)).IsRepresentedBy j)
    (h : IsSemidirectDecomposition (RationalPointFamily.parabolic i ν I)
      (RationalPointFamily.levi i ν I) (RationalPointFamily.unipotent i ν I))
    (hU : IsClosed (RationalPointFamily.unipotent i ν I : Set (rationalPoints G)))
    (eU : pointImage (r ≫ p) = RationalPointFamily.unipotent i ν I)
    (eM : pointImage (l ≫ p) = RationalPointFamily.levi i ν I)
    (eA : (MulEquiv.subgroupCongr eM).toMonoidHom.comp (splitComponentPointsMap (l ≫ p) a) =
      RationalPointFamily.splitComponentPointsMap i ν I j hj a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ↔
      RationalPointFamily.IsNormalizedJacquetExponent i ν I j hj h hU ha π χ := by
  let := RationalPointFamily.splitComponentPointTopology ha
  exact normalizedGeneralizedWeight_congr
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr) hU h.levi_le_normalizer π _ _
    (splitComponentPointsMap_mem_center (l ≫ p) ha)
    (RationalPointFamily.splitComponentPointsMap_mem_center i ν I j hj ha) eU eM eA χ

end Jacquet

end Topology

end Langlands.Aubert.General.RepresentedParabolic
