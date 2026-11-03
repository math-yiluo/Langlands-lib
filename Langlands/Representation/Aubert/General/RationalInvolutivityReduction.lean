import Langlands.Representation.Aubert.General.InvolutivityReduction
import Langlands.Representation.Aubert.General.RationalInductionTarget
import Langlands.Representation.Aubert.General.RationalInvolutivityTarget
import Langlands.Representation.Aubert.General.RestrictedLeviTopology

/-!
# Involutivity on the actual rational-point family from its named inputs

Aubert's proof of Theorem 1.7(3) (printed p. 2183) uses Theorem 1.7(2),
transitivity of normalized induction and Jacquet restriction, and the
identity `i_S ∘ r_S = id`. `InvolutivityReduction` carries out this
computation for an arbitrary family. This module specializes it to the
actual standard family of `RationalPoint k G.X`.

The Levi data that `RationalInductionCompatibilityStatement` takes as
premises are partly derived here from the premises of
`RationalInvolutivityStatement`: closedness of the Levis, continuity of the
restricted projections and the compact-limit property of the restricted
radicals. The intersection statement, finite-length preservation inside the
Levis, the induction compatibility, the term transitivity and the top term
stay explicit hypotheses. The last three are stated here as the named
propositions `RationalTermTransitivityStatement` and
`RationalTopTermStatement` (with the published
`RationalInductionCompatibilityStatement`), and finite length inside the
Levis as `RationalLeviFiniteLengthStatement`. No instance of any of them is
proved here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

namespace IsSemidirectDecomposition

variable {H : Type*} [Group H] [TopologicalSpace H] {P M U : Subgroup H}

/-- In a Hausdorff group, the Levi of a decomposition of a closed parabolic
with continuous projection is closed: it is the set of points of `P` fixed
by the projection. -/
theorem isClosed_levi [T2Space H] (h : IsSemidirectDecomposition P M U)
    (hP : IsClosed (P : Set H)) (hproj : Continuous h.projection) :
    IsClosed (M : Set H) := by
  have hcl : IsClosed {p : P | ((h.projection p : M) : H) = (p : H)} :=
    isClosed_eq (continuous_subtype_val.comp hproj) continuous_subtype_val
  have himage : (M : Set H) =
      Subtype.val '' {p : P | ((h.projection p : M) : H) = (p : H)} := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, h.levi_le hx⟩, congrArg Subtype.val (h.projection_levi ⟨x, hx⟩), rfl⟩
    · rintro ⟨p, hp, rfl⟩
      rw [← show ((h.projection p : M) : H) = (p : H) from hp]
      exact (h.projection p).2
  rw [himage]
  exact hP.isClosedEmbedding_subtypeVal.isClosedMap _ hcl

omit [TopologicalSpace H] in
/-- The projection of a decomposition read inside a subgroup `L` is the
ambient projection. -/
theorem coe_projection_subgroupOf {L : Subgroup H} (h : IsSemidirectDecomposition P M U)
    (hL : IsSemidirectDecomposition (P.subgroupOf L) (M.subgroupOf L) (U.subgroupOf L))
    (x : P.subgroupOf L) :
    (((hL.projection x : M.subgroupOf L) : L) : H) =
      ((h.projection ⟨((x : L) : H), x.2⟩ : M) : H) := by
  have hm : h.projection ⟨((x : L) : H), x.2⟩ =
      ⟨(((hL.projection x : M.subgroupOf L) : L) : H), (hL.projection x).2⟩ := by
    rw [h.projection_eq_iff]
    have hmem := hL.projection_inv_mul_mem x
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  rw [hm]

end IsSemidirectDecomposition

namespace RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rationalInvolutivityPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

section LeviPremises

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [T2Space (RationalPoint k G.X)]
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hproj : ∀ I, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I).projection)
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))

include hP hproj in
/-- The actual standard Levis are closed. -/
theorem levi_isClosed (J : Finset (SimpleRoot i ν)) :
    IsClosed (levi i ν J : Set (RationalPoint k G.X)) :=
  (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J).isClosed_levi
    (hP J) (hproj J)

include hP hproj hUc in
/-- The actual radicals of the standard parabolics inside a standard Levi are
limits of compact subgroups. -/
theorem isLimitOfCompactSubgroups_leviUnipotent (J : Finset (SimpleRoot i ν))
    (I : Finset J) :
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)) :=
  isLimitOfCompactSubgroups_subgroupOf _ _ (levi_isClosed i ν hStandard hG hi hν hP hproj J)
    (hUc (leviIndex J I))

end LeviPremises

section Reduction

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hproj : ∀ I, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I).projection)
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hiFl : ∀ I, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)))
  (hrFl : ∀ I, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)))
  [Mono i.hom.hom.left] (hRoots : HasRelativeRootSystem i)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hiLFl : ∀ J, letI := (levi_isClosed i ν hStandard hG hi hν hP hproj J).locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)))
  (hrLFl : ∀ J, letI := (levi_isClosed i ν hStandard hG hi hν hP hproj J).locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Mono i.hom.hom.left] in
include hiLFl hrLFl hUc in
/-- The finite-length data inside the actual standard Levis, with the
closedness of the Levis, the continuity of the restricted projections and the
compact-limit property of the restricted radicals derived. -/
theorem standardLeviParabolicFiniteLength_of_premises (J : Finset (SimpleRoot i ν)) :
    letI := (levi_isClosed i ν hStandard hG hi hν hP hproj J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val) :=
  standardLeviParabolicFiniteLength i ν hInter hG hi hν hU hP J
    (levi_isClosed i ν hStandard hG hi hν hP hproj J)
    (continuous_standardLeviProjection i ν hStandard hInter hG hi hν hproj J)
    (isLimitOfCompactSubgroups_leviUnipotent i ν hStandard hG hi hν hP hproj hUc J)
    (hiLFl J) (hrLFl J)

/-- The published rational induction compatibility, read as the general
`InductionCompatibilityStatement` of the actual standard family with the
derived Levi data. -/
theorem inductionCompatibilityStatement_of_rational
    (hcompat : RationalInductionCompatibilityStatement.{u, v}) :
    letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    InductionCompatibilityStatement.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
      (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
      (levi_isClosed i ν hStandard hG hi hν hP hproj)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
      (standardLeviParabolicFiniteLength_of_premises i ν hStandard hG hi hν hU hP hproj hUc
        hInter hiLFl hrLFl) :=
  hcompat k G hG T i hi ν hν hStandard hRoots hInter hU hP hproj hUc hiFl hrFl
    (levi_isClosed i ν hStandard hG hi hν hP hproj)
    (continuous_standardLeviProjection i ν hStandard hInter hG hi hν hproj)
    (isLimitOfCompactSubgroups_leviUnipotent i ν hStandard hG hi hν hP hproj hUc)
    hiLFl hrLFl

/-- Aubert's Theorem 1.7(3) on the actual rational-point family, from the
published rational induction compatibility, term transitivity of the actual
family and the top term `i_S ∘ r_S = id`. -/
theorem rationalAlternatingOperator_comp_self
    (hcompat : RationalInductionCompatibilityStatement.{u, v})
    (htrans : letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      TermTransitivityStatement.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
        (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
        (levi_isClosed i ν hStandard hG hi hν hP hproj)
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (standardLeviParabolicFiniteLength_of_premises i ν hStandard hG hi hν hU hP hproj hUc
          hInter hiLFl hrLFl))
    (htop : letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      alternatingTerm.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
        (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
        Finset.univ = LinearMap.id) :
    (rationalAlternatingOperator.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
        hRoots).comp
      (rationalAlternatingOperator.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
        hRoots) = LinearMap.id :=
  letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  involutivityStatement_of_inductionCompatibility _ _ _ _ _ _ _ _ _
    (inductionCompatibilityStatement_of_rational i ν hStandard hG hi hν hU hP hproj hUc hiFl
      hrFl hRoots hInter hiLFl hrLFl hcompat) htrans htop

end Reduction

/-- Finite-length preservation of normalized induction and normalized Jacquet
restriction for the standard parabolics inside every actual standard Levi, on
the canonical rational-point topology. The premises are those of
`RationalInvolutivityStatement` without the root-system hypothesis, together
with the intersection statement and the closedness of the Levis. This declares
a target; no instance is proved. -/
def RationalLeviFiniteLengthStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (_hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
      (_hproj : ∀ I, Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection)
      (_hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
      (_hiFl : ∀ I, PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (_hrFl : ∀ I, PreservesFiniteLength
        (jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X)))
      (J : Finset (SimpleRoot i ν)),
      letI := (hM J).locallyCompactSpace
      ∀ I : Finset J,
        PreservesFiniteLength
            (normalizedInductionFunctor.{u, max (u + 1) v}
              (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
              ((hU (leviIndex J I)).preimage continuous_subtype_val)) ∧
          PreservesFiniteLength
            (jacquetFunctor.{u, max (u + 1) v}
              (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
              ((hU (leviIndex J I)).preimage continuous_subtype_val))

/-- `TermTransitivityStatement` for the actual standard family, with the Levi
data of `RationalInductionCompatibilityStatement`, for any enumeration of the
simple roots: `i_J ∘ i^{L_J}_I ∘ r^{L_J}_I ∘ r_J = i_I ∘ r_I` on exact K0. The
premises are those of `RationalInductionCompatibilityStatement` with the
root-system hypothesis replaced by a `Fintype` instance. This declares a
target; no instance is proved. -/
def RationalTermTransitivityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
      (hproj : ∀ I, Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection)
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
      (hiFl : ∀ I, PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hrFl : ∀ I, PreservesFiniteLength
        (jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X)))
      (hLproj : ∀ (J : Finset (SimpleRoot i ν)) (I : Finset J),
        Continuous (standardLeviProjection i ν hInter hG hi hν J I))
      (hLUc : ∀ (J : Finset (SimpleRoot i ν)) (I : Finset J),
        Jacquet.Localization.IsLimitOfCompactSubgroups
          ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)))
      (hiLFl : ∀ J, letI := (hM J).locallyCompactSpace
        ∀ I : Finset J, PreservesFiniteLength
          (normalizedInductionFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
            ((hU (leviIndex J I)).preimage continuous_subtype_val)))
      (hrLFl : ∀ J, letI := (hM J).locallyCompactSpace
        ∀ I : Finset J, PreservesFiniteLength
          (jacquetFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
            ((hU (leviIndex J I)).preimage continuous_subtype_val)))
      [Fintype (SimpleRoot i ν)],
      TermTransitivityStatement.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
        (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
        hM (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (fun J => standardLeviParabolicFiniteLength.{u, v} i ν hInter hG hi hν hU hP J (hM J)
          (hLproj J) (hLUc J) (hiLFl J) (hrLFl J))

/-- The top term `i_S ∘ r_S = id` of the actual standard family on exact K0,
for any enumeration of the simple roots. The premises are those of
`RationalInvolutivityStatement` with the root-system hypothesis replaced by a
`Fintype` instance. This declares a target; no instance is proved. -/
def RationalTopTermStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
      (hproj : ∀ I, Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection)
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
      (hiFl : ∀ I, PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hrFl : ∀ I, PreservesFiniteLength
        (jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      [Fintype (SimpleRoot i ν)],
      alternatingTerm.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
        (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
        Finset.univ = LinearMap.id

/-- Aubert's Theorem 1.7(3) on the actual rational-point family from its
named inputs: the intersection statement, finite length inside the standard
Levis, the induction compatibility of Theorem 1.7(2), term transitivity and
the top term. -/
theorem rationalInvolutivityStatement_of_reductions
    (hInter : StandardLeviIntersectionStatement.{u})
    (hLeviFl : RationalLeviFiniteLengthStatement.{u, v})
    (hcompat : RationalInductionCompatibilityStatement.{u, v})
    (htrans : RationalTermTransitivityStatement.{u, v})
    (htop : RationalTopTermStatement.{u, v}) :
    RationalInvolutivityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro _ _ _ ν hν hStandard hRoots hU hP hproj hUc hiFl hrFl
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  have hLFl := hLeviFl k G hG T i hi ν hν hStandard hInter hU hP hproj hUc hiFl hrFl
    (levi_isClosed i ν hStandard hG hi hν hP hproj)
  exact rationalAlternatingOperator_comp_self i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
    hRoots hInter (fun J I => (hLFl J I).1) (fun J I => (hLFl J I).2) hcompat
    (htrans k G hG T i hi ν hν hStandard hInter hU hP hproj hUc hiFl hrFl _
      (continuous_standardLeviProjection i ν hStandard hInter hG hi hν hproj)
      (isLimitOfCompactSubgroups_leviUnipotent i ν hStandard hG hi hν hP hproj hUc)
      (fun J I => (hLFl J I).1) (fun J I => (hLFl J I).2))
    (htop k G hG T i hi ν hν hStandard hU hP hproj hUc hiFl hrFl)

end RationalPointFamily

end Langlands.Aubert.General
