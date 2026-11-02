import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.PointDecomposition

/-!
# The actual standard family as semidirect decompositions

For a connected reductive group `G` over a field `k`, a maximal split torus
`i : T ⟶ G` and a generic cocharacter `ν`, the published standard family
`RationalPointFamily.parabolic/levi/unipotent i ν I`, indexed by finite sets `I`
of actual simple relative roots, consists of actual semidirect decompositions
`P_I(k) = L_I(k) ⋉ U_I(k)`, conditional on the published target
`GroupScheme.StandardCocharacterStatement`. That target identifies each standard
subgroup functor with the dynamic subgroup of a standard cocharacter. The
decomposition then comes from `dynamic_isSemidirectDecomposition`. With it, the
normalized induction and Jacquet functors between `G(k)` and every standard Levi,
and Aubert's operator for the standard family, are instances of the generic
constructions. The topology of `G(k)` is an instance argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

universe uV

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Conditional on `StandardCocharacterStatement`: for every standard cocharacter
`ζ` of `I`, the standard family at `I` equals the rational points of the dynamic
subgroups of `ζ`, and a standard cocharacter exists. -/
theorem exists_standardCocharacter_eq (hstd : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (I : Finset (SimpleRoot i ν)) :
    ∃ zeta : cocharacterLattice T, IsStandardCocharacter i ν (rootSet i ν I) zeta ∧
      parabolic i ν I =
        (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) ∧
      levi i ν I =
        (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) ∧
      unipotent i ν I =
        (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨⟨zeta, hzeta⟩, hall⟩ := hstd k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨hP, hM, hU⟩ := hall zeta hzeta
  refine ⟨zeta, hzeta, ?_, ?_, ?_⟩
  · change (standardParabolic i ν (rootSet i ν I)).carrier _ = _
    rw [hP]
  · change (standardLevi i ν (rootSet i ν I)).carrier _ = _
    rw [hM]
  · change (standardUnipotent i ν (rootSet i ν I)).carrier _ = _
    rw [hU]

/-- Conditional on `StandardCocharacterStatement`: the actual standard family is
an actual semidirect decomposition `P_I(k) = L_I(k) ⋉ U_I(k)` for every `I`. -/
theorem isSemidirectDecomposition (hstd : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (I : Finset (SimpleRoot i ν)) :
    IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I) := by
  have : IsSeparated G.X.hom := hG.isSeparated
  obtain ⟨zeta, _, hP, hM, hU⟩ := exists_standardCocharacter_eq hstd hG i hi ν hν I
  rw [hP, hM, hU]
  exact dynamic_isSemidirectDecomposition _ _

section Functors

variable [TopologicalSpace (RationalPoint k G.X)] [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- Normalized parabolic induction from the actual standard Levi `L_I(k)` to
`G(k)`, conditional on `StandardCocharacterStatement`. The topology of `G(k)` is
an instance argument. -/
def standardInductionFunctor (hstd : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X))) :
    SmoothRep.{0, u, uV} ℂ (levi i ν I) ⥤ SmoothRep.{0, u, max u uV} ℂ (RationalPoint k G.X) :=
  normalizedInductionFunctor (isSemidirectDecomposition hstd hG i hi ν hν I) hU

/-- Normalized Jacquet restriction from `G(k)` to the actual standard Levi
`L_I(k)`, conditional on `StandardCocharacterStatement`. -/
def standardJacquetFunctor (hstd : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X))) :
    SmoothRep.{0, u, uV} ℂ (RationalPoint k G.X) ⥤ SmoothRep.{0, u, uV} ℂ (levi i ν I) :=
  jacquetFunctor (isSemidirectDecomposition hstd hG i hi ν hν I) hU

/-- Aubert's unadjusted operator `D_G = ∑_{I ⊆ S} (-1)^{|I|} i_I ∘ r_I` for the
actual standard family of `G(k)`, indexed by the finite sets of actual simple
relative roots. It is conditional on `StandardCocharacterStatement` and on the
named finite-length hypotheses `hfl`. -/
def standardAlternatingOperator (hstd : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    [Fintype (SimpleRoot i ν)]
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hfl : ∀ I, ParabolicFiniteLength.{u, max u uV}
      (isSemidirectDecomposition hstd hG i hi ν hν I) (hU I)) :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, u, max u uV} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, u, max u uV} ℂ (RationalPoint k G.X) :=
  alternatingOperator (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition hstd hG i hi ν hν) hU hfl

/-- The standard operator is the general `alternatingOperator` of the standard
family, so `alternatingOperator_ofRepresentation` and
`alternatingOperator_of_isEmpty` apply to it. -/
theorem standardAlternatingOperator_eq (hstd : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    [Fintype (SimpleRoot i ν)]
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hfl : ∀ I, ParabolicFiniteLength.{u, max u uV}
      (isSemidirectDecomposition hstd hG i hi ν hν I) (hU I)) :
    standardAlternatingOperator.{u, uV} hstd hG i hi ν hν hU hfl =
      alternatingOperator (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition hstd hG i hi ν hν) hU hfl :=
  rfl

end Functors

end Langlands.Aubert.General.RationalPointFamily
