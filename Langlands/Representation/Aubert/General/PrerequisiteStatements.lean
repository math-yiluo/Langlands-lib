import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Representation-theoretic prerequisite targets for the general Aubert adapters

Proposition definitions for the actual rational points
`G(F) = RationalPoint F G.X` (points tested by the identity of `Spec F`) of a
connected reductive group `G` over a nonarchimedean local field `F`, with the
pinned point topology `rationalPointTopology F G.X`, and for the actual dynamic
subgroups `P(χ)(F)`, `Z(χ)(F)` and `U(χ)(F)` of every cocharacter `χ : 𝔾_m → G`
over `F`. None of these propositions is assumed or proved here.

Each statement quantifies over the field `F` together with its local-field
instances. Topological facts about `G(F)` that are needed only to form the
functors or the contragredient (topological group, local compactness, the
nonarchimedean property, closedness of `U(χ)(F)`) are explicit hypotheses on this
one pinned topology. They are true facts (Conrad, Prop. 2.1; Renard V.2.1), not
alternative topologies.

One proved bridge is included: the two finite-length targets, together with the
structural inputs of the exactness theorems of `AlternatingOperator`, give the
adapters' named prerequisite `ParabolicFiniteLength` for every actual dynamic
decomposition of `G(F)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

universe u uV

/-- **Finite length implies admissible for `G(F)`** (Renard VI.6.3, Howe; the
direction used is "finite length ⇒ admissible", via VI.2.2 for irreducibles).
For every nonarchimedean local field `F` and every connected reductive group `G`
over `F`, every smooth complex representation of `G(F)`, with its point
topology, of finite length is admissible. -/
def RationalPointsFiniteLengthAdmissibleStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ A : SmoothRep.{0, u, uV} ℂ (RationalPoint F G.X), A.HasFiniteLength → A.IsAdmissible

/-- **Finite length implies admissible for every dynamic Levi `Z(χ)(F)`**
(Renard VI.6.3 applied to the Levi). For every nonarchimedean local field `F`,
every connected reductive `G` over `F` and every cocharacter `χ`, every
finite-length smooth complex representation of the actual subgroup
`Z(χ)(F) ≤ G(F)`, with the subspace topology, is admissible. -/
def DynamicLeviFiniteLengthAdmissibleStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ A : SmoothRep.{0, u, uV} ℂ ((Dynamic.centralizer χ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Subgroup (RationalPoint F G.X)),
      A.HasFiniteLength → A.IsAdmissible

/-- **Smooth contragredients of finite-length representations of `G(F)` have
finite length** (derived from Renard VI.6.3, I.5.1 Corollaire and the exactness
of the smooth dual). The hypothesis that `G(F)` is a topological group for the
point topology is needed to form the contragredient. -/
def RationalPointsContragredientFiniteLengthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [IsTopologicalGroup (RationalPoint F G.X)],
      ContragredientPreservesFiniteLength.{u, uV} (RationalPoint F G.X)

/-- **Smooth contragredients of finite-length representations of every dynamic
Levi `Z(χ)(F)` have finite length** (the previous statement for the Levi). -/
def DynamicLeviContragredientFiniteLengthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [IsTopologicalGroup (RationalPoint F G.X)],
      ContragredientPreservesFiniteLength.{u, uV}
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
          Subgroup (RationalPoint F G.X))

/-- **Normalized parabolic induction preserves finite length** (Renard VI.6.2 and
the paragraph after it). For every nonarchimedean local field `F`, every
connected reductive `G` over `F` and every cocharacter `χ`, the actual normalized
induction functor `SmoothRep ℂ Z(χ)(F) ⥤ SmoothRep ℂ G(F)` of the decomposition
`P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)` sends finite-length representations to
finite-length representations. -/
def DynamicInductionFiniteLengthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (RationalPoint F G.X)] [NonarchimedeanGroup (RationalPoint F G.X)]
      (hU : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
        Set (RationalPoint F G.X))),
      SmoothRep.PreservesFiniteLength (normalizedInductionFunctor.{u, uV}
        (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU)

/-- **Normalized Jacquet restriction preserves finite length** (Renard VI.6.4).
For every nonarchimedean local field `F`, every connected reductive `G` over `F`
and every cocharacter `χ`, the actual normalized Jacquet functor
`SmoothRep ℂ G(F) ⥤ SmoothRep ℂ Z(χ)(F)` of `P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)` sends
finite-length representations to finite-length representations. -/
def DynamicJacquetFiniteLengthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (RationalPoint F G.X)] [NonarchimedeanGroup (RationalPoint F G.X)]
      (hU : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
        Set (RationalPoint F G.X))),
      SmoothRep.PreservesFiniteLength (jacquetFunctor.{u, uV}
        (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU)

/-- The two finite-length targets, together with the structural inputs of the
exactness theorems of `AlternatingOperator` (Hausdorff `G(F)`, closed `P(χ)(F)`,
continuous projection, and `U(χ)(F)` a limit of compact subgroups), give the
adapters' named prerequisite `ParabolicFiniteLength` for the actual dynamic
decomposition of `G(F)`. -/
theorem rational_parabolicFiniteLength
    (hi : DynamicInductionFiniteLengthStatement.{u, uV})
    (hr : DynamicJacquetFiniteLengthStatement.{u, uV})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (RationalPoint F G.X)] [NonarchimedeanGroup (RationalPoint F G.X)]
      [T2Space (RationalPoint F G.X)]
      (hU : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
        Set (RationalPoint F G.X)))
      (_hP : IsClosed ((Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
        Set (RationalPoint F G.X)))
      (_hproj : Continuous (dynamic_isSemidirectDecomposition χ
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))).projection)
      (_hUc : Jacquet.Localization.IsLimitOfCompactSubgroups
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
          Subgroup (RationalPoint F G.X))),
      ParabolicFiniteLength.{u, uV}
        (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  intro _ _ _ hU hP hproj hUc
  exact ParabolicFiniteLength.of_preservesFiniteLength
    (compactOpenCofinal_of_nonarchimedean _) _ hU hP hproj hUc (hi F G hG χ hU) (hr F G hG χ hU)

end Langlands.Aubert.General
