import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups

/-! # Modular characters of represented parabolics

For a represented parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P` and unipotent radical
`r : U ⟶ P`, the modular character of the literal image `P(F)` is the Haar modulus of
conjugation on `U(F)` as soon as `M(F)` is unimodular. No root presentation is needed: the
Levi projection is continuous by `continuous_projection_pointImage`, and `U(F)` is unimodular
by `isLimitOfCompactSubgroups_pointImage_radical`.

* `rationalPoints_modularCharacter_eq_one`: `G(F)` is unimodular, from
  `RationalReductiveUnimodularityStatement`.
* `modularCharacter_pointImage_of_leviUnimodular`: the parabolic modulus formula from
  unimodularity of `M(F)` in its own topology.
* `modularCharacter_pointImage_of_unimodularity`: the same formula from
  `RationalReductiveUnimodularityStatement`, applied to the connected reductive Levi.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviParabolicModulusPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The rational points of a connected reductive group are unimodular, given the general
reductive unimodularity statement. -/
theorem rationalPoints_modularCharacter_eq_one
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u}) (hG : IsConnectedReductive G)
    (g : rationalPoints G) : Measure.modularCharacter g = 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  exact hUnimod k G hG hStandard g

/-- If the Levi points `M(F)` are unimodular in their own topology, then the modular
character of the represented parabolic `P(F)` is the Haar modulus of conjugation on its
unipotent radical `U(F)`. -/
theorem modularCharacter_pointImage_of_leviUnimodular (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (hM :
      letI := leviPointTopology l hl
      letI : LocallyCompactSpace (rationalPoints M) :=
        leviPoints_locallyCompactSpace p l hp hl
      letI : NonarchimedeanGroup (rationalPoints M) :=
        leviPoints_nonarchimedeanGroup p l hp hl
      ∀ m : rationalPoints M, Measure.modularCharacter m = 1) :
    letI : LocallyCompactSpace (pointImage p) :=
      (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
    ∀ q : pointImage p, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter (pointImage (r ≫ p))
        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
        (pointImage p)
        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).le_normalizer
        q : ℝ≥0) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  have hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let : LocallyCompactSpace (pointImage p) :=
    (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
  let : LocallyCompactSpace (pointImage (r ≫ p)) := hU.locallyCompactSpace
  let : LocallyCompactSpace (pointImage (l ≫ p)) :=
    (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let e := leviPointsEquiv p l hp hl
  have hM' : ∀ m : pointImage (l ≫ p), Measure.modularCharacter m = 1 := by
    intro m
    simpa only [e.apply_symm_apply] using
      (modularCharacter_continuousMulEquiv e (e.symm m)).trans (hM (e.symm m))
  have hδU := isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1
  intro q
  simpa only [HaarModulus.closedRestrictCharacter_eq] using
    h.modularCharacter_eq_restrictCharacter_of_unimodular
      (continuous_projection_pointImage p l r hp hl hr hmul) hM'
      (by simpa only [IsUnimodularModulus, HaarModulus.closedNormalizerCharacter_eq]
        using hδU) q

/-- The modular character of a represented parabolic `P(F)` is the Haar modulus of
conjugation on its unipotent radical, given the general reductive unimodularity statement
(applied to the connected reductive Levi `M`). -/
theorem modularCharacter_pointImage_of_unimodularity
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u}) (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    letI : LocallyCompactSpace (pointImage p) :=
      (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
    ∀ q : pointImage p, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter (pointImage (r ≫ p))
        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
        (pointImage p)
        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).le_normalizer
        q : ℝ≥0) := by
  apply modularCharacter_pointImage_of_leviUnimodular hG p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : T2Space (rationalPoints M) := rationalPoint_t2Space k M
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  exact hUnimod k M hl.isConnectedReductive hStandard

end Langlands.Aubert.General.RepresentedParabolic
