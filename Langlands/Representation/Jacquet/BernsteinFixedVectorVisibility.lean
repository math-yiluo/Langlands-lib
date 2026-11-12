import Langlands.Representation.Jacquet.StandardIrreducibleFixedVectors
import Langlands.Representation.Jacquet.StandardBernsteinFixedVectorReduction
import Langlands.Representation.CuspidalSupport.BernsteinJacquetInertiaExclusion
import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison

/-! # Fixed-level visibility from actual association invariance -/

noncomputable section

set_option maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.Jacquet

open GroupScheme CuspidalSupport Aubert.General Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open BruhatTits.SpecialCompact

private theorem irreducible_smoothPullback
    {H J : Type uF} [Group H] [TopologicalSpace H] [Group J] [TopologicalSpace J]
    (e : H ≃ₜ* J) (A : SmoothRep.{0, uF, uV} ℂ J) (hA : A.IsIrreducible) :
    (SmoothRep.pullback e A).IsIrreducible :=
  (isIrreducible_comp_continuousMulEquiv_iff A.representation e).mpr hA

section Local

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance visibilityAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance visibilityAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance visibilityLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance visibilityLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance visibilityLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance visibilityLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

attribute [local irreducible] Standard.leviScheme

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
private theorem irreducible_standardRationalPullback
    (I J : Finset (SimpleRoot i ν))
    (e : bernsteinLeviScheme i ν I ≅ bernsteinLeviScheme i ν J)
    (A : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J)))
    (hA : A.IsIrreducible) :
    (rationalIsoPullback (H := bernsteinLeviScheme i ν I)
      (K := bernsteinLeviScheme i ν J) e A).IsIrreducible :=
  irreducible_smoothPullback (rationalPointIso (H := bernsteinLeviScheme i ν I)
    (K := bernsteinLeviScheme i ν J) e) A hA

/-- Put the second datum on the first datum's actual Levi using the given
algebraic conjugacy. Its cuspidality follows from same-Levi inertia, rather
than from an unproved general conjugation rule for the standard family. -/
def bernsteinInertiaRepresentativeOnSourceLevi
    (a b : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (c : RationalLeviConjugacy
      (Standard.leviHom i ν (rootSet i ν a.roots))
      (Standard.leviHom i ν (rootSet i ν b.roots)))
    (h : IsRationalInertiaRelated (bernsteinLeviScheme i ν a.roots)
      a.representation (rationalIsoPullback (H := bernsteinLeviScheme i ν a.roots)
        (K := bernsteinLeviScheme i ν b.roots) c.iso b.representation)) :
    BernsteinCuspidalDatum.{uF, uV} i ν family := by
  have hD : (rationalIsoPullback (H := bernsteinLeviScheme i ν a.roots)
        (K := bernsteinLeviScheme i ν b.roots) c.iso b.representation).IsIrreducible :=
    irreducible_standardRationalPullback i ν a.roots b.roots
      c.iso b.representation b.irreducible
  exact a.replaceInertia i ν family (rationalIsoPullback (H := bernsteinLeviScheme i ν a.roots)
        (K := bernsteinLeviScheme i ν b.roots) c.iso b.representation) hD h


/-- The replacement is untwisted-associated to the second datum by the
original actual conjugacy and the identity on the pulled-back action. -/
theorem bernsteinInertiaRepresentativeOnSourceLevi_associated
    (a b : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (c : RationalLeviConjugacy
      (Standard.leviHom i ν (rootSet i ν a.roots))
      (Standard.leviHom i ν (rootSet i ν b.roots)))
    (h : IsRationalInertiaRelated (bernsteinLeviScheme i ν a.roots)
      a.representation (rationalIsoPullback (H := bernsteinLeviScheme i ν a.roots)
        (K := bernsteinLeviScheme i ν b.roots) c.iso b.representation)) :
    AreBernsteinCuspidalDataAssociated i ν family
      (bernsteinInertiaRepresentativeOnSourceLevi i ν family a b c h) b := by
  unfold AreBernsteinCuspidalDataAssociated bernsteinInertiaRepresentativeOnSourceLevi
    BernsteinCuspidalDatum.replaceInertia
  exact ⟨c, ⟨Iso.refl _⟩⟩


/-- Expose the transferred support at its actual source-Levi coefficient. -/
private theorem sourceLevi_constituent_of_association
    (hAssociation : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (c : RationalLeviConjugacy
      (Standard.leviHom i ν (rootSet i ν a.roots))
      (Standard.leviHom i ν (rootSet i ν b.roots)))
    (h : IsRationalInertiaRelated (bernsteinLeviScheme i ν a.roots)
      a.representation (rationalIsoPullback (H := bernsteinLeviScheme i ν a.roots)
        (K := bernsteinLeviScheme i ν b.roots) c.iso b.representation))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hτ : IsBernsteinCuspidalSupport i ν family b τ) :
    τ.IsIrreducible ∧ SmoothRep.IsSubquotient τ
      (rationalStandardInduction i ν family a.roots
        (rationalIsoPullback (H := bernsteinLeviScheme i ν a.roots)
          (K := bernsteinLeviScheme i ν b.roots) c.iso b.representation)) := by
  let d := bernsteinInertiaRepresentativeOnSourceLevi i ν family a b c h
  have hd : AreBernsteinCuspidalDataAssociated i ν family d b :=
    bernsteinInertiaRepresentativeOnSourceLevi_associated i ν family a b c h
  have ht := (hAssociation d b hd τ).mpr hτ
  simpa only [IsBernsteinCuspidalSupport, bernsteinInduction,
    bernsteinInertiaRepresentativeOnSourceLevi, BernsteinCuspidalDatum.replaceInertia,
    rationalStandardInduction, d] using ht

/-- Same-Levi constituent visibility and actual untwisted association
invariance compare any two constituents whose cuspidal data are inertially
related. Both substantive inputs remain explicit. -/
theorem nontrivial_fixedVectors_iff_of_bernsteinInertiaRelated
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hAssociation : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (hVisibility : ∀ I,
      standardConstituentFixedVectorVisibility.{uF, max uF uV} i ν family I K)
    {a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family}
    (hab : IsBernsteinInertiaRelated i ν family a b)
    {π τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (hπ : IsBernsteinCuspidalSupport i ν family a π)
    (hτ : IsBernsteinCuspidalSupport i ν family b τ) :
    Nontrivial (fixedVectors π.representation K.toSubgroup) ↔
      Nontrivial (fixedVectors τ.representation K.toSubgroup) := by
  obtain ⟨c, h⟩ := hab
  have hτd := sourceLevi_constituent_of_association i ν family hAssociation a b c h τ hτ
  have hB := irreducible_standardRationalPullback i ν a.roots b.roots
    c.iso b.representation b.irreducible
  exact nontrivial_fixedVectors_constituents_iff_of_rationalInertiaRelated
    i ν family a.roots K hK (hVisibility a.roots)
    a.representation (rationalIsoPullback (H := bernsteinLeviScheme i ν a.roots)
      (K := bernsteinLeviScheme i ν b.roots) c.iso b.representation) a.irreducible hB h
    π τ hπ.1 hτd.1 hπ.2 hτd.2

/-- Equality of the genuine quotient class supplies the actual inertial
relation between chosen support witnesses. No support uniqueness or
decomposition theorem is required for this implication. -/
theorem bernsteinFixedVectorVisibility_of_association_and_constituentVisibility
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hAssociation : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (hVisibility : ∀ I,
      standardConstituentFixedVectorVisibility.{uF, max uF uV} i ν family I K) :
    bernsteinFixedVectorVisibility.{uF, uV} i ν family K := by
  intro s π τ hπ hτ
  obtain ⟨a, ha, hπa⟩ := hπ
  obtain ⟨b, hb, hτb⟩ := hτ
  exact nontrivial_fixedVectors_iff_of_bernsteinInertiaRelated i ν family K hK
    hAssociation hVisibility
    ((bernsteinInertialClass_eq_iff i ν family a b).mp (ha.trans hb.symm)) hπa hτb

/-- At the prescribed normal level, VI.9.4 supplies the same-Levi input.
Untwisted support invariance remains the other explicit input. -/
theorem bernsteinFixedVectorVisibility_of_subquotientGeneration_and_association
    (hGeneration : StandardFixedVectorSubquotientGenerationStatement.{uF, max uF uV})
    (hAssociation : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G)) (hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
    (hKK₀ : K.toSubgroup ≤ K₀)
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwasawa : ∀ x : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, x = m * n * k)
    (hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
      ∃ (B : CommGroupScheme (Spec (CommRingCat.of F))) (q : B.toGrp ⟶ T.toGrp),
        IsCompatibleStandardSplitComponent i ν J B q ∧
          StandardParabolicBasisMember i ν J q K.toSubgroup) :
    bernsteinFixedVectorVisibility.{uF, uV} i ν family K :=
  bernsteinFixedVectorVisibility_of_association_and_constituentVisibility
    i ν family K hK hAssociation
    (standardConstituentFixedVectorVisibility_of_subquotientGeneration
      i ν family hGeneration K hK K₀ hK₀ hKK₀ hnormal hIwasawa hIwahori)

end Local

/-- Global specialization at exactly the geometry of the host proposition.
The two source inputs remain explicit; all topology and family data are
constructed from the host hypotheses. -/
theorem standardBernsteinFixedVectorVisibility_of_subquotientGeneration_and_association
    (hGeneration : StandardFixedVectorSubquotientGenerationStatement.{uF, max uF uV})
    (hAssociation :
      ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
        [IsNonarchimedeanLocalField F]
        (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
        [LocallyOfFiniteType G.X.hom]
        (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T),
        letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
        letI : TopologicalSpace (rationalPoints G) := pointTopology
        ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
          (family : BernsteinStandardFamily i ν),
          BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family) :
    StandardBernsteinFixedVectorVisibilityStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro T i hi ν hν _hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  let : T2Space F := BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  exact bernsteinFixedVectorVisibility_of_subquotientGeneration_and_association
    i ν (standardBernsteinFamily i ν hG hi hν) hGeneration
    (hAssociation F G T i ν (standardBernsteinFamily i ν hG hi hν))
    K hK K₀ hK₀ hKK₀ hnormal hIwasawa hIwahori

end Langlands.Jacquet
