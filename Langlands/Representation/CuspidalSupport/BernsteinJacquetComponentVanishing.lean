import Langlands.Representation.CuspidalSupport.BernsteinJacquetInertiaExclusion
import Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement
import Langlands.Representation.Category.ConstituentSerre
import Langlands.CategoryTheory.Renard.CategoryDecompositionSimpleClassesProof

/-! # Vanishing of the unwanted Jacquet inertia components -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Components

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance jacquetComponentPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

variable (π : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
  (h : IsRationalInertiaCategoryDecomposition G π)
  (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))

/-- Choose the two actual components supplied by an inertia decomposition.
The `true` component is in the inertia block and `false` in its complement. -/
def rationalInertiaComponentFamily : Bool → SmoothRep.{0, uF, uV} ℂ (rationalPoints G) :=
  (h.1 V).choose

/-- The chosen component inclusions, with the original object as coproduct vertex. -/
def rationalInertiaComponentCofan : Cofan (rationalInertiaComponentFamily G π h V) :=
  Cofan.mk V (h.1 V).choose_spec.choose

/-- The choice retains the actual coproduct universal property. -/
def rationalInertiaComponentIsColimit : IsColimit (rationalInertiaComponentCofan G π h V) :=
  (h.1 V).choose_spec.choose_spec.2.some

/-- The components retain the prescribed all/no-subquotient inertia properties. -/
theorem rationalInertiaComponentFamily_property (b : Bool) :
    rationalInertiaDecompositionProperties G π b (rationalInertiaComponentFamily G π h V b) :=
  (h.1 V).choose_spec.choose_spec.1 b

/-- An object has no constituents in the inertia orbit exactly when its
chosen block component is zero. No finite-length assumption is used. -/
theorem rationalInertiaComponent_isZero_iff_complement :
    IsZero (rationalInertiaComponentFamily G π h V true) ↔
      rationalInertiaComplementProperty G π V := by
  let A := rationalInertiaComponentFamily G π h V
  let s := rationalInertiaComponentCofan G π h V
  let hs := rationalInertiaComponentIsColimit G π h V
  have hA := rationalInertiaComponentFamily_property G π h V
  constructor
  · intro hz D hD hDV hπD
    let e : SmoothRep.directSum A ≅ V :=
      SmoothRep.mkIso (SmoothRep.cofanDirectSumEquiv A s hs)
    obtain ⟨b, hb⟩ := SmoothRep.irreducibleSubquotient_directSum A hD
      (hDV.of_iso_right e.symm)
    cases b
    · exact hA false D hD hb hπD
    · exact SmoothRep.not_isSubquotient_of_isZero hz hD hb
  · intro hV
    have hmono : Mono (s.inj true) :=
      Langlands.Renard.CategoryDecompositionSimpleClassesProof.cofan_leg_mono hs true
    have hAV : SmoothRep.IsSubquotient (A true) V :=
      SmoothRep.IsSubrepresentation.isSubquotient
        ⟨s.inj true, (SmoothRep.mono_iff_injective _).mp hmono⟩
    exact (SmoothRep.isZero_iff_subsingleton_carrier _).mpr
      (subsingleton_of_rationalInertiaBlock_and_complement (hA true)
        (rationalInertiaComplementProperty_of_isSubquotient hV hAV))

end Components

section Bernstein

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance jacquetComponentGroupAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance jacquetComponentBernsteinPointTopology : TopologicalSpace (rationalPoints G) := pointTopology
local instance jacquetComponentLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance jacquetComponentLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance jacquetComponentLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance jacquetComponentLeviPointTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Given the genuine inertia decompositions on the actual standard Levis,
condition (iii) of the published characterization is exactly vanishing of
all components prohibited by Renard's original condition (iii). -/
theorem bernsteinJacquetExclusion_iff_zero_inertiaComponents
    (hD : ∀ b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      IsRationalInertiaCategoryDecomposition (bernsteinLeviScheme i ν b.roots) b.representation)
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :
    BernsteinJacquetExclusion i ν family a V ↔
      ∀ b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
        ¬ IsBernsteinInertiaRelated i ν family a b →
          IsZero (rationalInertiaComponentFamily (bernsteinLeviScheme i ν b.roots)
            b.representation (hD b) (bernsteinSchemeJacquet i ν family b.roots V) true) := by
  rw [bernsteinJacquetExclusion_iff_inertiaComplement]
  exact ⟨fun h b hab => (rationalInertiaComponent_isZero_iff_complement _ _ _ _).mpr (h b hab),
    fun h b hab => (rationalInertiaComponent_isZero_iff_complement _ _ _ _).mp (h b hab)⟩

end Bernstein

end Langlands.CuspidalSupport
