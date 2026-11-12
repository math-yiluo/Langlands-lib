import Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationStatement
import Langlands.Representation.CuspidalSupport.RationalCuspidalBlockVisibility
import Langlands.Representation.CuspidalSupport.RationalInertiaCoproducts
import Langlands.Representation.Category.CoproductCompression
import Langlands.Representation.Tensor.SmoothSubquotients
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Jacquet exclusion and the unwanted inertia components of Renard VI.7.2 -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance instBernsteinJacquetInertiaExclusionGroupAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance instBernsteinJacquetInertiaExclusionTopology :
    TopologicalSpace (rationalPoints G) := pointTopology
local instance instBernsteinJacquetInertiaExclusionLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instBernsteinJacquetInertiaExclusionLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instBernsteinJacquetInertiaExclusionLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance instBernsteinJacquetInertiaExclusionLeviPointTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The Jacquet module transported back to the actual standard Levi scheme. -/
def bernsteinSchemeJacquet (I : Finset (SimpleRoot i ν))
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)) :=
  SmoothRep.pullback (leviRationalPointHomeomorph i ν I)
    ((normalizedJacquetFunctor (unipotent i ν I) (levi i ν I)
      (family.closedUnipotent I) (family.decomposition I).levi_le_normalizer).obj V)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Move a subquotient comparison across the canonical standard Levi homeomorphism. -/
theorem isSubquotient_bernsteinSchemeJacquet_iff
    (I : Finset (SimpleRoot i ν))
    (D : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    SmoothRep.IsSubquotient D (bernsteinSchemeJacquet i ν family I V) ↔
      SmoothRep.IsSubquotient (bernsteinLiteralLeviRep i ν I D)
        ((normalizedJacquetFunctor (unipotent i ν I) (levi i ν I)
          (family.closedUnipotent I) (family.decomposition I).levi_le_normalizer).obj V) := by
  let e := leviRationalPointHomeomorph i ν I
  let J := (normalizedJacquetFunctor (unipotent i ν I) (levi i ν I)
    (family.closedUnipotent I) (family.decomposition I).levi_le_normalizer).obj V
  have cancel (A : SmoothRep.{0, uF, uV} ℂ (levi i ν I)) :
      SmoothRep.pullback e.symm (SmoothRep.pullback e A) ≅ A :=
    SmoothRep.mkIso (equivOfRepresentationEq (by
      ext x v
      change A.representation (e (e.symm x)) v = A.representation x v
      rw [e.apply_symm_apply]))
  have cancel' : SmoothRep.pullback e (SmoothRep.pullback e.symm D) ≅ D :=
    SmoothRep.mkIso (equivOfRepresentationEq (by
      ext x v
      change D.representation (e.symm (e x)) v = D.representation x v
      rw [e.symm_apply_apply]))
  exact ⟨fun h => (h.pullback e.symm).of_iso_right (cancel J),
    fun h => (h.pullback e).of_iso_left cancel'⟩

omit [LocallyOfFiniteType G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
include family in
/-- An unramified character of the actual standard Levi kills every proper
standard radical inside that Levi. Compact containment proves this on points. -/
theorem bernsteinLeviUnramifiedCharacter_radical
    (J : Finset (SimpleRoot i ν))
    (χ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters (bernsteinLeviScheme i ν J) c).toMul))
    (I : Finset J) :
    (unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J) ≤
      (χ.val.toMonoidHom.comp
        (leviRationalPointHomeomorph i ν J).symm.toMonoidHom).ker := by
  intro x hx
  have hUc := isLimitOfCompactSubgroups_subgroupOf _ _ (family.closedLevi J)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter (leviIndex J I))
  obtain ⟨C, hCc, hC⟩ := hUc {⟨x, hx⟩} isCompact_singleton
  let f := (leviRationalPointHomeomorph i ν J).symm.toMonoidHom.comp
    ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)).subtype
  have hf : Continuous f :=
    (leviRationalPointHomeomorph i ν J).symm.continuous.comp continuous_subtype_val
  have hcompact : IsCompact (C.map f : Set (rationalPoints (bernsteinLeviScheme i ν J))) := by
    rw [Subgroup.coe_map]
    exact hCc.image hf
  apply χ.property
  apply Plancherel.compactSubgroup_le_rationalCommonNormKernel
    (bernsteinLeviScheme i ν J) (C.map f) hcompact
  exact ⟨⟨x, hx⟩, hC (Set.mem_singleton _), rfl⟩

/-- Actual inertia preserves the exact inside-Levi cuspidality used in a
Bernstein datum, without adding structural hypotheses to the standard family. -/
theorem isLeviCuspidal_bernsteinLiteralLeviRep_of_inertia
    (J : Finset (SimpleRoot i ν))
    {A B : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J))}
    (hAB : IsRationalInertiaRelated (bernsteinLeviScheme i ν J) A B)
    (hA : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent J (family.closedLevi J) (family.leviDecomposition J)
      (bernsteinLiteralLeviRep i ν J A)) :
    Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent J (family.closedLevi J) (family.leviDecomposition J)
      (bernsteinLiteralLeviRep i ν J B) := by
  let := (family.closedLevi J).locallyCompactSpace
  obtain ⟨χ, ⟨e⟩⟩ := hAB
  let ψ : Induction.SmoothCharacter ℂ (levi i ν J) :=
    ⟨χ.val.toMonoidHom.comp (leviRationalPointHomeomorph i ν J).symm.toMonoidHom,
      (isOpen_rationalUnramifiedCharacter_ker (bernsteinLeviScheme i ν J) χ).preimage
        (leviRationalPointHomeomorph i ν J).symm.continuous⟩
  have et : bernsteinLiteralLeviRep i ν J (rationalUnramifiedTwist
      (bernsteinLeviScheme i ν J) χ A) ≅
      (bernsteinLiteralLeviRep i ν J A).twist ψ.toMonoidHom ψ.isOpen_ker :=
    SmoothRep.mkIso (equivOfRepresentationEq (by rfl))
  have eB : bernsteinLiteralLeviRep i ν J B ≅
      (bernsteinLiteralLeviRep i ν J A).twist ψ.toMonoidHom ψ.isOpen_ker :=
    ((SmoothRep.pullbackFunctor (leviRationalPointHomeomorph i ν J).symm).mapIso e) ≪≫ et
  intro I
  let t := (SmoothRep.equivOfIso ((jacquetFunctor (family.leviDecomposition J I.val)
    ((family.closedUnipotent (leviIndex J I.val)).preimage continuous_subtype_val)).mapIso eB)).toLinearEquiv
  let q := normalizedJacquetCharacterTwistEquiv
    ((unipotent i ν (leviIndex J I.val)).subgroupOf (levi i ν J))
    ((levi i ν (leviIndex J I.val)).subgroupOf (levi i ν J))
    ((family.closedUnipotent (leviIndex J I.val)).preimage continuous_subtype_val)
    (family.leviDecomposition J I.val).levi_le_normalizer ψ
    (bernsteinLeviUnramifiedCharacter_radical i ν family J χ I.val)
    (bernsteinLiteralLeviRep i ν J A)
  have hq : Subsingleton ((jacquetFunctor (family.leviDecomposition J I.val)
      ((family.closedUnipotent (leviIndex J I.val)).preimage continuous_subtype_val)).obj
      ((bernsteinLiteralLeviRep i ν J A).twist ψ.toMonoidHom ψ.isOpen_ker)) :=
    q.toEquiv.subsingleton_congr.mpr (hA I)
  let := hq
  exact t.injective.subsingleton

/-- Replace the representation of a datum by an inertia-related irreducible
on the same actual Levi. -/
def BernsteinCuspidalDatum.replaceInertia
    (b : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (D : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν b.roots)))
    (hD : D.IsIrreducible)
    (hbD : IsRationalInertiaRelated (bernsteinLeviScheme i ν b.roots) b.representation D) :
    BernsteinCuspidalDatum.{uF, uV} i ν family where
  roots := b.roots
  representation := D
  irreducible := hD
  cuspidal := isLeviCuspidal_bernsteinLiteralLeviRep_of_inertia i ν family b.roots hbD b.cuspidal

/-- The replacement stays in the same genuine Bernstein inertial class. -/
theorem BernsteinCuspidalDatum.inertia_replaceInertia
    (b : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (D : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν b.roots)))
    (hD : D.IsIrreducible)
    (hbD : IsRationalInertiaRelated (bernsteinLeviScheme i ν b.roots) b.representation D) :
    IsBernsteinInertiaRelated i ν family b (b.replaceInertia i ν family D hD hbD) :=
  ⟨RationalLeviConjugacy.refl _, hbD.trans
    (IsRationalInertiaRelated.of_iso (rationalIsoPullbackReflIso D).symm)⟩

/-- The exact condition (iii) in the published characterization target. -/
def BernsteinJacquetExclusion
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) : Prop :=
  ∀ b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
    ¬ IsBernsteinInertiaRelated i ν family a b →
      ¬ SmoothRep.IsSubquotient (bernsteinLiteralLeviRep i ν b.roots b.representation)
        ((normalizedJacquetFunctor (unipotent i ν b.roots) (levi i ν b.roots)
          (family.closedUnipotent b.roots)
          (family.decomposition b.roots).levi_le_normalizer).obj V)

/-- Testing every prohibited cuspidal datum excludes its entire inertia orbit
from the actual scheme-side Jacquet module. -/
theorem bernsteinJacquetExclusion_iff_inertiaComplement
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :
    BernsteinJacquetExclusion i ν family a V ↔
      ∀ b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
        ¬ IsBernsteinInertiaRelated i ν family a b →
          rationalInertiaComplementProperty (bernsteinLeviScheme i ν b.roots)
            b.representation (bernsteinSchemeJacquet i ν family b.roots V) := by
  constructor
  · intro h b hab D hD hDJ hbD
    let c := b.replaceInertia i ν family D hD hbD
    have hbc : IsBernsteinInertiaRelated i ν family b c :=
      b.inertia_replaceInertia i ν family D hD hbD
    exact h c (fun hac => hab (hac.trans hbc.symm))
      ((isSubquotient_bernsteinSchemeJacquet_iff i ν family b.roots D V).mp hDJ)
  · intro h b hab hbV
    exact h b hab b.representation b.irreducible
      ((isSubquotient_bernsteinSchemeJacquet_iff i ν family b.roots b.representation V).mpr hbV)
      (IsRationalInertiaRelated.refl _)

end Langlands.CuspidalSupport
