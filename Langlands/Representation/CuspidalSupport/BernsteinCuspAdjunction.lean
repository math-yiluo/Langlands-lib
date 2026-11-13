import Langlands.Representation.Aubert.General.InductionLimits
import Langlands.Representation.CuspidalSupport.BernsteinCuspAdjunctionStatement
import Langlands.Representation.Aubert.General.FirstAdjointnessConsequences
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-! # The adjunction in Renard VI.7.2, second Lemma -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.CuspidalSupport

universe uI uC vC uD vD

section FiniteProduct

variable {ι : Type uI} {C : Type uC} [Category.{vC} C]
  {D : ι → Type uD} [∀ j, Category.{vD} (D j)]
  (L : ∀ j, C ⥤ D j) (K : ∀ j, D j ⥤ C)

/-- Assemble adjunctions with a common source using a product in that source. -/
def piLimitAdjunction [HasLimitsOfShape (Discrete ι) C]
    (adj : ∀ j, L j ⊣ K j) :
    Functor.pi' L ⊣ Functor.pi K ⋙ (piEquivalenceFunctorDiscrete ι C).functor ⋙ lim :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => limit.lift ((piEquivalenceFunctorDiscrete ι C).functor.obj ((Functor.pi K).obj Y)) {
        pt := X
        π := Discrete.natTrans (fun j => (adj j.as).homEquiv X (Y j.as) (f j.as)) }
      invFun := fun g j => ((adj j).homEquiv X (Y j)).symm
        (g ≫ limit.π ((piEquivalenceFunctorDiscrete ι C).functor.obj ((Functor.pi K).obj Y)) ⟨j⟩)
      left_inv := by
        intro f
        change (∀ j, (L j).obj X ⟶ Y j) at f
        funext j
        dsimp
        erw [limit.lift_π]
        exact (adj j).homEquiv X (Y j) |>.symm_apply_apply _
      right_inv := by
        intro g
        apply limit.hom_ext
        rintro ⟨j⟩
        simp
        rfl }
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      funext j
      dsimp
      rw [Category.assoc, (adj j).homEquiv_naturality_left_symm]
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      dsimp
      apply limit.hom_ext
      rintro ⟨j⟩
      simp only [Category.assoc, limMap_π, limit.lift_π, limit.lift_π_assoc,
        Discrete.natTrans_app]
      exact (adj j).homEquiv_naturality_right (f j) (g j) }

/-- In a category with biproducts, the product right adjoint is also the coproduct
right adjoint. This includes an empty finite indexing type. -/
def piCoproductAdjunction [HasZeroMorphisms C] [HasBiproductsOfShape ι C]
    (adj : ∀ j, L j ⊣ K j) :
    Functor.pi' L ⊣ Functor.pi K ⋙ (piEquivalenceFunctorDiscrete ι C).functor ⋙ colim :=
  (piLimitAdjunction L K adj).ofNatIsoRight
    (Functor.isoWhiskerLeft (Functor.pi K ⋙ (piEquivalenceFunctorDiscrete ι C).functor)
      HasBiproductsOfShape.colimIsoLim.symm)

end FiniteProduct

universe uG uV

section Smooth

open Langlands.Aubert.General

variable {H : Type uG} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]

/-- First adjointness as a native categorical adjunction, at the saturated
carrier universe used by normalized induction. -/
def normalizedJacquetInductionAdjunction {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (hδ : IsUnimodularModulus U hU) :
    jacquetFunctor.{uG, max uG uV} h hU ⊣
      normalizedInductionFunctor.{uG, max uG uV} h hU :=
  firstAdjointnessAdjunction h hU hδ

omit [LocallyCompactSpace H] [NonarchimedeanGroup H] in
/-- Every unit of a faithful left adjoint on smooth representations is injective.
This needs no exactness assumption. -/
theorem injective_adjunction_unit {E : Type uD} [Category.{vD} E]
    {L : SmoothRep.{0, uG, uV} ℂ H ⥤ E}
    {K : E ⥤ SmoothRep.{0, uG, uV} ℂ H} [L.Faithful]
    (adj : L ⊣ K) (V : SmoothRep.{0, uG, uV} ℂ H) :
    Function.Injective (SmoothRep.hom (adj.unit.app V)) :=
  (SmoothRep.mono_iff_injective _).mp inferInstance

end Smooth

universe uF

open _root_.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

section StandardFamily

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

local instance bernsteinAdjunctionPointTopology :
    TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The literal Levi cuspidal subcategory used in the target statement. -/
abbrev bernsteinLeviCuspidalProperty (J : Finset (SimpleRoot i ν)) :
    ObjectProperty (SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) := fun W =>
  Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
    family.closedUnipotent J (family.closedLevi J) (family.leviDecomposition J) W

include family in
omit [LocallyOfFiniteType G.X.hom] in
/-- Clause (i) of the second Lemma, for every supplied choice of cuspidal left
adjoints. No whole-category cuspidal decomposition is assumed. -/
theorem bernsteinCuspAdjunction_of_reflectors
    (sc : ∀ J : Finset (SimpleRoot i ν),
      SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) ⥤
        (bernsteinLeviCuspidalProperty.{uV, uF} i ν family J).FullSubcategory)
    (hsc : ∀ J, Nonempty (sc J ⊣ (bernsteinLeviCuspidalProperty i ν family J).ι)) :
    have : Finite (SimpleRoot i ν) := family.finiteSimpleRoots
    let cusp : ∀ J : Finset (SimpleRoot i ν),
        ObjectProperty (SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) := fun J W =>
      Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
        family.closedUnipotent J (family.closedLevi J) (family.leviDecomposition J) W
    Nonempty ((Functor.pi' fun J =>
      normalizedJacquetFunctor (unipotent i ν J) (levi i ν J)
        (family.closedUnipotent J) (family.decomposition J).levi_le_normalizer ⋙ sc J) ⊣
      Functor.pi (fun J => (cusp J).ι ⋙
          normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)) ⋙
        (piEquivalenceFunctorDiscrete (Finset (SimpleRoot i ν))
          (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))).functor ⋙ colim) := by
  classical
  have : Finite (SimpleRoot i ν) := family.finiteSimpleRoots
  have : HasFiniteBiproducts
      (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) := Abelian.hasFiniteBiproducts
  exact ⟨piCoproductAdjunction _ _ (fun J =>
    (normalizedJacquetInductionAdjunction (family.decomposition J) (family.closedUnipotent J)
      (standardUnipotent_isUnimodular_of_standardCocharacterStatement
        i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
        family.genericCocharacter J (family.closedUnipotent J))).comp (hsc J).some)⟩

end StandardFamily

end Langlands.CuspidalSupport
