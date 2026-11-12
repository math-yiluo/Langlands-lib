import Langlands.Representation.Category.IntertwinerSubspaces
import Langlands.Representation.CuspidalSupport.BernsteinCoproductRegrouping

/-! # Descending actual Bernstein components to the original carrier -/

noncomputable section

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

local instance bernsteinCarrierDescentTopology :
    TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- A cross-universe injection into a saturated block object gives the
original block property on the source, through actual lifted constituents. -/
theorem bernsteinBlockProperty_of_injectiveIntertwiner
    {V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)}
    {W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    {c : BernsteinInertialClass.{uF, max uF uV} i ν family}
    (hW : bernsteinSaturatedBlockProperty i ν family c W)
    (f : V.representation.IntertwiningMap W.representation)
    (hf : Function.Injective f) :
    bernsteinBlockProperty i ν family c V := by
  intro D hD hDV
  exact hW (SmoothRep.universeLift.{uF} D)
    ((SmoothRep.isIrreducible_universeLift_iff D).mpr hD)
    (hDV.universeLift_of_injectiveIntertwiner f hf)

/-- A spanning invariant family in the larger carrier whose members lie in
their actual blocks descends to an original-carrier Bernstein coproduct. -/
def bernsteinDescendedCofanIsColimit
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    {V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)}
    {W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (e : V.representation.Equiv W.representation)
    (S : BernsteinInertialClass.{uF, max uF uV} i ν family →
      Subrepresentation W.representation)
    (hspan : (⨆ c, S c) = ⊤)
    (hS : ∀ c, bernsteinSaturatedBlockProperty i ν family c
      (SmoothRep.subrepresentation W (S c))) :
    IsColimit (SmoothRep.invariantSubspaceCofan
      (fun c => SmoothRep.intertwinerPreimage e.toIntertwiningMap (S c))) := by
  have hsmall (c) : bernsteinBlockProperty i ν family c
      (SmoothRep.subrepresentation V
        (SmoothRep.intertwinerPreimage e.toIntertwiningMap (S c))) :=
    bernsteinBlockProperty_of_injectiveIntertwiner i ν family (hS c)
      (SmoothRep.intertwinerPreimageMap e.toIntertwiningMap (S c))
      (SmoothRep.intertwinerPreimageMap_injective _ _ e.injective)
  apply SmoothRep.invariantSubspaceCofanIsColimit _
    (SmoothRep.iSup_intertwinerPreimage_eq_top_of_equiv e S hspan)
  intro c d hcd D hD hDc hDd
  exact hcd (hunique _ c d (hsmall c D hD hDc) (hsmall d D hD hDd))

/-- A supplied actual Bernstein decomposition descends through an actual
representation equivalence to an object in the original carrier universe. -/
theorem isBernsteinCoproductOfComponents_of_equiv
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    {V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)}
    {W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (e : V.representation.Equiv W.representation)
    (hW : Renard.IsCoproductOfComponents
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, max uF uV} i ν family c) W) :
    Renard.IsCoproductOfComponents
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family c) V := by
  obtain ⟨A, legs, hA, ⟨hs⟩⟩ := hW
  let s := Cofan.mk W legs
  let S := fun c => (SmoothRep.hom (s.inj c)).range
  have hS (c) : bernsteinSaturatedBlockProperty i ν family c
      (SmoothRep.subrepresentation W (S c)) :=
    (bernsteinBlockProperty_iff_saturated _ _).mp
      (bernsteinBlockProperty_of_isSubquotient (hA c)
        (SmoothRep.image_isQuotient (s.inj c)).isSubquotient)
  refine ⟨_, (SmoothRep.invariantSubspaceCofan
    (fun c => SmoothRep.intertwinerPreimage e.toIntertwiningMap (S c))).inj, ?_,
    ⟨bernsteinDescendedCofanIsColimit i ν family hunique e S
      (SmoothRep.iSup_range_cofan_eq_top A s hs) hS⟩⟩
  intro c
  exact bernsteinBlockProperty_of_injectiveIntertwiner i ν family (hS c)
    (SmoothRep.intertwinerPreimageMap e.toIntertwiningMap (S c))
    (SmoothRep.intertwinerPreimageMap_injective _ _ e.injective)

/-- A source embedding in a decomposed larger object inherits an actual
Bernstein decomposition in its own original carrier universe. -/
theorem isBernsteinCoproductOfComponents_of_injectiveIntertwiner
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    {V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)}
    {W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (f : V.representation.IntertwiningMap W.representation)
    (hf : Function.Injective f)
    (hW : Renard.IsCoproductOfComponents
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, max uF uV} i ν family c) W) :
    Renard.IsCoproductOfComponents
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family c) V :=
  isBernsteinCoproductOfComponents_of_equiv i ν family hunique
    (SmoothRep.intertwinerImageEquiv f hf)
    (bernsteinSplitSubrepresentation_of_supportUniqueness.{uF, max uF uV}
      i ν family hunique
      W f.range hW)

end Langlands.CuspidalSupport
