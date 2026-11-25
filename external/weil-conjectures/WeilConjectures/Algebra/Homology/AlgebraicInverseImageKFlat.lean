/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Homology.RingedSiteKFlatStalkCriterion

/-!
# K-flatness under algebraic inverse image

Source: Stacks Project, Cohomology on Sites, Tags 0DEN and 0DEP.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD w t
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
  (I : AlgebraicInverseImage f.inverse R S) [I.modules.Additive]
  (p : GeometricMorphism (Type w) (Sheaf K (Type w))) (s : RingedSitePoint S p)

private def unliftSheafIso
    {E : Type uC} [Category.{vC} E] (T : GrothendieckTopology E)
    {A : Type uD} [Category.{vD} A] (U : A ⥤ Type w)
    [T.HasSheafCompose U] [T.HasSheafCompose (U ⋙ uliftFunctor.{w, w})] :
    sheafCompose T (U ⋙ uliftFunctor.{w, w}) ≅ sheafCompose T U :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ uliftTrivial (U.obj (M.obj.obj V)))
      (by intros; rfl))) (by intros; rfl)

private noncomputable def unliftInverseImage
    (I : AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} f.inverse R S) :
    AlgebraicInverseImage f.inverse R S := by
  let eR := unliftSheafIso J (CategoryTheory.forget CommRingCat.{w})
  let eS := unliftSheafIso K (CategoryTheory.forget CommRingCat.{w})
  let eM := Functor.isoWhiskerLeft (toSheaf ((sheafCompose J
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) <|
    unliftSheafIso J (CategoryTheory.forget AddCommGrpCat.{w})
  let eN := Functor.isoWhiskerLeft (toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{w} RingCat.{w})).obj S)) <|
    unliftSheafIso K (CategoryTheory.forget AddCommGrpCat.{w})
  let er := f.inverse.mapIso (eR.app R).symm ≪≫ I.ringUnderlying ≪≫ eS.app S
  let em := Functor.isoWhiskerLeft I.modules eN.symm ≪≫ I.moduleUnderlying ≪≫
    Functor.isoWhiskerRight eM f.inverse
  refine {
    ringUnderlying := er
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    modules := I.modules
    moduleUnderlying := em
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_ }
  · intro T a b z h V x
    have hr := I.ringAdd T (a ≫ (eR.app R).inv) (b ≫ (eR.app R).inv)
      (z ≫ (eR.app R).inv) h V x
    simpa [er, eS, unliftSheafIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a b z h V x
    have hr := I.ringMul T (a ≫ (eR.app R).inv) (b ≫ (eR.app R).inv)
      (z ≫ (eR.app R).inv) h V x
    simpa [er, eS, unliftSheafIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app R).inv) h V x
    simpa [er, eS, unliftSheafIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app R).inv) h V x
    simpa [er, eS, unliftSheafIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b z h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).inv) (b ≫ (eM.app M).inv)
      (z ≫ (eM.app M).inv) h V x
    simpa [em, eN, unliftSheafIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).inv) h V x
    simpa [em, eN, unliftSheafIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b z h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app R).inv) (b ≫ (eM.app M).inv)
      (z ≫ (eM.app M).inv) h V x
    simpa [er, em, eS, eN, unliftSheafIso, uliftTrivial, Functor.map_comp] using hr

private noncomputable def compositePoint : RingedSitePoint R (p.comp f) where
  ring := s.ring
  ringUnderlying := p.inverse.mapIso I.ringUnderlying ≪≫ s.ringUnderlying
  ringAdd := by
    intro T a b z hz x
    simpa [GeometricMorphism.comp, Functor.map_comp] using
      s.ringAdd (f.inverse.obj T)
        (f.inverse.map a ≫ I.ringUnderlying.hom)
        (f.inverse.map b ≫ I.ringUnderlying.hom)
        (f.inverse.map z ≫ I.ringUnderlying.hom) (I.ringAdd T a b z hz) x
  ringMul := by
    intro T a b z hz x
    simpa [GeometricMorphism.comp, Functor.map_comp] using
      s.ringMul (f.inverse.obj T)
        (f.inverse.map a ≫ I.ringUnderlying.hom)
        (f.inverse.map b ≫ I.ringUnderlying.hom)
        (f.inverse.map z ≫ I.ringUnderlying.hom) (I.ringMul T a b z hz) x
  ringZero := by
    intro T a ha x
    simpa [GeometricMorphism.comp, Functor.map_comp] using
      s.ringZero (f.inverse.obj T) (f.inverse.map a ≫ I.ringUnderlying.hom)
        (I.ringZero T a ha) x
  ringOne := by
    intro T a ha x
    simpa [GeometricMorphism.comp, Functor.map_comp] using
      s.ringOne (f.inverse.obj T) (f.inverse.map a ≫ I.ringUnderlying.hom)
        (I.ringOne T a ha) x
  modules := I.modules ⋙ s.modules
  moduleUnderlying :=
    (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft I.modules s.moduleUnderlying ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight I.moduleUnderlying p.inverse ≪≫ Functor.associator _ _ _
  moduleAdd := by
    intro M T a b z hz x
    simpa [GeometricMorphism.comp, Functor.map_comp] using
      s.moduleAdd (I.modules.obj M) (f.inverse.obj T)
        (f.inverse.map a ≫ I.moduleUnderlying.inv.app M)
        (f.inverse.map b ≫ I.moduleUnderlying.inv.app M)
        (f.inverse.map z ≫ I.moduleUnderlying.inv.app M) (I.moduleAdd M T a b z hz) x
  moduleZero := by
    intro M T a ha x
    simpa [GeometricMorphism.comp, Functor.map_comp] using
      s.moduleZero (I.modules.obj M) (f.inverse.obj T)
        (f.inverse.map a ≫ I.moduleUnderlying.inv.app M) (I.moduleZero M T a ha) x
  moduleSMul := by
    intro M T a b z hz x
    simpa [GeometricMorphism.comp, Functor.map_comp] using
      s.moduleSMul (I.modules.obj M) (f.inverse.obj T)
        (f.inverse.map a ≫ I.ringUnderlying.hom)
        (f.inverse.map b ≫ I.moduleUnderlying.inv.app M)
        (f.inverse.map z ≫ I.moduleUnderlying.inv.app M) (I.moduleSMul M T a b z hz) x
  modules_additive := inferInstance

private theorem precoverageSite {E : Type uC} [Category.{vC} E] [HasPullbacks E]
    (J : GrothendieckTopology E) : J.toPrecoverage.IsSiteForCoverings := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro X R T hR hT
    exact J.toPretopology.transitive R (fun _ a ha ↦ T a ha) hR
      (fun _ a ha ↦ hT _ a ha)
  · intro ι X U a ha Y b
    refine ⟨fun i ↦ pullback b (a i), fun i ↦ pullback.fst _ _,
      fun i ↦ pullback.snd _ _, fun i ↦ IsPullback.of_hasPullback _ _, ?_⟩
    change Sieve.ofArrows _ _ ∈ J Y
    rw [Sieve.ofArrows_eq_pullback_of_isPullback _
      (fun i ↦ IsPullback.of_hasPullback b (a i))]
    exact J.pullback_stable b ha


private theorem precoverageTopology {E : Type uC} [Category.{vC} E]
    (J : GrothendieckTopology E) : J.toPrecoverage.toGrothendieck = J := by
  apply le_antisymm J.toGrothendieck_toPrecoverage_le
  intro U S hS
  simpa only [Sieve.generate_sieve] using
    J.toPrecoverage.generate_mem_toGrothendieck
      ((J.arrows_mem_toPrecoverage_iff S).2 hS)

/-- Algebraic inverse image preserves K-flat complexes when the target has a specified
conservative family of points. No termwise flatness or boundedness is required.
Source: Stacks Project, Cohomology on Sites, Tags 0DEN and 0DEP
(auxiliary; not a blueprint node).

Proof: for every target point, compose its ring and module presentation with the
algebraic inverse image. The ring is the target stalk ring, the module functor is the
composite, and preservation of all operation graphs follows by applying the two
presentations successively. The forward stalk criterion at the composite point makes
each target stalk K-flat. Apply the reverse stalk criterion to the conservative family.
The construction also covers an empty conservative family and the zero ring. -/
theorem AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) :
    ∀ (f : GeometricMorphism (Sheaf JD (Type w)) (Sheaf JC (Type w)))
    {R : Sheaf JC CommRingCat.{w}} {S : Sheaf JD CommRingCat.{w}}
    (I : AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} f.inverse R S)
    [I.modules.Additive]
    (ι : Type t) (p : ι → GeometricMorphism (Type w) (Sheaf JD (Type w)))
    (_s : ∀ i, RingedSitePoint S (p i))
    (_hp : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse))
    (P : CochainComplex (SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((I.modules.mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [← precoverageTopology JC, ← precoverageTopology JD]
  intro f R S I _ ι p s hp P hP
  let I₀ := unliftInverseImage f I
  have : I₀.modules.Additive := ‹I.modules.Additive›
  apply (CochainComplex.ringedSite_kFlat_stalk_criterion
    JD.toPrecoverage S _).2 ι p s hp
  intro i
  exact (CochainComplex.ringedSite_kFlat_stalk_criterion.{uC, vC, w, 0}
    JC.toPrecoverage R P).1 ((p i).comp f) (compositePoint f I₀ (p i) (s i)) hP

end SheafOfModules
