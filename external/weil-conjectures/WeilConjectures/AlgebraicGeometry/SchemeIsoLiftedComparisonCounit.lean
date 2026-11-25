/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
public import WeilConjectures.AlgebraicGeometry.SchemeIsoRightAdjointNormalized

/-! # Counit compatibility of the lifted unit comparison

Source: Stacks Project, Tag 0ATR, adjunction comparison under an equivalence.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

/-- Rewrite the ambient normalization with a supplied lifted direct-image comparison.
This concerns only one vertical map and its exceptional adjunction, not a square.
Source: Stacks Project, Tag 0ATR, compatibility of the transported counit.
(blueprint: lem-sc-scheme-iso-lifted-comparison-counit)

Proof: The supplied component identity identifies the ambient hom of k at a(K),
after any two postcompositions, with the direct image of the pinned isomorphism
unit followed by the inverse direct-image conjugate. Take these postcompositions
to be the direct image of φ at K and the counit of adjb at K. The result is exactly
the ambient normalization identity hφ at K. Thus their composite equals the
counit of adja. The maps belong to the full quasi-coherent subcategories by their
supplied types and pullback/direct-image preservation. The inclusion is faithful,
so the ambient equation is the equation for the lifted comparison. No existence
or invertibility of a second mate is used. Identity isomorphisms, zero objects
and empty schemes obey the same equation and require no additional hypotheses. -/
theorem schemeIso_liftedComparison_counit
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f')
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory P)
    (b : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory U)
    (adja : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty P).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjb : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty U).ι ⋙ schemeDerivedDirectImage f')
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f') _ _ _ _ f' _ _).fst E.obj E.property) ⊣ b)
    (φ : (a ⋙ (schemeDerivedQCohProperty P).ι) ⋙ derivedPullback e.hom ≅
      b ⋙ (schemeDerivedQCohProperty U).ι) :
    let adj := fun {X Y : Scheme.{u}} (k : X ⟶ Y) ↦
      Classical.choose (exists_schemeDerivedAdjunction k
        (hAdd := (Classical.choose exists_derivedPullbackComposition) k)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) k))
    let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let c := comp e.hom f ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) he)
    let δ := conjugateIsoEquiv (adj f')
      ((adj f).comp (adj e.hom)) c
    ∀ (k : qcDirectImage f ⟶ qcPullback e.hom ⋙ qcDirectImage f'),
      (∀ (E : schemeDerivedQCohCategory P) (A B : schemeDerivedCategory S)
          (t : ((qcPullback e.hom ⋙ qcDirectImage f').obj E).obj ⟶ A) (v : A ⟶ B),
        (k.app E).hom ≫ t ≫ v =
          (schemeDerivedDirectImage f).map ((adj e.hom).unit.app E.obj) ≫
            δ.inv.app ((derivedPullback e.hom).obj E.obj) ≫ t ≫ v) →
      SchemeIsoRightAdjointNormalized f f' e he a b adja adjb φ →
      ∀ K : schemeDerivedQCohCategory S,
        (k.app (a.obj K)).hom ≫ (schemeDerivedDirectImage f').map (φ.hom.app K) ≫
          (adjb.counit.app K).hom = (adja.counit.app K).hom := by
  intro adj comp c δ k hk hφ K
  have hh := hk (a.obj K) ((schemeDerivedDirectImage f').obj (b.obj K).obj) K.obj
    ((schemeDerivedDirectImage f').map (φ.hom.app K)) (adjb.counit.app K).hom
  exact hh.trans (hφ K)

end
end AlgebraicGeometry
