/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
import WeilConjectures.AlgebraicGeometry.OpenRestrictedCanonicalSquare
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction

/-! # Comparison square on literal restrictions

Source: Stacks Project, Tags 0DJ8 and 0DJ9 (locality of the stalk comparison).
(blueprint: lem-pc-open-restricted-comparison-core).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
private theorem openRestrictedCompositionMap_naturality
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    {K L : schemeDerivedCategory X} (a : K ⟶ L) :
    (derivedPullback (pullback.snd g' U.ι)).map ((derivedPullback U.ι).map a) ≫
      openRestrictedCompositionMap g' U L =
    openRestrictedCompositionMap g' U K ≫
      (derivedPullback (pullback.fst g' U.ι)).map ((derivedPullback g').map a) := by
  let e := eqToIso (congrArg (fun k ↦ derivedPullback k)
    (pullback.condition (f := g') (g := U.ι)).symm)
  let t := (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))))
      (pullback.snd g' U.ι) U.ι ≪≫ e ≪≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))))
      (pullback.fst g' U.ι) g').symm
  simpa only [t, e, openRestrictedCompositionMap, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Functor.comp_map, Category.assoc] using t.hom.naturality a

private theorem compose_comparison_square
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {R Q T V : C} {A B : D}
    (bR : A ⟶ H.obj R) (bQ : B ⟶ H.obj Q) (n : A ⟶ B)
    (d : R ⟶ Q) (r : R ⟶ T) (s : Q ⟶ T) (β : T ⟶ V)
    (hd : d ≫ s = r) (hn : bR ≫ H.map d = n ≫ bQ) :
    bR ≫ H.map (r ≫ β) = n ≫ bQ ≫ H.map (s ≫ β) := by
  rw [← hd, Category.assoc, H.map_comp, ← Category.assoc, hn, Category.assoc]

private theorem additive_comparisonIntoPullback_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (d : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let H := comparisonStalkCohomology X' z i ⋙ F
    let a := F.map (comparisonIntoPullback f f' g g' sq z P hcP i)
    let b := F.map (comparisonIntoPullback f f' g g' sq z Q hcQ i)
    ∃ n : (Arrow.mk a).left ≅ (Arrow.mk b).left,
      a ≫ H.map ((derivedPullback g').map d.hom) = n.hom ≫ b := by
  classical
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  obtain ⟨e, he, _⟩ := exists_comparisonSourceIso f f' g g' sq z P Q d i
  have hn := comparisonIntoPullback_naturality f f' g g' sq z P Q
    hP hQ hcP hcQ d i e he
  let E := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (TensorProduct (R f g' z) (A g' z) (B f' z)) (C z))
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
  refine ⟨F.mapIso (E.mapIso e), ?_⟩
  simpa only [Functor.map_comp, Functor.comp_map, Functor.mapIso_hom] using
    congrArg F.map hn


set_option linter.unusedVariables false in
/-- The open comparison square when the restricted representative data are supplied.
Source: Stacks Project, Tag 0DJ8 (locality of equation-bc), Tag 0DJ9
(source-open induction), and Tag 06YB (K-flat stalks).
(blueprint: lem-pc-open-restricted-comparison-core).

Proof: put p = pullback.fst g′ U.ι and q = pullback.snd g′ U.ι. The open
immersion p has exact module restriction. Uniqueness of left adjoints identifies
its tensor pullback with restriction, and uniqueness of left derived functors
identifies their derived functors. Descend restrictStalkNatIso to the exact
derived functors and then cohomology, obtaining η independently of P and K.
Open restriction preserves K-flatness of P by the stalk criterion.
The stalk ring maps of p and U.ι are isomorphisms. The pullback condition,
stalkMap_comp, and restriction-stalk extension identify the original and
restricted stalk complexes with their base-ring actions. Apply the universal
derived base tensor functor, cohomology, and final scalar extension to obtain
the source isomorphism. The comparison_eq and localized_eq model equations
identify both comparisons with universal counits and adjunction transposes.
Naturality of these maps and tensorStalkIso proves the square for the canonical
exact-restriction identification. The derived-composition counit equation gives
precisely β. For the supplied eQ, compare it with the canonical identification
through a derived automorphism of the literal restricted representative. Apply
comparisonIntoPullback_naturality and exists_comparisonSourceIso to that
automorphism; compose its source isomorphism with the preceding one. Naturality
of η transports the square along eP. This gives the displayed formula for every
supplied eQ and hcQ. Invertibility of comparisonIntoPullback is never assumed.
Empty opens have no z, and the same operations apply to zero complexes and rings. -/
theorem exists_open_restricted_comparison_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
      AddCommGrpCat.{u}
    let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
      AddCommGrpCat.{u}
    let H := comparisonStalkCohomology X' (pullback.fst g' U.ι z) i ⋙ F
    let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
    ∃ η : H ≅ derivedPullback (pullback.fst g' U.ι) ⋙ HU,
      ∀ (K : schemeDerivedCategory X)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
        (eP : DerivedCategory.Q.obj P ≅ K),
      let Q : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
        ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
      ∀ (hcQ : IsIso ((counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
        (eQ : DerivedCategory.Q.obj Q ≅ (derivedPullback U.ι).obj K),
      let a := F.map (comparisonIntoPullback f f' g g' sq
        (pullback.fst g' U.ι z) P hcP i)
      let b := FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sqU z Q hcQ i)
      let β := openRestrictedCompositionMap g' U K
      ∃ l : (Arrow.mk a).left ≅ (Arrow.mk b).left,
        a ≫ H.map ((derivedPullback g').map eP.hom) ≫
            η.hom.app ((derivedPullback g').obj K) =
          l.hom ≫ b ≫ HU.map ((derivedPullback (pullback.snd g' U.ι)).map eQ.hom ≫ β) := by
  intro F FU H HU
  let η := openDerivedStalkIso (pullback.fst g' U.ι) z i
  refine ⟨η, ?_⟩
  intro K P hP hcP eP Q hcQ eQ a b β
  let q := pullback.snd g' U.ι
  let p := pullback.fst g' U.ι
  let eR := openRestrictionRepresentativeIso U.ι P
  let β₀ := openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P)
  obtain ⟨l, hl⟩ := exists_open_restricted_canonical_square
    f f' g g' sq U sqU z i P hP hcP hcQ
  change a ≫ η.hom.app ((derivedPullback g').obj (DerivedCategory.Q.obj P)) =
    l.hom ≫ b ≫ HU.map ((derivedPullback q).map eR.hom ≫ β₀) at hl
  have hn := η.hom.naturality ((derivedPullback g').map eP.hom)
  change H.map ((derivedPullback g').map eP.hom) ≫
      η.hom.app ((derivedPullback g').obj K) =
    η.hom.app ((derivedPullback g').obj (DerivedCategory.Q.obj P)) ≫
      HU.map ((derivedPullback p).map ((derivedPullback g').map eP.hom)) at hn
  have hb := openRestrictedCompositionMap_naturality g' U eP.hom
  have he : (derivedPullback q).map eR.hom ≫ β₀ ≫
      (derivedPullback p).map ((derivedPullback g').map eP.hom) =
      (derivedPullback q).map (eR.hom ≫ (derivedPullback U.ι).map eP.hom) ≫ β := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun m ↦ (derivedPullback q).map eR.hom ≫ m) hb.symm
  have ht : a ≫ H.map ((derivedPullback g').map eP.hom) ≫
      η.hom.app ((derivedPullback g').obj K) =
      l.hom ≫ b ≫
        HU.map ((derivedPullback q).map
          (eR.hom ≫ (derivedPullback U.ι).map eP.hom) ≫ β) := by
    rw [hn]
    rw [← Category.assoc, hl]
    simp only [Category.assoc, ← HU.map_comp]
    rw [he]
  have hQ : Q.IsKFlatTensor := isKFlat_restrict U.ι P hP
  let d : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj Q :=
    eR ≪≫ (derivedPullback U.ι).mapIso eP ≪≫ eQ.symm
  obtain ⟨n, hnat⟩ := additive_comparisonIntoPullback_naturality
    (U.ι ≫ f) (p ≫ f') g q sqU z Q Q hQ hQ hcQ hcQ d i
  change b ≫ HU.map ((derivedPullback q).map d.hom) = n.hom ≫ b at hnat
  have hd : (derivedPullback q).map d.hom ≫ (derivedPullback q).map eQ.hom =
      (derivedPullback q).map (eR.hom ≫ (derivedPullback U.ι).map eP.hom) := by
    rw [← Functor.map_comp]
    simp only [d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hs := compose_comparison_square HU b b n.hom
    ((derivedPullback q).map d.hom)
    ((derivedPullback q).map (eR.hom ≫ (derivedPullback U.ι).map eP.hom))
    ((derivedPullback q).map eQ.hom) β hd hnat
  refine ⟨l ≪≫ n, ?_⟩
  exact ht.trans (by
    simpa only [Iso.trans_hom, Category.assoc] using
      congrArg (fun m ↦ l.hom ≫ m) hs)

end AlgebraicGeometry.SingleComplexBaseChange
