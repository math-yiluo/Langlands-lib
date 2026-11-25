/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
public import WeilConjectures.AlgebraicGeometry.OpenDerivedStalkIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictedOrdinaryComparisonSquare
import all WeilConjectures.AlgebraicGeometry.OpenRestrictedCounitCompatibility

/-! # Comparison square on literal restrictions

Source: Stacks Project, Tags 0DJ8 and 0DJ9 (locality of the stalk comparison).
(blueprint: lem-pc-open-restricted-canonical-square).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
private theorem assemble_open_counit_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    (H : C ⥤ D) (HU : E ⥤ D) (L : C ⥤ E) (η : H ≅ L ⋙ HU)
    {K N : C} {QU NU : E} {A B : D}
    (ε : K ⟶ N) [IsIso ε] (εU : QU ⟶ NU) [IsIso εU]
    (r : QU ⟶ L.obj K) (d : L.obj N ≅ NU)
    (a : A ⟶ H.obj N) (b : B ⟶ HU.obj NU) (l : A ⟶ B)
    (hl : a ≫ η.hom.app N = l ≫ b ≫ HU.map d.inv)
    (hc : r ≫ L.map ε = εU ≫ d.inv) :
    a ≫ H.map (inv ε) ≫ η.hom.app K =
      l ≫ b ≫ HU.map (inv εU) ≫ HU.map r := by
  have hc' : d.inv ≫ L.map (inv ε) = inv εU ≫ r := by
    apply (cancel_epi εU).mp
    rw [← Category.assoc εU d.inv, ← hc]
    simp only [Category.assoc, ← L.map_comp, IsIso.hom_inv_id,
      L.map_id, Category.comp_id, IsIso.hom_inv_id_assoc]
  have hn := η.hom.naturality (inv ε)
  change H.map (inv ε) ≫ η.hom.app K = η.hom.app N ≫ HU.map (L.map (inv ε)) at hn
  rw [hn, ← Category.assoc a, hl]
  simp only [Category.assoc, ← HU.map_comp, hc']

-- The localized tensor and exact restriction factors need extra elaboration heartbeats.
set_option linter.unusedVariables false in
-- Preserve the existing named K-flatness binder, unused in the dependent conclusion.
/-- Compatibility of the two comparison arrows on a literal restriction, using
only the constructed derived-stalk isomorphism and representing isomorphism.
Source: Stacks Project, Tag 0DJ8, locality of equation-bc; Tag 0DJ9,
source-open induction paragraph; Tag 0D5U, exact open restriction.
(blueprint: lem-pc-open-restricted-canonical-square).

Proof: put j = U.ι, p = pullback.fst g′ j and q = pullback.snd g′ j.
Both j and p are open immersions, so their stalk ring maps are isomorphisms.
The pullback condition and stalkMap_comp identify the source and base stalk
ring maps for the two squares. The scalar-compatible restriction-stalk
extension isomorphism identifies the stalk complexes of P and its literal
restriction Q. Transport the universal base-derived tensor functors over
these ring isomorphisms, then apply cohomology and extension to the final
stalk ring. This constructs l, including its inverse, independently of
any invertibility of the comparison arrow. The model equations comparison_eq
and localized_eq express both comparison arrows as universal derived
counits followed by scalar-extension adjunction transposes. Their naturality
under these ring and stalk identifications, and tensorStalkIso, proves their
commutative square. Exact-restriction homology and restriction-stalk naturality
identify its right side with the constructed openDerivedStalkIso. The
universal-counit equation defining the derived composition comparisons
identifies the bottom transport with openRestrictedCompositionMap. The
localization factor of exact restriction is precisely
openRestrictionRepresentativeIso. Thus the equality is the displayed one.
K-flatness of P computes the original derived pullback; exact open restriction
preserves K-flatness. The supplied hcQ computes the restricted derived pullback.
This calculation has no arbitrary represented object or representing isomorphism.
Empty opens have no z. Top opens, zero complexes and zero rings use the same
functorial identifications; there is no nonzero or nonempty assumption. -/
theorem exists_open_restricted_canonical_square
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
    let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
    ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
      ,
      let Q : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
        ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
      ∀ (hcQ : IsIso ((counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))),
      let eQ := openRestrictionRepresentativeIso U.ι P
      let η := openDerivedStalkIso (pullback.fst g' U.ι) z i
      let a := F.map (comparisonIntoPullback f f' g g' sq
        (pullback.fst g' U.ι z) P hcP i)
      let b := FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sqU z Q hcQ i)
      let β := openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P)
      ∃ l : (Arrow.mk a).left ≅ (Arrow.mk b).left,
        a ≫ η.hom.app ((derivedPullback g').obj (DerivedCategory.Q.obj P)) =
          l.hom ≫ b ≫ HU.map ((derivedPullback (pullback.snd g' U.ι)).map eQ.hom ≫ β) := by
  dsimp only
  intro P _hP hcP hcQ
  let := hcP
  let := hcQ
  let p := pullback.fst g' U.ι
  let q := pullback.snd g' U.ι
  let Q := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
  let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (p z))) AddCommGrpCat.{u}
  let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat.{u}
  let H := comparisonStalkCohomology X' (p z) i ⋙ F
  let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
  let η := openDerivedStalkIso p z i
  let ε := (counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let εU := (counit q).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)
  let d := openRestrictedTensorDerivedIso g' U P
  let r := (derivedPullback q).map (openRestrictionRepresentativeIso U.ι P).hom ≫
    openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P)
  obtain ⟨l, hl⟩ := exists_open_restricted_ordinary_comparison_square
    f f' g g' sq U sqU z i P
  refine ⟨l, ?_⟩
  have hc : r ≫ (derivedPullback p).map ε = εU ≫ d.inv := by
    simpa only [r, p, q, Q, ε, εU, d, Category.assoc] using
      openRestricted_counit_compatibility g' U P
  have ht := assemble_open_counit_square H HU (derivedPullback p) η ε εU r d
    (F.map (comparisonIntoTensorPullback f f' g g' sq (p z) P i))
    (FU.map (comparisonIntoTensorPullback (U.ι ≫ f) (p ≫ f') g q sqU z Q i))
    l.hom hl hc
  simp only [comparisonIntoPullback, comparisonIntoTensorPullback, Functor.map_comp,
    Functor.comp_map, Category.assoc, H, HU, F, FU, η, ε, εU, r, p, q, Q] at ht ⊢
  convert ht using 1 <;> rfl

end AlgebraicGeometry.SingleComplexBaseChange
