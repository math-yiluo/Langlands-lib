/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.OpenComparisonIntoPullbackTransport

/-! # Source-open conjugacy of the canonical stalk comparison

Source: Stacks Project, Tag 0DJ8, locality of equation-bc on X'; Tag 0DJ9,
source-open induction.
(blueprint: lem-pc-single-complex-open-stalk-conjugacy).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

set_option backward.isDefEq.respectTransparency.types false in
private theorem open_stalkComparison_normalized
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c : Coordinates g' K K' φ) (z : X') (i : ℤ) :
    stalkComparison f f' g g' sq c z i ≫
        ((comparisonStalkHomologyIso X' z c.N i).inv ≫
          (comparisonStalkCohomology X' z i).map c.e'.hom) =
      comparisonIntoPullback f f' g g' sq z c.P c.counit_isIso i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map c.e.hom ≫ φ) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  have := c.counit_isIso
  have ht := comparisonStalkHomologyIso_naturality X' z c.t i
  have ht' : HomologicalComplex.homologyMap
      (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).map c.t) i ≫ (comparisonStalkHomologyIso X' z c.N i).inv =
      (comparisonStalkHomologyIso X' z
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).inv ≫
          (comparisonStalkCohomology X' z i).map (DerivedCategory.Q.map c.t) := by
    apply (cancel_epi (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).hom).mp
    rw [← Category.assoc, ← ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht'' := congrArg (fun a => a ≫ (comparisonStalkCohomology X' z i).map c.e'.hom) ht'
  simp only [Category.assoc] at ht''
  let H := comparisonStalkCohomology X' z i
  have hrep : H.map (inv ((counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P))) ≫
      H.map ((derivedPullback g').map c.e.hom ≫ φ) =
      H.map (DerivedCategory.Q.map c.t) ≫ H.map c.e'.hom := by
    rw [← H.map_comp, ← c.represents]
    simp only [cast_eq, IsIso.inv_hom_id_assoc, H.map_comp]
  simp only [stalkComparison, comparisonIntoPullback, cast_eq, Category.assoc]
  rw [hrep, ht'']

set_option backward.isDefEq.respectTransparency.types false in
/-- The original and source-open comparisons are isomorphic as additive arrows.
No invertibility of either comparison is assumed.

Proof: write j = U.ι, p = pullback.fst g' j, q = pullback.snd g' j.
The base change p of j is an open immersion. Restrict c.P and c.N termwise along
j and p. Exact restriction preserves K-flatness, and its derived functor is
canonically derived pullback on an open immersion. The underived pullback
composition isomorphisms give a chain map from q* of the restricted source to
the restricted target. The defining universal-counit equation for the derived
composition comparisons gives its represents equation for the displayed phiU.
This produces coordinates r for phiU with the restricted representatives.

At z, the isomorphisms j.stalkMap (q z) and p.stalkMap z identify the original
rings A and C with the restricted rings. The commutative square identifies the
base rings R and B; the stalkMap_comp equations identify their algebra actions.
The restriction-stalk extension isomorphisms identify the complexes degreewise.
Thus derived tensor over R with B gives an isomorphism of the model cohomology
objects, compatible with the A-tensor-R-B action (multiplication is natural).
After extension to C this gives the source vertical isomorphism. Exact stalks
and cohomology give the target vertical isomorphism. The comparison_eq and
localized_eq equations of the cohomology models identify their horizontal maps
with the universal derived tensor counits and their scalar-extension transposes.
Naturality of these counits, of tensorStalkIso, and of the restricted chain map
therefore gives a commuting square for c and r.

For arbitrary d, its e and e' compared with those of r give derived isomorphisms
of the representatives. Apply the same source transport and pullback naturality
used in coordinate invariance: after normalizing the targets by e', both maps
are induced by phiU because of represents. These give another commuting square
with invertible vertical maps for r and d. Compose the squares and forget the
module scalars. Arrow.isoMk packages the two additive isomorphisms and the
commutativity equation. This uses no flatness over R and does not assert that
the localized comparison itself is invertible. For an empty open there is no z;
for the top open the same ring isomorphisms apply. Zero complexes and zero rings
are also allowed, since every transport is through a ring or derived isomorphism.
Source: Stacks Project, perfect.tex, Tag 0DJ8, proof of locality of condition (1);
Tag 0DJ9, the comparison for U and its inverse image.
(blueprint: lem-pc-single-complex-open-stalk-conjugacy). -/
theorem nonempty_stalkComparison_open_arrow_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (c : Coordinates g' K K' φ)
    (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g) :
    let φU :=
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))))
        (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))))
        (pullback.fst g' U.ι) g').inv.app K ≫
      (derivedPullback (pullback.fst g' U.ι)).map φ
    ∀ (d : Coordinates (pullback.snd g' U.ι) ((derivedPullback U.ι).obj K)
        ((derivedPullback (pullback.fst g' U.ι)).obj K') φU)
      (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ),
      Nonempty
        (Arrow.mk ((forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
            AddCommGrpCat.{u}).map
              (stalkComparison f f' g g' sq c (pullback.fst g' U.ι z) i)) ≅
          Arrow.mk ((forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
            AddCommGrpCat.{u}).map
              (stalkComparison (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
                g (pullback.snd g' U.ι) sqU d z i))) := by
  intro φU d z i
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
    AddCommGrpCat.{u}
  let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
    AddCommGrpCat.{u}
  let H := comparisonStalkCohomology X' (pullback.fst g' U.ι z) i
  let HU := comparisonStalkCohomology (pullback g' U.ι) z i
  obtain ⟨η, hη⟩ := exists_open_comparisonIntoPullback_transport f f' g g' sq U sqU z i
  obtain ⟨l, hl⟩ := hη K c.P d.P c.isKFlat d.isKFlat
    c.counit_isIso d.counit_isIso c.e d.e
  let a := F.map (comparisonIntoPullback f f' g g' sq
    (pullback.fst g' U.ι z) c.P c.counit_isIso i)
  let b := FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sqU z d.P d.counit_isIso i)
  let β :=
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.snd g' U.ι) U.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := U.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' U.ι) g').inv.app K
  change a ≫ (H ⋙ F).map ((derivedPullback g').map c.e.hom) ≫
      η.hom.app ((derivedPullback g').obj K) =
    l.hom ≫ b ≫ (HU ⋙ FU).map
      ((derivedPullback (pullback.snd g' U.ι)).map d.e.hom ≫ β) at hl
  let cTarget := F.mapIso
    ((comparisonStalkHomologyIso X' (pullback.fst g' U.ι z) c.N i).symm ≪≫
      H.mapIso c.e')
  let dTarget := FU.mapIso
    ((comparisonStalkHomologyIso (pullback g' U.ι) z d.N i).symm ≪≫ HU.mapIso d.e')
  have hc : F.map (stalkComparison f f' g g' sq c (pullback.fst g' U.ι z) i) ≫
      cTarget.hom = a ≫ (H ⋙ F).map ((derivedPullback g').map c.e.hom ≫ φ) := by
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map (open_stalkComparison_normalized
        f f' g g' sq c (pullback.fst g' U.ι z) i)).trans (F.map_comp _ _))
  have hd : FU.map (stalkComparison (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sqU d z i) ≫ dTarget.hom =
      b ≫ (HU ⋙ FU).map ((derivedPullback (pullback.snd g' U.ι)).map d.e.hom ≫ φU) := by
    exact (FU.map_comp _ _).symm.trans
      ((congrArg FU.map (open_stalkComparison_normalized (U.ι ≫ f)
        (pullback.fst g' U.ι ≫ f') g (pullback.snd g' U.ι) sqU d z i)).trans
          (FU.map_comp _ _))
  have hs : F.map (stalkComparison f f' g g' sq c (pullback.fst g' U.ι z) i) ≫
      cTarget.hom ≫ η.hom.app K' =
      l.hom ≫ FU.map (stalkComparison (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sqU d z i) ≫ dTarget.hom := by
    calc
      _ = (a ≫ (H ⋙ F).map ((derivedPullback g').map c.e.hom ≫ φ)) ≫
          η.hom.app K' := by
        simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ η.hom.app K') hc
      _ = (a ≫ (H ⋙ F).map ((derivedPullback g').map c.e.hom) ≫
          η.hom.app ((derivedPullback g').obj K)) ≫
          (HU ⋙ FU).map ((derivedPullback (pullback.fst g' U.ι)).map φ) := by
        simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using
          congrArg (fun k ↦ a ≫ (H ⋙ F).map ((derivedPullback g').map c.e.hom) ≫ k)
            (η.hom.naturality φ)
      _ = (l.hom ≫ b ≫ (HU ⋙ FU).map
          ((derivedPullback (pullback.snd g' U.ι)).map d.e.hom ≫ β)) ≫
          (HU ⋙ FU).map ((derivedPullback (pullback.fst g' U.ι)).map φ) := by
        exact congrArg (fun k ↦ k ≫
          (HU ⋙ FU).map ((derivedPullback (pullback.fst g' U.ι)).map φ)) hl
      _ = _ := by
        simpa only [φU, β, Functor.map_comp, Category.assoc] using
          congrArg (fun k ↦ l.hom ≫ k) hd.symm
  refine ⟨Arrow.isoMk l (cTarget ≪≫ η.app K' ≪≫ dTarget.symm) ?_⟩
  change l.hom ≫ FU.map (stalkComparison (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sqU d z i) =
    F.map (stalkComparison f f' g g' sq c (pullback.fst g' U.ι z) i) ≫
      (cTarget.hom ≫ η.hom.app K' ≫ dTarget.inv)
  apply (cancel_mono dTarget.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hs.symm

end AlgebraicGeometry.SingleComplexBaseChange
