/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenStalkConjugacy

/-! # Restriction of the single-complex stalk condition to a source open

Source: Stacks Project, Tag 0DJ8, locality on X', and Tag 0DJ9, source-open induction.
(blueprint: lem-pc-single-complex-open-stalk-condition).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restrict the canonical stalk condition and its coefficient map to a source open.
There is no affineness, quasi-coherence, quasi-compactness or boundedness assumption.
Source: Stacks Project, Tag 0DJ8, proof that condition (1) is local on X';
Tag 0DJ9, the similarly constructed comparison on U and its inverse image.
(blueprint: lem-pc-single-complex-open-stalk-condition).

Proof: The projection pullback.fst is the base change of the open immersion U.ι,
hence is itself an open immersion. Take an original coordinate presentation c
using nonempty_coordinates. Restrict c.P and c.N termwise along these two
open immersions. Restriction is exact and preserves K-flatness. Its exact derived
functor agrees with derived pullback, so the restrictions of c.e and c.e' give
the representative isomorphisms. The canonical underived tensor-pullback
composition comparison transports the restriction of c.t to the required chain
map. The universal derived counits and their composition compatibility transport
c.represents to its required localization equation; the counit is invertible on
the restricted K-flat representative. These data construct cU. At a point z of
the pullback, the local rings
of U and of the pullback identify with those of X and X' at their images. The
maps from the base stalk rings are unchanged. Open restriction is exact and
commutes with cohomology; the pullback composition comparisons identify the
restricted coefficient map with the original coefficient map on these stalks.
Using K-flat representatives, the base tensor comparison and its tensor-stalk
identification therefore agree under these ring and complex isomorphisms.
The cohomology map in cU is therefore conjugate, through local-ring scalar
extension equivalences, to the cohomology map in c at the image point. Such
conjugation preserves and reflects invertibility, giving equivalence of invertibility
at each z and degree. The original condition gives invertibility in c, hence in
cU. For any other restricted coordinate presentation d, apply the existing
isIso_stalkComparison_iff_coordinates to cU and d in the restricted square. This
gives the required invertibility for every restricted presentation. The assertion
is vacuous for an empty source open, and the
same construction applies to the top open; neither case requires an extra assumption. -/
theorem singleComplexStalkCondition_open
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ)
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
    SingleComplexBaseChange.StalkCondition (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sqU ((derivedPullback U.ι).obj K)
      ((derivedPullback (pullback.fst g' U.ι)).obj K') φU := by
  let c := Classical.choice
    (SingleComplexBaseChange.nonempty_coordinates.{u, w} g' K K' φ)
  dsimp only [SingleComplexBaseChange.StalkCondition]
  intro d z i
  let e := Classical.choice
    (SingleComplexBaseChange.nonempty_stalkComparison_open_arrow_iso.{u, w}
      f f' g g' sq K K' φ c U sqU d z i)
  have h_original := h_stalk c (pullback.fst g' U.ι z) i
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
    AddCommGrpCat.{u}
  let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat.{u}
  have h_map : IsIso (F.map
      (SingleComplexBaseChange.stalkComparison f f' g g' sq c
        (pullback.fst g' U.ι z) i)) := inferInstance
  have h_restricted := (Arrow.isIso_iff_isIso_of_isIso e.hom).mp h_map
  exact isIso_of_reflects_iso _ FU

end AlgebraicGeometry
