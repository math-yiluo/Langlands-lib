/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeCodomainIso
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeDomainIso
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Transport of the derived mate in its base coordinates

Source: Stacks Project, Tags 08HY, 0D5S and 0D5T.
(blueprint: lem-pc-derived-base-change-base-coordinates).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- Change the two base schemes, keeping the upper-left scheme fixed.
Source: Stacks Project, Tag 08HY (counit description), Tags 0D5S and 0D5T.
(blueprint: lem-pc-derived-base-change-base-coordinates).

Proof: Use the coherent pullback comparisons selected in
exists_derivedPullbackComposition and the derived adjunctions pinned to their counits
in schemeDerivedBaseChangeMap. For an isomorphism s, the unit laws and comparisons
for s.hom and s.inv identify their composite pullbacks with the identity. Thus the
pullback along s.hom is an equivalence, whose inverse is pullback along s.inv.
The right adjoint of this equivalence is its inverse. Uniqueness of right adjoints,
using the pinned adjunction, identifies R(s.inv)_* with L(s.hom)^*.
Write V = L(eT.hom)^*. The comparison for f' followed by eT.hom, and its right
adjoint mate, followed by eT.inv give b : Rf'_* ≅ R(f' eT)_* R(eT.inv)_*.
Similarly the right-adjoint comparison for f eS gives
R(f eS)_* ≅ Rf_* R(eS.hom)_*. Compose with the pullback comparison for
(eT.inv g) eS and the inverse-equivalence counits for eS and eT to obtain
Rf_* Lg^* ≅ R(f eS)_* L(eT.inv g eS)^* R(eT.inv)_*, namely a.
These are mates of the selected comparisons, not independent choices of adjunctions.
To check the displayed square, apply V's inverse-equivalence identification and
transpose under L(f' eT)^* ⊣ R(f' eT)_*. By the defining mate formula, the right
side transposes to Lg'^* applied to the counit for f eS, with the comparison for
g' (f eS). The composite-adjunction counit formula expresses this counit as the
counit of eS followed by that of f. The inverse-equivalence counit cancels the eS
factor of a. On the left, the definition of b as the right-adjoint mate cancels
the eT factor and leaves the transpose of the original mate. Pullback associativity
and the two unit laws identify both expressions with Lg'^* of the counit of f.
The Hom equivalence and the equivalence along eT are faithful, giving the equation.
All comparisons are natural, so it holds for every E. The argument uses only a
commutative square, and applies to identity coordinates, empty schemes and zero E. -/
theorem exists_derivedBaseChange_base_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B)
    (hA : g' ≫ (f ≫ eS.hom) =
      (f' ≫ eT.hom) ≫ (eT.inv ≫ g ≫ eS.hom)) :
    let fA := f ≫ eS.hom
    let gA := eT.inv ≫ g ≫ eS.hom
    let T := schemeDerivedDirectImage eT.inv
    ∃ b : schemeDerivedDirectImage f' ≅
        schemeDerivedDirectImage (f' ≫ eT.hom) ⋙ T,
    ∃ a : schemeDerivedDirectImage f ⋙ derivedPullback g ≅
        schemeDerivedDirectImage fA ⋙ derivedPullback gA ⋙ T,
      ∀ E : schemeDerivedCategory X,
        schemeDerivedBaseChangeMap f f' g g' h E ≫
            b.hom.app ((derivedPullback g').obj E) =
          a.hom.app E ≫ T.map
            (schemeDerivedBaseChangeMap fA (f' ≫ eT.hom) gA g' hA E) := by
  have hS : g' ≫ (f ≫ eS.hom) = f' ≫ (g ≫ eS.hom) := by
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ eS.hom) h
  obtain ⟨aS, haS⟩ := exists_derivedBaseChange_codomain_iso f g g' f' h eS hS
  obtain ⟨b, aT, haT⟩ := exists_derivedBaseChange_domain_iso
    (f ≫ eS.hom) (g ≫ eS.hom) g' f' hS eT hA
  refine ⟨b, aS ≪≫ aT, ?_⟩
  intro E
  calc
    _ = (aS.hom.app E ≫
        schemeDerivedBaseChangeMap (f ≫ eS.hom) f' (g ≫ eS.hom) g' hS E) ≫
        b.hom.app ((derivedPullback g').obj E) := by rw [haS E]
    _ = aS.hom.app E ≫ (aT.hom.app E ≫ (schemeDerivedDirectImage eT.inv).map
        (schemeDerivedBaseChangeMap (f ≫ eS.hom) (f' ≫ eT.hom)
          (eT.inv ≫ g ≫ eS.hom) g' hA E)) := by
      rw [Category.assoc, haT E]
    _ = _ := by simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]


end AlgebraicGeometry
