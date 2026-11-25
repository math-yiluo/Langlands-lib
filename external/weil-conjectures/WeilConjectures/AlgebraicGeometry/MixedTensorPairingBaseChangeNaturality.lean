/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Base change preserves the direct-image tensor pairing
Source: Stacks Project, cohomology.tex Tag 08I3 and Remark 08HY;
duality.tex Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-tensor-pairing-base-change-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Naturality in the object of the canonical derived base-change map.
Source: Stacks Project, cohomology.tex, Remark 08HY.
(blueprint: lem-sc-mixed-tensor-pairing-base-change-naturality).

Proof: express the map as the adjoint transpose of the pullback-composition square
comparison followed by the pulled-back counit. Naturality of the composition
comparison moves the direct-image of a across the comparison. Naturality of the
counit moves a across the counit. Functoriality of pullback combines these equations.
Naturality of the adjunction Hom equivalence then gives the asserted equality. -/
theorem mixedTensorPairing_baseChange_naturality
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) {E F : schemeDerivedCategory X} (a : E ⟶ F) :
    schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map a) =
      (derivedPullback g).map ((schemeDerivedDirectImage f).map a) ≫
        schemeDerivedBaseChangeMap f f' g g' h F := by
  symm
  let adj (k : X' ⟶ S') := Classical.choose (exists_schemeDerivedAdjunction k
    (hAdd := (Classical.choose exists_derivedPullbackComposition) k)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) k))
  let adjf := Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))
  let comp : ∀ {Y Z W : Scheme.{u}} (k : Y ⟶ Z) (l : Z ⟶ W),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let t : derivedPullback g ⋙ derivedPullback f' ⟶
      derivedPullback f ⋙ derivedPullback g' :=
    (comp f' g).hom ≫
      (eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm)).hom ≫ (comp g' f).inv
  let q : schemeDerivedDirectImage f ⋙ derivedPullback g ⋙ derivedPullback f' ⟶
      𝟭 (schemeDerivedCategory X) ⋙ derivedPullback g' :=
    Functor.whiskerLeft (schemeDerivedDirectImage f) t ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight adjf.counit (derivedPullback g')
  have hq := q.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hq
  unfold schemeDerivedBaseChangeMap
  refine (adj f').homEquiv_naturality_left_square _ _ _ _ ?_
  dsimp only [q, t, eqToIso, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app] at hq
  simpa only [Category.id_comp, Category.comp_id, Category.assoc, eqToHom_app] using hq

end AlgebraicGeometry
