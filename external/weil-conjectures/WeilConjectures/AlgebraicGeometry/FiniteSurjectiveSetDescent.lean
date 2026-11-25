/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Finite surjective descent of global sections for étale sheaves of sets

Source: literature/stacks-project/etale-cohomology.tex, Remark 09Z3
(blueprint: lem-weil-pbc-sets-finite-surjective-descent).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Source: Stacks Project, Étale Cohomology, Remark 09Z3, following Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-surjective-descent)
The unit on global sections is injective with image exactly the equalizer of the
projection pullbacks, composed with the inverse-image composition comparisons.

Proof:
1. The first projection is finite by lem-weil-pbc-finite-morphism-permanence;
   its composite with f is finite by lem-weil-pbc-finite-composition.
2. Construct A = f_* f⁻¹G and B = f₁* f₁⁻¹G, their unit and the two projection
   maps, using lem-weil-pbc-sets-etale-inverse-image-composition-units and the
   natural fibre-product pasting isomorphisms of def-pc-fibre-product.
3. The composition unit equation makes the unit equalize these maps. The
   sectionwise equalizer E is a sheaf by lem-weil-pbc-site-sheaf-sets-limits-sectionwise.
4. At a geometric point the lifts P are nonempty by surjectivity and
   lem-weil-pbc-finite-geometric-point-lift. The double-fibre lifts are P × P.
5. By lem-weil-pbc-sets-finite-pushforward-stalk and
   lem-weil-pbc-sets-etale-inverse-image-stalk-germ, the stalks of A and B are
   products of G's stalk over P and P × P respectively.
6. The unit becomes the diagonal: check on germs using the germ formula of
   lem-weil-pbc-sets-etale-inverse-image-stalk-germ and def-weil-pbc-category-colimit.
7. The composition comparisons respect stalk identifications: check on the
   locally generating pulled-back germs using the composition unit equation.
8. Thus the two maps on stalks become the two coordinate projections; verify
   on germs of sections of A using the canonical pointed fibre-product isomorphisms.
9. By lem-weil-pbc-sets-etale-stalk-finite-limits, E's stalk is the equalizer,
   hence exactly the constant families. Nonemptiness of P makes its diagonal bijective.
10. The geometric stalk criterion lem-weil-pbc-sets-etale-iso-on-geometric-stalks
    gives G ≅ E. Evaluate at the identity étale neighbourhood to get the claim. -/
theorem finiteSurjectiveSetDescent
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Function.Injective (etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X))) ∧
      ∀ s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk (𝟙 X)))),
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s') ↔
          ∃ s : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
            etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X)) s = s' := by
  constructor
  · exact finiteSurjectiveSetDescent_injective f G
  · intro s'
    constructor
    · exact finiteSurjectiveSetDescent_compatible_lift f G s'
    · rintro ⟨s, rfl⟩
      have hunit (W : Scheme.{u}) (g : W ⟶ X') :
          etaleSetDescentComparison f g G (Scheme.Etale.mk (𝟙 X))
              (etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X)) s) =
            etaleSetDescentUnit (g ≫ f) G (Scheme.Etale.mk (𝟙 X)) s := by
        have h := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
          X X' W f g G (Scheme.Etale.mk (𝟙 X)) s
        unfold etaleSetDescentComparison
        erw [h]
        simp [etaleSetDescentUnit, ← Functor.map_comp_apply, ← op_comp]
      have unit_transport {a b : pullback f f ⟶ X} (e : a = b) :
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) e)
            (etaleSetDescentUnit a G (Scheme.Etale.mk (𝟙 X)) s) =
            etaleSetDescentUnit b G (Scheme.Etale.mk (𝟙 X)) s := by
        subst b
        rfl
      exact (hunit _ (pullback.fst f f)).trans
        ((unit_transport ((pullback.condition (f := f) (g := f)).symm)).symm.trans
          (congrArg (fun z ↦ eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm) z)
            (hunit _ (pullback.snd f f)).symm))


end AlgebraicGeometry
