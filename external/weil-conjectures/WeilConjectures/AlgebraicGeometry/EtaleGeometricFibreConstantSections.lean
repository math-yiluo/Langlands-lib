/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant
import all WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback

/-!
# Sections on a connected geometric fibre

Source: Stacks Project, Étale Cohomology, Lemma 59.39.3 (Tag 0A3H), final paragraph,
and Remark 59.23.2 (Tag 03P5), set-valued form
(blueprint: lem-weil-pbc-etale-geometric-fibre-constant-sections).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The inverse image over a geometric point is the constant sheaf of its stalk.
Its global sections on a nonempty connected scheme are exactly the constant sections,
and further pullback preserves their values, even on an empty or disconnected scheme.
The comparison is the canonical, germ-normalized family supplied by
`etaleGeometricFibreInverseImageConstant`; the equality fixes that family's choice.
Global sections are evaluated at the identity étale object. After base change this
object is canonically the identity object of the source, so the final equation is
an equation of global sections there.

Source: Stacks Project, Étale Cohomology, Lemma 59.39.3 (Tag 0A3H), final paragraph,
and Remark 59.23.2 (Tag 03P5), set-valued form
(blueprint: lem-weil-pbc-etale-geometric-fibre-constant-sections).

Proof:
1. For `q = h ≫ s`, use lem-weil-pbc-etale-geometric-fibre-inverse-image-constant
   and lem-weil-pbc-sets-etale-inverse-image-composition-units to identify `q⁻¹F`
   canonically with the constant sheaf of `F_s`. Use the chosen germ-normalized family.
2. On nonempty connected `U`, the constant-section map is bijective by
   lem-weil-pbc-constant-sheaf-set-sections-connected-natural, applied to `F_s`.
   Composing it with the inverse comparison on sections gives the displayed bijection.
   The nonemptiness is included in def-weil-connected-scheme (`ConnectedSpace U`).
3. For `v : V → U`, the naturality clause of the first comparison and the
   constant-section naturality clause of the second lemma identify the unit-pullback
   with the section having the same stalk value on `V`. The composition comparison
   of lem-weil-pbc-sets-etale-inverse-image-composition-units converts the iterated
   inverse image to the inverse image along `v ≫ h ≫ s`. This uses no connectedness
   or nonemptiness of `V`. -/
theorem etaleGeometricFibreConstantSections
    (S : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ∃ α : ∀ (U : Scheme.{u}) (h : U ⟶ Spec (.of Ω)),
      Scheme.etaleSetPullback (h ≫ s) ≅
        (Scheme.pointSmallEtale s).sheafFiber ⋙
          constantSheaf U.smallEtaleTopology (Type (u + 1)),
      α = Classical.choose (etaleGeometricFibreInverseImageConstant S Ω s) ∧
      ∀ (U : Scheme.{u}) (h : U ⟶ Spec (.of Ω)) [ConnectedSpace U]
        (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
        Function.Bijective (fun e : (Scheme.pointSmallEtale s).sheafFiber.obj F =>
          ((α U h).inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 U)))
            ((toSheafify U.smallEtaleTopology
              ((Functor.const U.Etaleᵒᵖ).obj
                ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
                  (op (Scheme.Etale.mk (𝟙 U))) e)) ∧
        ∀ (V : Scheme.{u}) (v : V ⟶ U)
          (e : (Scheme.pointSmallEtale s).sheafFiber.obj F),
          (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
            S U V (h ≫ s) v).hom.app F).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj
              (Scheme.Etale.mk (𝟙 U))))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
              (U.smallGrothendieckTopology @Etale)
              (V.smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback (h ≫ s)).obj F)).hom.app
                  (op (Scheme.Etale.mk (𝟙 U)))
              (((α U h).inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 U)))
                ((toSheafify U.smallEtaleTopology
                  ((Functor.const U.Etaleᵒᵖ).obj
                    ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
                      (op (Scheme.Etale.mk (𝟙 U))) e))) =
          (((α V (v ≫ h)).inv.app F ≫
            eqToHom (congrArg
              (fun k : V ⟶ S => (Scheme.etaleSetPullback k).obj F)
              (Category.assoc v h s))).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj
                  (Scheme.Etale.mk (𝟙 U)))))
            ((toSheafify V.smallEtaleTopology
              ((Functor.const V.Etaleᵒᵖ).obj
                ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
                  (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj
                    (Scheme.Etale.mk (𝟙 U)))) e) := by
  classical
  let α := Classical.choose (etaleGeometricFibreInverseImageConstant S Ω s)
  have hα := Classical.choose_spec (etaleGeometricFibreInverseImageConstant S Ω s)
  refine ⟨α, rfl, ?_⟩
  intro U h _ F
  constructor
  · have hi : Function.Bijective
        (((α U h).inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 U)))) := by
      exact (CategoryTheory.isIso_iff_bijective _).1 inferInstance
    exact hi.comp (Scheme.set_constant_sections_bijective U
      ((Scheme.pointSmallEtale s).sheafFiber.obj F))
  · intro V v e
    exact hα.2 U V h v F (Scheme.Etale.mk (𝟙 U)) e

end AlgebraicGeometry
