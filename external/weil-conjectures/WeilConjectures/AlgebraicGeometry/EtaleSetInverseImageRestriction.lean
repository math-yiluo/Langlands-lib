/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Inverse image of étale sheaves of sets along an étale morphism

Source: Stacks Project, Étale Cohomology, Tag 03S2, paragraph after Definition 03S3;
Sites, Tag 00XZ (blueprint: lem-weil-pbc-sets-etale-inverse-image-restriction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tags 03S2 and 00XZ
(blueprint: lem-weil-pbc-sets-etale-inverse-image-restriction).
Restriction is the existing `Etale.localizationRestriction`: on `V → U` its value is
`G(V → U → X)`, with the maps of `G`. It is a sheaf and is naturally isomorphic to
set-valued inverse image. The isomorphism sends a section pulled back by the unit to
restriction along `W ×_X U → W`. Evaluating at `U → U` gives the asserted isomorphism
`(j⁻¹G)(U) ≅ G(U)`.

Proof:
1. By lem-weil-pbc-etale-localization-functor-adjoint, composition with `j` is left
   adjoint to base change, with counit the first fibre-product projection.
   By lem-weil-pbc-sets-etale-inverse-image-composition-units, direct image is
   precomposition with base change and its adjunction unit is the pulled-back section.
2. Covers over `U` remain covers over `X`, and fibre products agree. Thus restriction
   preserves sheaves. Base change preserves sheaves by
   lem-weil-pbc-etale-covering-base-change and situation-conventions.
3. Apply lem-weil-pbc-sets-adjoint-continuous-restriction-adjunction to composition
   and base change. The resulting restriction/direct-image adjunction has unit
   `G(p_W)` for the projection `p_W : W ×_X U → W`.
4. By lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction and
   lem-weil-pbc-sets-etale-inverse-image-composition-units, inverse image is another
   left adjoint to the same direct image. Uniqueness of left adjoints gives a natural
   isomorphism compatible with these units.
5. Evaluate that compatibility on `W` and `s ∈ G(W)` to obtain the displayed equation.
   The component at the identity object of `U.Etale` is the global-sections isomorphism,
   using def-pc-fibre-product to identify `X ×_X U` with `U`. -/
theorem etaleSetInverseImageRestriction {X U : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    ∃ ρ : Scheme.etaleSetPullback j ≅
      Etale.localizationRestriction (Type (u + 1)) j inferInstance,
      ∀ (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (W : X.Etale) (s : G.obj.obj (op W)),
        (ρ.hom.app G).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ j).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ j) (Type (u + 1))
            (X.smallGrothendieckTopology @Etale)
            (U.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op W) s) =
          G.obj.map
            ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
              inferInstance trivial).counit.app W).op s := by
  let adj₁ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ j) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let siteAdj := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial
  let adj₂ := siteAdj.sheafPushforwardContinuous (E := Type (u + 1))
        (U.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
  refine ⟨adj₁.leftAdjointUniq adj₂, ?_⟩
  intro G W s
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ G
  exact congrArg (fun f ↦ f.hom.app (op W) s) h

end AlgebraicGeometry
