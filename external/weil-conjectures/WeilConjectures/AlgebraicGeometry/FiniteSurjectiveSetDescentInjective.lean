/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

/-! # Injectivity of finite surjective descent

Source: Stacks Project, Étale Cohomology, Remark 09Z3 and Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-surjective-descent-injective).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Section pullback along the adjunction unit. Source: Stacks, Remark 09Z3
(blueprint: lem-weil-pbc-sets-finite-surjective-descent). 
(blueprint: lem-weil-pbc-sets-finite-surjective-descent-injective)
-/
noncomputable def etaleSetDescentUnit {S T : Scheme.{u}} (e : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U)

/-- Pull back a section and apply the unit-compatible composition comparison, then
identify the iterated fibre product with the composite fibre product.
Source: Stacks, Remark 09Z3 (blueprint: lem-weil-pbc-sets-finite-surjective-descent). 
(blueprint: lem-weil-pbc-sets-finite-surjective-descent-injective)
-/
noncomputable def etaleSetDescentComparison {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) :=
  ((Scheme.etaleSetPullback (g ≫ f)).obj G).obj.map
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app U).op
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2) X Y W f g).hom.app G).hom.app
       (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))
      (etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj G)
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) s))

/-- Source: Stacks Project, Étale Cohomology, Remark 09Z3 and Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-surjective-descent-injective).

Proof: Let two sections have equal pullbacks. For a geometric point of X,
surjectivity supplies a point of X' over its image, and finite geometric-point
lifting supplies a lift with the same algebraically closed field. Apply the
germ-compatible inverse-image stalk bijection at this lift to the equality of
pulled-back sections. Its unit formula says that the original sections have
equal germs at the original geometric point. This holds at every geometric
point. Equality of germs gives equality on an étale neighbourhood of each
point (the stalk is the filtered colimit of pointed neighbourhoods). These
neighbourhoods cover X, so the separatedness axiom of G makes the sections equal.
This also covers the empty scheme, where the empty covering gives at most one section. -/
theorem finiteSurjectiveSetDescent_injective
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Function.Injective (etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X))) := by
  intro a b hab
  apply etaleSetSection_ext_of_geometric_germs X G (Scheme.Etale.mk (𝟙 X)) a b
  intro Ω _ _ y z
  obtain ⟨x', hx'⟩ := f.surjective (y default)
  obtain ⟨⟨t, ht⟩, -⟩ :=
    Scheme.Hom.GeometricFiber.exists_apply_default_eq (f := f) (y := y) x' hx'
  subst y
  obtain ⟨c, -, hc, -⟩ := etaleSetInverseImageStalkGerm X X' f G Ω t
  let U := Scheme.Etale.mk (𝟙 X)
  let z' : (Scheme.pointSmallEtale t).fiber.obj
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) :=
    Over.homMk (pullback.lift z.left t (Over.w z))
    (pullback.lift_snd z.left t (Over.w z))
  have he := congrArg (fun s' ↦ c ((Scheme.pointSmallEtale t).toPresheafFiber
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) z'
    ((Scheme.etaleSetPullback f).obj G).obj s')) hab
  exact (hc U z a).symm.trans (he.trans (hc U z b))

end AlgebraicGeometry
