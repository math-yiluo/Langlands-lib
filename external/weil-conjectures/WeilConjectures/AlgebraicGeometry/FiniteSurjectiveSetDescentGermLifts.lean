/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentCoordinatesConstant
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.FinitePushforwardSetStalk
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

/-! # Compatible finite-descent sections have preimages on geometric stalks

Source: Stacks Project, Étale Cohomology, Lemma 09Z2 and Remark 09Z3.
(blueprint: lem-weil-pbc-sets-finite-descent-germ-lifts).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem descent_coordinate
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x}) :
    ∃ c : (Scheme.pointSmallEtale t.1).sheafFiber.obj
        ((Scheme.etaleSetPullback f).obj G) →
        (Scheme.pointSmallEtale x).sheafFiber.obj G,
      Function.Bijective c ∧ ∀ a : (Scheme.pointSmallEtale x).sheafFiber.obj G,
        c ((colimit.pre
          ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op)
          ((Scheme.pointSmallEtale x).sheafFiber.map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G) a)) = a := by
  rcases t with ⟨t, ht⟩
  subst x
  obtain ⟨c, hc, hg, -⟩ := etaleSetInverseImageStalkGerm X X' f G Ω t
  refine ⟨c, hc, ?_⟩
  intro a
  obtain ⟨U, z, s, rfl⟩ :=
    (Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber_jointly_surjective (P := G.obj) a
  change c ((colimit.pre
    ((Functor.Elements.π (Scheme.pointSmallEtale t).fiber).op ⋙
      ((Scheme.etaleSetPullback f).obj G).obj)
    (Etale.baseChangeNbhd f (t ≫ f) ⟨t, rfl⟩).op)
      ((Scheme.pointSmallEtale (t ≫ f)).presheafFiber.map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
      (X.smallGrothendieckTopology @Etale)
      (X'.smallGrothendieckTopology @Etale)).unit.app G).hom
      ((Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber U z G.obj s))) = _
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  have hpre := ConcreteCategory.congr_hom
    (colimit.ι_pre
      ((Functor.Elements.π (Scheme.pointSmallEtale t).fiber).op ⋙
        ((Scheme.etaleSetPullback f).obj G).obj)
      (Etale.baseChangeNbhd f (t ≫ f) ⟨t, rfl⟩).op (op (Functor.elementsMk _ U z)))
    (etaleSetDescentUnit f G U s)
  erw [hpre]
  exact hg U z s

/-- Source: Stacks Project, Étale Cohomology, Lemma 09Z2 and Remark 09Z3.
(blueprint: lem-weil-pbc-sets-finite-descent-germ-lifts).

Proof: Fix a geometric point x. Its lift set P along f is nonempty: choose a
point above x and use finite geometric-point lifting with the same algebraically
closed field. Finite-pushforward stalks identify the stalk of f_*f⁻¹G with the
product of the inverse-image stalks indexed by P. The germ-compatible inverse-image
bijections identify each factor with G_x, and identify the unit with the diagonal.
The same construction for h = p₁ ≫ f identifies its stalk with the product indexed
by P × P, using the pullback universal property. The composition-unit formula shows
that the two comparison maps on germs act by the two projections P × P → P.
To check this formula for arbitrary inverse-image germs, use the inverse-image
bijection to represent them as germs of unit-pulled-back sections; on these germs
it is exactly the composition-unit formula. Compatibility of s' therefore says all
coordinates of its germ are equal. Choose any lift in P and take its coordinate a.
The diagonal formula and injectivity of the finite-pushforward product map imply
that the image of a under the stalk unit is the germ of s'. This statement stops at
the stalk: representing a and realizing germ equality on a refinement, and proving
the resulting sieve covers, are separate steps. If X is empty there is no geometric
point x, so the assertion is vacuous. -/
theorem finiteSurjectiveSetDescent_compatible_germ_lifts
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ∀ s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk (𝟙 X)))),
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s') →
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (x : Spec (.of Ω) ⟶ X)
            (z : (Scheme.pointSmallEtale x).fiber.obj (Scheme.Etale.mk (𝟙 X))),
            ∃ a : (Scheme.pointSmallEtale x).sheafFiber.obj G,
              (Scheme.pointSmallEtale x).sheafFiber.map
                ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G) a =
                (Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 X)) z
                  ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
                    X.smallEtaleTopology X'.smallEtaleTopology).obj
                      ((Scheme.etaleSetPullback f).obj G)).obj s' := by
  classical
  intro s' hs Ω _ _ x z
  choose c hc hdiag using descent_coordinate f G x
  let α := (Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 X)) z
      ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology X'.smallEtaleTopology).obj
          ((Scheme.etaleSetPullback f).obj G)).obj s'
  let r := fun t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x} ↦ (colimit.pre
          ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op)
  obtain ⟨x', hx'⟩ := f.surjective (x default)
  obtain ⟨⟨t₀, ht₀⟩, -⟩ :=
    Scheme.Hom.GeometricFiber.exists_apply_default_eq (f := f) (y := x) x' hx'
  let t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x} := ⟨t₀, ht₀⟩
  refine ⟨c t (r t α), ?_⟩
  apply (finite_pushforward_set_stalk_bijective f ((Scheme.etaleSetPullback f).obj G) x).2.1
  funext v
  apply (hc v).1
  change c v (r v ((Scheme.pointSmallEtale x).sheafFiber.map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
      (X.smallGrothendieckTopology @Etale)
      (X'.smallGrothendieckTopology @Etale)).unit.app G) (c t (r t α)))) =
    c v (r v α)
  rw [hdiag]
  exact finiteSurjectiveSetDescent_coordinates_constant f G Ω x c hc hdiag s' hs z t v

end AlgebraicGeometry
