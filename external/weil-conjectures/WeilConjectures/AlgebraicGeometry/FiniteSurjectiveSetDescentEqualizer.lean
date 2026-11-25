/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentLocalLifts
/-! # Lifting compatible sections along a finite surjective morphism

Source: Stacks Project, Étale Cohomology, Remark 09Z3 and Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-surjective-descent-equalizer).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
private theorem unit_injective_on_object
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) :
    Function.Injective (etaleSetDescentUnit f G U) := by
  intro a b hab
  apply etaleSetSection_ext_of_geometric_germs X G U a b
  intro Ω _ _ y z
  obtain ⟨x', hx'⟩ := f.surjective (y default)
  obtain ⟨⟨t, ht⟩, -⟩ :=
    Scheme.Hom.GeometricFiber.exists_apply_default_eq (f := f) (y := y) x' hx'
  subst y
  obtain ⟨c, -, hc, -⟩ := etaleSetInverseImageStalkGerm X X' f G Ω t
  let z' : (Scheme.pointSmallEtale t).fiber.obj
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) :=
    Over.homMk (pullback.lift z.left t (Over.w z))
      (pullback.lift_snd z.left t (Over.w z))
  have he := congrArg (fun s' ↦ c ((Scheme.pointSmallEtale t).toPresheafFiber
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) z'
    ((Scheme.etaleSetPullback f).obj G).obj s')) hab
  exact (hc U z a).symm.trans (he.trans (hc U z b))

private theorem lift_of_covering_image
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F H : Sheaf J (Type (u + 1))} (φ : F ⟶ H)
    (hinj : ∀ U : C, Function.Injective (φ.hom.app (op U)))
    {U : C} (s : H.obj.obj (op U))
    (hcover : Presheaf.imageSieve φ.hom s ∈ J U) :
    ∃ t : F.obj.obj (op U), φ.hom.app (op U) t = s := by
  classical
  let x := Presieve.FamilyOfElements.localPreimage φ.hom s
  have hx : x.Compatible := by
    intro V W Z a b i j hi hj hab
    apply hinj Z
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    dsimp [x, Presieve.FamilyOfElements.localPreimage]
    rw [Presheaf.app_localPreimage, Presheaf.app_localPreimage]
    change (H.obj.map i.op ≫ H.obj.map a.op) s =
      (H.obj.map j.op ≫ H.obj.map b.op) s
    rw [← H.obj.map_comp, ← H.obj.map_comp, ← op_comp, ← op_comp, hab]
  let hF := F.property.isSheafFor _ hcover
  refine ⟨hF.amalgamate x hx, ?_⟩
  apply (H.property.isSheafFor _ hcover).isSeparatedFor.ext
  intro V i hi
  rw [← NatTrans.naturality_apply, hF.valid_glue hx i hi]
  exact Presheaf.app_localPreimage φ.hom s i hi

/-- Source: Stacks Project, Étale Cohomology, Remark 09Z3, following Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-surjective-descent-equalizer).
Every compatible section is in the image of the unit.

Proof:
1. Write D = X' ×_X X', with projections p and q and composite h = p ≫ f = q ≫ f.
   Both p and h are finite, by finite base change and composition.
2. Let A = f_* f⁻¹G and B = h_* h⁻¹G. At U, the two maps A(U) → B(U)
   are pullback by p or q, followed by the chosen inverse-image comparison and
   the canonical fibre-product pasting isomorphism. Naturality of units and of
   the comparisons makes these maps morphisms of sheaves.
3. Their sectionwise equalizer E is a sheaf. The composition-unit equation shows
   the unit G → A equalizes these two morphisms, hence factors as ψ : G → E.
4. Fix a geometric point x : Spec Ω → X. Its set P of lifts to X' is nonempty:
   lift the underlying point using surjectivity, then use finite geometric-point
   lifting. Lifts to D correspond to P × P by the pullback universal property.
5. Finite pushforward stalks and the inverse-image germ bijection identify A_x
   with the product of G_x over P, and B_x with its product over P × P.
6. Under these identifications the unit is the diagonal. Indeed, restriction of
   the germ of a unit-pulled-back section to a lift is its pulled-back germ, and
   the inverse-image stalk bijection sends it to the original germ. Every stalk
   element is represented by a section, so this verifies the diagonal on all elements.
7. The composition comparisons respect the inverse-image stalk identifications:
   both composites send every iterated unit-pulled-back germ to the original germ,
   by the composition-unit equation. The germ theorem says these germs generate
   the inverse-image stalk and uniquely determine that map. Thus the composites agree.
8. A germ of a section of A is represented over some U ×_X X'. Pulling it to D
   through p or q, the pointed fibre-product pasting identifies its germ with
   the restriction at the corresponding lift. Step 7 then says the maps on
   stalks are the two coordinate projections from the P-indexed product.
9. Stalks preserve the equalizer E. By step 8, its stalk consists of constant
   families. Since P is nonempty, the diagonal is a bijection G_x → E_x.
10. Geometric stalks detect isomorphisms, so ψ is an isomorphism. At U = X this
    makes G(X) → E(X) bijective. Compatibility is membership in E(X), so the
    inverse supplies a preimage of every compatible section. Conversely every
    unit section is compatible by step 3. If X is empty, the empty sheaf covering
    supplies the unique section and the compatibility equation is automatic. -/
theorem finiteSurjectiveSetDescent_compatible_lift
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
          ∃ s : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
            etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X)) s = s' := by
  intro s' hs'
  let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale)
    (X'.smallGrothendieckTopology @Etale)).unit.app G
  have hinj : ∀ U : X.Etale, Function.Injective (η.hom.app (op U)) :=
    unit_injective_on_object f G
  have hcover := finiteSurjectiveSetDescent_compatible_locally_lifts f G s' hs'
  exact lift_of_covering_image η hinj s' hcover

end AlgebraicGeometry
