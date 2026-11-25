/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.Basic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Injective abelian sheaves restrict surjectively along monomorphisms

Source: Stacks Project, Cohomology on Sites, Tag 093X.
(blueprint: lem-weil-pbc-injective-sheaf-mono-restriction)
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max w v}]

/-- Source: Stacks Project, Tag 093X, specialized to abelian sheaves.
(blueprint: lem-weil-pbc-injective-sheaf-mono-restriction)

Proof: Evaluation at U is represented by the sheafification of the free abelian
presheaf on the (universe-lifted) representable U. A monomorphism a : U' → U gives
an objectwise injective map between the representables, hence a monomorphism of
free abelian presheaves. Sheafification preserves this monomorphism. A section of
an injective sheaf over U' corresponds to a morphism from that free sheaf; extend
it along the monomorphism by injectivity. Evaluate the extension on the generator
id_U. Naturality and the extension identity show its restriction is the given
section. This also works for an empty object and for the zero sheaf. -/
theorem injective_sheaf_mono_restriction
    (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I]
    {U' U : C} (a : U' ⟶ U) [Mono a] : Function.Surjective (I.obj.map a.op) := by
  let P (W : C) : Sheaf J AddCommGrpCat.{max w v} :=
    (presheafToSheaf J _).obj (uliftYoneda.{w}.obj W ⋙ AddCommGrpCat.free)
  let t : (uliftYoneda.{w}.obj U' ⋙ AddCommGrpCat.free) ⟶
      (uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free) :=
    Functor.whiskerRight (uliftYoneda.{w}.map a) AddCommGrpCat.free
  have ht : Mono t := by
    have (W : Cᵒᵖ) : Mono (t.app W) := by
      have : Mono ((uliftYoneda.{w}.map a).app W) := by
        rw [mono_iff_injective]
        intro x y hxy
        apply ULift.ext
        apply (cancel_mono a).1
        exact congrArg ULift.down hxy
      exact Functor.map_mono AddCommGrpCat.free _
    exact NatTrans.mono_of_mono_app t
  let f : P U' ⟶ P U := (presheafToSheaf J _).map t
  have : Mono f := inferInstance
  let e (W : C) (g : P W ⟶ I) : I.obj.obj (op W) :=
    g.hom.app (op W) ((toSheafify J (uliftYoneda.{w}.obj W ⋙ AddCommGrpCat.free)).app
      (op W) (Sheaf.freeYonedaGen.{w} W))
  intro s
  let b : P U' ⟶ I :=
    ⟨sheafifyLift J (Sheaf.freeYonedaPresheafHom.{w} U' I.obj s) I.property⟩
  let g := Injective.factorThru b f
  refine ⟨e U g, ?_⟩
  have hg : f ≫ g = b := Injective.comp_factorThru b f
  have he : e U' b = s := by
    change ((toSheafify J _ ≫ sheafifyLift J
      (Sheaf.freeYonedaPresheafHom.{w} U' I.obj s) I.property).app (op U')) _ = s
    rw [toSheafify_sheafifyLift]
    exact Sheaf.freeYonedaPresheafHom_gen U' I.obj s
  rw [← he, ← hg]
  dsimp [e]
  rw [← ConcreteCategory.comp_apply, ← g.hom.naturality]
  rw [ConcreteCategory.comp_apply]
  congr 1
  change ((toSheafify J _).app (op U) ≫ (P U).obj.map a.op)
      (Sheaf.freeYonedaGen.{w} U) =
    ((toSheafify J _).app (op U') ≫ f.hom.app (op U')) (Sheaf.freeYonedaGen.{w} U')
  rw [← (toSheafify J _).naturality]
  rw [ConcreteCategory.comp_apply]
  have hgen : (uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free).map a.op
      (Sheaf.freeYonedaGen.{w} U) = FreeAbelianGroup.of (ULift.up a) := by
    simp [Sheaf.freeYonedaGen]
  rw [hgen]
  change _ = ((toSheafify J _ ≫ f.hom).app (op U')) (Sheaf.freeYonedaGen.{w} U')
  change _ = ((toSheafify J _ ≫ sheafifyMap J t).app (op U'))
    (Sheaf.freeYonedaGen.{w} U')
  rw [← toSheafify_naturality]
  dsimp [t]
  simp [Sheaf.freeYonedaGen]
  rfl

end CategoryTheory
