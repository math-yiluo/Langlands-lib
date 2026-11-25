/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement

/-! # The specified internal-Hom comparison is natural

Source: Stacks Project, Tag 03EO, and the internal-Hom naturality field of a
specified twisted action-site presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace CategoryTheory.TwistedActionRingedSite

attribute [local irreducible] sigma SheafOfModules.monoidalCategory
attribute [local implicit_reducible] forgetPairs Endofunctor.Algebra.forget

private theorem forgetPairs_map {A : Type (u + 1)} [Category.{u} A]
    (T : A ⥤ A) {M N : Pairs T} (f : M ⟶ N) :
    (forgetPairs T).map f = f.hom.f := rfl

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {s : C ≌ C} [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    {R : Sheaf J CommRingCat.{u}}
    {a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R}

omit [s.functor.IsContinuous J J] in
private theorem homComparison_naturality (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∀ {M N : (Modules P.coefficient)ᵒᵖ × Modules P.coefficient} (f : M ⟶ N),
      U.map ((Functor.uncurry.obj (SheafOfModules.homFunctor P.coefficient)).map f) ≫
          (P.hom N.1.unop N.2).hom =
        (P.hom M.1.unop M.2).hom ≫
          (Functor.uncurry.obj (SheafOfModules.homFunctor R)).map ((U.op.prod U).map f) := by
  let := P.category
  dsimp only
  intro M N f
  simpa only [Functor.comp_map, Functor.prod_map, Functor.op_map,
    Functor.uncurry_obj_map, SheafOfModules.homFunctor_map_app,
    SheafOfModules.homFunctor_obj_map, SheafOfModules.homObjMap_comp_homObjMap,
    Category.comp_id, Category.id_comp, forgetPairs_map, Quiver.Hom.unop_op]
    using P.hom_naturality f.1.unop f.2

private noncomputable def homComparison (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    Functor.uncurry.obj (SheafOfModules.homFunctor (R := P.coefficient)) ⋙ U ≅
      (U.op.prod U) ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) := by
  exact NatIso.ofComponents (fun M ↦ P.hom M.1.unop M.2) (homComparison_naturality P)

omit [s.functor.IsContinuous J J] in
private theorem homComparison_hom_app (P : Presentation J s R a) :
    letI := P.category
    ∀ M N : Modules P.coefficient,
      (homComparison P).hom.app (op M, N) = (P.hom M N).hom := by
  exact fun M N ↦ rfl

omit [s.functor.IsContinuous J J] in
/-- The presentation's internal-Hom identifications assemble into a natural isomorphism.

Source: Stacks Project, Tag 03EO; the specified presentation's Hom naturality equation.
(blueprint: lem-sf-twisted-action-hom-comparison).

Proof: the uncurried Hom functor maps a pair of arrows by first precomposing and then
postcomposing. The internal-Hom composition formula identifies this with homObjMap of
the pair. Thus P.hom_naturality is exactly the required naturality square. Apply
NatIso.ofComponents to the specified P.hom isomorphisms; the forward components are
those specified maps by construction. -/
theorem hom_comparison (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∃ H : Functor.uncurry.obj (SheafOfModules.homFunctor (R := P.coefficient)) ⋙ U ≅
        (U.op.prod U) ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)),
      ∀ M N : Modules P.coefficient, H.hom.app (op M, N) = (P.hom M N).hom := by
  exact ⟨homComparison P, homComparison_hom_app P⟩

end CategoryTheory.TwistedActionRingedSite
