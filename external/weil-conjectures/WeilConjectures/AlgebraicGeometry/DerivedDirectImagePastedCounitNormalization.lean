/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCompositionCounitApex

/-! # Counit calculations for pullback composition
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-direct-image-pasted-counit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Adjunction.comp
  Scheme.Modules.tensorPullback DerivedCategory.Qh
private theorem counit_of_normalization
    {C D H J : Type*} [Category* C] [Category* D] [Category* H] [Category* J]
    {T : C ⥤ D} {U : D ⥤ C} {L : H ⥤ J} {R : J ⥤ H}
    (b : T ⊣ U) (a : L ⊣ R) (Q : C ⥤ H) (P : D ⥤ J)
    (ε : Q ⋙ L ⟶ T ⋙ P) (β : U ⋙ Q ⟶ P ⋙ R)
    (hc : ∀ M K (t : T.obj M ⟶ K),
      a.homEquiv (Q.obj M) (P.obj K) (ε.app M ≫ P.map t) =
        Q.map (b.homEquiv M K t) ≫ β.app K) (K : D) :
    L.map (β.app K) ≫ a.counit.app (P.obj K) =
      ε.app (U.obj K) ≫ P.map (b.counit.app K) := by
  have hid : b.homEquiv _ K (b.counit.app K) = 𝟙 _ := by
    exact b.right_triangle_components K
  have h := hc _ K (b.counit.app K)
  rw [hid, Q.map_id, Category.id_comp] at h
  have h' := congrArg (a.homEquiv _ _).symm h
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply] using h'.symm

private theorem pasted_counit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {Lf : D ⥤ C} {Rf : C ⥤ D} {Lg : E ⥤ D} {Rg : D ⥤ E}
    (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg)
    {K : C} {H : D} {M : E}
    (βf : H ⟶ Rf.obj K) (βg : M ⟶ Rg.obj H)
    (vf : Lf.obj H ⟶ K) (vg : Lg.obj M ⟶ H)
    (hf : Lf.map βf ≫ af.counit.app K = vf)
    (hg : Lg.map βg ≫ ag.counit.app H = vg) :
    (Lg ⋙ Lf).map (βg ≫ Rg.map βf) ≫ (ag.comp af).counit.app K =
      Lf.map vg ≫ vf := by
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← Lf.map_comp_assoc (Lg.map (Rg.map βf)) (ag.counit.app _)]
  rw [show Lg.map (Rg.map βf) ≫ ag.counit.app (Rf.obj K) =
    ag.counit.app H ≫ βf from ag.counit.naturality βf]
  rw [Lf.map_comp, Category.assoc, ← Lf.map_comp_assoc, hg, hf]


private theorem forward_of_counit {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {M : C} {K : D}
    (γ : M ⟶ R.obj K) (δ : L.obj M ⟶ K)
    (h : L.map γ ≫ a.counit.app K = δ) : a.homEquiv M K δ = γ := by
  apply (a.homEquiv M K).symm.injective
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply] using h.symm

variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

set_option linter.all false in
-- Avoid repeating the expensive chosen-object type comparisons during linting.
-- The selected adjunctions and composite sheaf instances need a larger budget.
/-- The pasted right-derived units transpose to the explicit pasted underived counits.
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-direct-image-pasted-counit-normalization).

Proof: For each s=f,g, evaluate the pinned Hom formula in
exists_schemeDerivedAdjunction at the underived s-counit. Its adjunct is the
identity by the right triangle identity; apply the inverse derived Hom equivalence
to obtain Ls(β(s)) followed by the derived s-counit equal to ε(s) followed by the
localized underived s-counit. Expand the composite-adjunction counit as
Lf of the g-counit followed by the f-counit. Functoriality expands the image of
the pasted units. Naturality of the derived g-counit moves Rg(β(f)) through it.
Group the two Lf-images and substitute the g-normalization, then substitute the
f-normalization. Functoriality and associativity give the explicit counit expression.
The inverse-forward law of the composite Hom equivalence gives the stated forward form.
This is a natural transformation calculation, valid also for identity morphisms,
zero complexes and empty schemes. -/
theorem derivedDirectImage_pasted_counit_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    ((schemeHomPullbackAdjunction.{u, w} g).comp
      (schemeHomPullbackAdjunction.{u, w} f)).homEquiv
        (((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) (DerivedCategory.Qh.obj K)
        (derivedCompositionCounitApex f g K) =
      (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (schemeDerivedDirectImage g).map
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K)
    := by
  classical
  apply forward_of_counit
    ((schemeHomPullbackAdjunction.{u, w} g).comp (schemeHomPullbackAdjunction.{u, w} f))
  rw [derivedCompositionCounitApex_eq]
  dsimp only
  let H := ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K
  let M := ((Scheme.Modules.pushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).obj H
  let a {A B : Scheme.{u}} (s : A ⟶ B) := schemeHomPullbackAdjunction.{u, w} s
  let b {A B : Scheme.{u}} (s : A ⟶ B) :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).mapHomotopyCategory
      (ComplexShape.up ℤ)
  let ε {A B : Scheme.{u}} (s : A ⟶ B) :=
    (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
  have hc {A B : Scheme.{u}} (s : A ⟶ B)
      (H : HomotopyCategory (SheafOfModules.{u} (moduleRings B.toRingedSpace)) (ComplexShape.up ℤ))
      (J : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (ComplexShape.up ℤ))
      (t : ((Scheme.Modules.tensorPullback s).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj H ⟶ J) :
      (a s).homEquiv (DerivedCategory.Qh.obj H) (DerivedCategory.Qh.obj J)
        ((ε s).app H ≫ DerivedCategory.Qh.map t) =
      (DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings B.toRingedSpace))).map
          ((b s).homEquiv H J t) ≫
        (RingedSpace.moduleDirectImage s.toLRSHom.toShHom).rightDerivedFunctorUnit.app J := by
    exact Classical.choose_spec (exists_schemeDerivedAdjunction s
      (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
      (ε s) ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) s)) H J t
  have he {A B : Scheme.{u}} (s : A ⟶ B)
      (J : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace))
        (ComplexShape.up ℤ)) :=
    counit_of_normalization (b s) (a s)
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings B.toRingedSpace)))
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings A.toRingedSpace)))
      (ε s) (RingedSpace.moduleDirectImage s.toLRSHom.toShHom).rightDerivedFunctorUnit
      (hc s) J
  exact pasted_counit (a f) (a g)
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K)
    ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app H)
    ((ε f).app H ≫ DerivedCategory.Qh.map ((b f).counit.app K))
    ((ε g).app M ≫
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).map
        ((b g).counit.app H))
    (he f K) (he g H)

end AlgebraicGeometry
