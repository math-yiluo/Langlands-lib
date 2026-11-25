/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedQCoh
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedFunctorComparisons

/-! # Projection mate transport along scheme isomorphisms

Source: Stacks Project, Tag 08EU, affine-local reduction, expanded along scheme isomorphisms.
(blueprint: lem-pc-projection-mate-scheme-iso-transport).
-/

@[expose] public section

universe u w w'

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option autoImplicit false

namespace ProjectionMateTransport

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def transportHom
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (a : C' ≌ C) (b : D' ≌ D)
    (F : C ⥤ D) (R : D ⥤ C) (F' : C' ⥤ D') (R' : D' ⥤ C')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (β : R' ⋙ a.functor ≅ b.functor ⋙ R) (p : F ⊣ R)
    (N : C') (E : D') :
    (F'.obj N ⟶ E) ≃ (N ⟶ R'.obj E) where
  toFun k := a.functor.preimage
    (p.homEquiv _ _ (α.hom.app N ≫ b.functor.map k) ≫ β.inv.app E)
  invFun l := b.functor.preimage
    (α.inv.app N ≫ (p.homEquiv _ _).symm (a.functor.map l ≫ β.hom.app E))
  left_inv k := by
    apply b.functor.map_injective
    simp [Category.assoc]
  right_inv l := by
    apply a.functor.map_injective
    simp [Category.assoc]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def transportAdj
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (a : C' ≌ C) (b : D' ≌ D)
    (F : C ⥤ D) (R : D ⥤ C) (F' : C' ⥤ D') (R' : D' ⥤ C')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (β : R' ⋙ a.functor ≅ b.functor ⋙ R) (p : F ⊣ R)
    : F' ⊣ R' :=
  Adjunction.mkOfHomEquiv {
    homEquiv := transportHom a b F R F' R' α β p
    homEquiv_naturality_left_symm := by
      intro N' N E f g
      apply b.functor.map_injective
      dsimp only [transportHom, Equiv.symm_mk, Equiv.coe_fn_mk]
      simp only [CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_comp]
      rw [Category.assoc, p.homEquiv_naturality_left_symm]
      simp only [← Category.assoc]
      exact congrArg (fun k => k ≫ _) (α.inv.naturality f).symm
    homEquiv_naturality_right := by
      intro N E E' f g
      apply a.functor.map_injective
      dsimp only [transportHom, Equiv.coe_fn_mk]
      simp only [CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_comp]
      rw [← Category.assoc, p.homEquiv_naturality_right]
      simp only [Category.assoc]
      exact congrArg (fun k => _ ≫ k) (β.inv.naturality g) }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transportAdj_map
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (a : C' ≌ C) (b : D' ≌ D)
    (F : C ⥤ D) (R : D ⥤ C) (F' : C' ⥤ D') (R' : D' ⥤ C')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (β : R' ⋙ a.functor ≅ b.functor ⋙ R) (p : F ⊣ R)
    (N : C') (E : D') (k : F'.obj N ⟶ E) :
    a.functor.map ((transportAdj a b F R F' R' α β p).homEquiv N E k) =
      p.homEquiv _ _ (α.hom.app N ≫ b.functor.map k) ≫ β.inv.app E := by
  simp [transportAdj, transportHom]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transportAdj_counit
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (a : C' ≌ C) (b : D' ≌ D)
    (F : C ⥤ D) (R : D ⥤ C) (F' : C' ⥤ D') (R' : D' ⥤ C')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (β : R' ⋙ a.functor ≅ b.functor ⋙ R) (p : F ⊣ R)
    (E : D') :
    α.hom.app (R'.obj E) ≫
      b.functor.map ((transportAdj a b F R F' R' α β p).counit.app E) =
        F.map (β.hom.app E) ≫ p.counit.app (b.functor.obj E) := by
  have h := transportAdj_map a b F R F' R' α β p (R'.obj E) E
    ((transportAdj a b F R F' R' α β p).counit.app E)
  have hq : (transportAdj a b F R F' R' α β p).homEquiv (R'.obj E) E
      ((transportAdj a b F R F' R' α β p).counit.app E) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id]
    rw [Equiv.apply_symm_apply]
  rw [hq, CategoryTheory.Functor.map_id] at h
  have h' : p.homEquiv _ _ (α.hom.app (R'.obj E) ≫
      b.functor.map ((transportAdj a b F R F' R' α β p).counit.app E)) =
      β.hom.app E := by
    have hc := congrArg (fun k => k ≫ β.hom.app E) h
    simpa [Category.assoc] using hc.symm
  rw [← Equiv.eq_symm_apply] at h'
  simpa [Adjunction.homEquiv_counit] using h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def transportTensorOver
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (a : C' ≌ C) (b : D' ≌ D) (F : C ⥤ D) (F' : C' ⥤ D')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (τa : tensor C' ⋙ a.functor ≅ a.functor.prod a.functor ⋙ tensor C)
    (τb : tensor D' ⋙ b.functor ≅ b.functor.prod b.functor ⋙ tensor D)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    :
    (tensor C' ⋙ F') ⋙ b.functor ≅ (F'.prod F' ⋙ tensor D') ⋙ b.functor :=
  CategoryTheory.Functor.isoWhiskerLeft (tensor C') α.symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight τa F ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (a.functor.prod a.functor) t ≪≫
    CategoryTheory.Functor.isoWhiskerRight (NatIso.prod α α) (tensor D) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (F'.prod F') τb.symm
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def transportTensor
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (a : C' ≌ C) (b : D' ≌ D) (F : C ⥤ D) (F' : C' ⥤ D')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (τa : tensor C' ⋙ a.functor ≅ a.functor.prod a.functor ⋙ tensor C)
    (τb : tensor D' ⋙ b.functor ≅ b.functor.prod b.functor ⋙ tensor D)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    : tensor C' ⋙ F' ≅ F'.prod F' ⋙ tensor D' :=
  CategoryTheory.Functor.fullyFaithfulCancelRight b.functor
    (transportTensorOver a b F F' α τa τb t)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transportTensor_map
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (a : C' ≌ C) (b : D' ≌ D) (F : C ⥤ D) (F' : C' ⥤ D')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (τa : tensor C' ⋙ a.functor ≅ a.functor.prod a.functor ⋙ tensor C)
    (τb : tensor D' ⋙ b.functor ≅ b.functor.prod b.functor ⋙ tensor D)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (N K : C') :
    b.functor.map ((transportTensor a b F F' α τa τb t).hom.app (N,K)) =
      α.inv.app (N ⊗ K) ≫ F.map (τa.hom.app (N,K)) ≫
        t.hom.app (a.functor.obj N,a.functor.obj K) ≫
          (α.hom.app N ⊗ₘ α.hom.app K) ≫ τb.inv.app (F'.obj N,F'.obj K) := by
  simp [transportTensor, transportTensorOver,
    CategoryTheory.Functor.fullyFaithfulCancelRight_hom_app]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def mate
    {C : Type*} {D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) (p : F ⊣ R)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (M : C) (L : D) : M ⊗ R.obj L ⟶ R.obj (F.obj M ⊗ L) :=
  p.homEquiv _ _ (t.hom.app (M,R.obj L) ≫ (𝟙 (F.obj M) ⊗ₘ p.counit.app L))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_naturality
    {C : Type*} {D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) (p : F ⊣ R)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    {M M' : C} {L L' : D} (m : M ⟶ M') (l : L ⟶ L') :
    (m ⊗ₘ R.map l) ≫ mate F R p t M' L' =
      mate F R p t M L ≫ R.map (F.map m ⊗ₘ l) := by
  dsimp only [mate]
  rw [← p.homEquiv_naturality_left, ← p.homEquiv_naturality_right]
  apply congrArg (p.homEquiv _ _)
  have ht := t.hom.naturality ((m, R.map l) : (M,R.obj L) ⟶ (M',R.obj L'))
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map, tensor_map] at ht
  rw [← Category.assoc, ht]
  dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.prod_obj, tensor_obj]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id,
    Category.id_comp]
  erw [p.counit.naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transport_mate_square
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (a : C' ≌ C) (b : D' ≌ D)
    (F : C ⥤ D) (R : D ⥤ C) (F' : C' ⥤ D') (R' : D' ⥤ C')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (β : R' ⋙ a.functor ≅ b.functor ⋙ R) (p : F ⊣ R)
    (τa : tensor C' ⋙ a.functor ≅ a.functor.prod a.functor ⋙ tensor C)
    (τb : tensor D' ⋙ b.functor ≅ b.functor.prod b.functor ⋙ tensor D)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (N : C') (E : D') :
    (τa.hom.app (N,R'.obj E) ≫ (𝟙 (a.functor.obj N) ⊗ₘ β.hom.app E)) ≫
        mate F R p t (a.functor.obj N) (b.functor.obj E) =
      a.functor.map (mate F' R' (transportAdj a b F R F' R' α β p)
        (transportTensor a b F F' α τa τb t) N E) ≫
        β.hom.app (F'.obj N ⊗ E) ≫
          R.map (τb.hom.app (F'.obj N,E)) ≫
            R.map (α.inv.app N ⊗ₘ 𝟙 (b.functor.obj E)) := by
  dsimp only [mate]
  rw [transportAdj_map]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← R.map_comp, ← p.homEquiv_naturality_right]
  erw [← p.homEquiv_naturality_left (𝟙 (a.functor.obj N) ⊗ₘ β.hom.app E)]
  erw [← p.homEquiv_naturality_left (τa.hom.app (N,R'.obj E))]
  apply congrArg (p.homEquiv (a.functor.obj (N ⊗ R'.obj E))
    (F.obj (a.functor.obj N) ⊗ b.functor.obj E))
  simp only [Category.assoc, transportTensor_map,
    Iso.hom_inv_id_app_assoc]
  have hb := τb.hom.naturality_assoc
    ((𝟙 (F'.obj N), (transportAdj a b F R F' R' α β p).counit.app E) :
      (F'.obj N, F'.obj (R'.obj E)) ⟶ (F'.obj N, E))
    (α.inv.app N ⊗ₘ 𝟙 (b.functor.obj E))
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map, tensor_map] at hb
  simp only [CategoryTheory.Functor.map_id] at hb
  erw [hb]
  simp only [Iso.inv_hom_id_app_assoc, tensorHom_comp_tensorHom]
  dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.prod_obj, tensor_obj]
  simp only [Category.comp_id, Category.id_comp, Iso.hom_inv_id_app]
  erw [transportAdj_counit]
  have ht := t.hom.naturality_assoc
    ((𝟙 (a.functor.obj N), β.hom.app E) :
      (a.functor.obj N, a.functor.obj (R'.obj E)) ⟶
        (a.functor.obj N, R.obj (b.functor.obj E)))
    (𝟙 (F.obj (a.functor.obj N)) ⊗ₘ p.counit.app (b.functor.obj E))
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map, tensor_map] at ht
  simp only [CategoryTheory.Functor.map_id, tensorHom_comp_tensorHom] at ht
  erw [ht]
  dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.prod_obj, tensor_obj]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def transportMateIso
    {C : Type*} {D : Type*} {C' : Type*} {D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (a : C' ≌ C) (b : D' ≌ D)
    (F : C ⥤ D) (R : D ⥤ C) (F' : C' ⥤ D') (R' : D' ⥤ C')
    (α : a.functor ⋙ F ≅ F' ⋙ b.functor)
    (β : R' ⋙ a.functor ≅ b.functor ⋙ R) (p : F ⊣ R)
    (τa : tensor C' ⋙ a.functor ≅ a.functor.prod a.functor ⋙ tensor C)
    (τb : tensor D' ⋙ b.functor ≅ b.functor.prod b.functor ⋙ tensor D)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (N : C') (E : D') :
    Arrow.mk (a.functor.map (mate F' R' (transportAdj a b F R F' R' α β p)
      (transportTensor a b F F' α τa τb t) N E)) ≅
      Arrow.mk (mate F R p t (a.functor.obj N) (b.functor.obj E)) :=
  Arrow.isoMk
    (τa.app (N,R'.obj E) ≪≫ (Iso.refl _ ⊗ᵢ β.app E))
    (β.app (F'.obj N ⊗ E) ≪≫ R.mapIso (τb.app (F'.obj N,E)) ≪≫
      R.mapIso ((α.app N).symm ⊗ᵢ Iso.refl _))
    (by simpa [Category.assoc] using
      transport_mate_square a b F R F' R' α β p τa τb t N E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def mateCongrIso
    {C : Type*} {D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) (p : F ⊣ R)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    {M M' : C} {L L' : D}
    (m : M ≅ M') (l : L ≅ L') :
    Arrow.mk (mate F R p t M L) ≅ Arrow.mk (mate F R p t M' L') :=
  Arrow.isoMk (m ⊗ᵢ R.mapIso l) (R.mapIso (F.mapIso m ⊗ᵢ l))
    (by simpa using mate_naturality F R p t m.hom l.hom)

end ProjectionMateTransport



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A supplied projection mate transports across a commuting square of scheme
isomorphisms, without any invertibility assumption on that mate.
Source: Stacks Project, perfect.tex, Tag 08EU, first sentence of its proof;
the scheme-isomorphism comparison part of the parent transport argument.
(blueprint: lem-pc-projection-mate-scheme-iso-transport).

Proof: Use exists_scheme_iso_derived_equivalence for eY and eX to obtain
exact isomorphism pushforward equivalences a and b with their localization
comparisons. The separate geometric theorem schemeIso_derived_functor_comparisons
supplies binary tensor comparisons τa and τb and natural isomorphisms
α : a followed by Lf* = Lg* followed by b and
β : Rg* followed by a = b followed by Rf*.

Construct q by transporting p's Hom equivalence through the fully faithful
functors a and b: the image under a of q.homEquiv(k) is
p.homEquiv(α.hom followed by b(k)) followed by β.inv.
Naturality of α and β proves both naturality laws of this Hom equivalence,
so Adjunction.mkOfHomEquiv gives q and its triangle identities. Its counit
satisfies α.hom followed by b(q.counit) = Lf*(β.hom) followed by p.counit.
Construct s after composing with b as the five natural isomorphisms
α.inv, Lf*(τa), t, α tensor α, and τb.inv. Full faithfulness of b lifts
this composite and its inverse to the required natural isomorphism s.

For arbitrary N and E on the primed categories, construct the source comparison
c = τa followed by identity tensor β, and the target comparison
d = β followed by Rf*(τb) followed by Rf*(α.inv tensor identity).
Expand q.homEquiv using its constructed formula and expand b(s) using its
five factors. Cancel α.hom with α.inv and β.inv with β.hom. Naturality of τb
moves b(identity tensor q.counit) past τb. The transported counit formula
then replaces α.hom followed by b(q.counit). Tensor composition and naturality
of t give c.hom followed by the p,t mate = a(the q,s mate) followed by d.hom.
Arrow.isoMk packages this square into an arrow isomorphism.

Take N = a.inverse(M) and E = b.inverse(L), with quasi-coherent cohomology
proved by scheme_iso_derived_inverse_preserves_qcoh. The counits of a and b
identify a(N) with M and b(E) with L. The p,t mate is natural in both
coefficients, by naturality of t, p.counit and p.homEquiv. Applying this
naturality to the two equivalence counits gives a second arrow isomorphism.
Compose the two arrow isomorphisms. The categorical calculation uses only
binary tensor naturality, not coherence of units, boundedness, nonemptiness,
or invertibility of either projection mate. -/
theorem projectionMate_schemeIso_transport
    (X Y X' Y' : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings Y'.toRingedSpace))]
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X' ≅ X) (eY : Y' ≅ Y)
    (hcomm : g ≫ eY.hom = eX.hom ≫ f)
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X) :
    ∃ (e : schemeDerivedCategory Y' ≌ schemeDerivedCategory Y)
      (q : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (s : tensor (schemeDerivedCategory Y') ⋙ derivedPullback g ≅
        (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory X'))
      (N : schemeDerivedQCohCategory Y') (E : schemeDerivedQCohCategory X'),
      Nonempty (Arrow.mk (e.functor.map (q.homEquiv (N.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
        ((derivedPullback g).obj N.obj ⊗ E.obj)
        (s.hom.app (N.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
          (𝟙 ((derivedPullback g).obj N.obj) ⊗ₘ q.counit.app E.obj)))) ≅
      Arrow.mk (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
        ((derivedPullback f).obj M.obj ⊗ L.obj)
        (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
          (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))) := by
  classical
  obtain ⟨a, ⟨ha⟩⟩ := Scheme.exists_scheme_iso_derived_equivalence eY
  obtain ⟨b, ⟨hb⟩⟩ := Scheme.exists_scheme_iso_derived_equivalence eX
  obtain ⟨⟨τa⟩, ⟨τb⟩, ⟨α⟩, ⟨β⟩⟩ :=
    schemeIso_derived_functor_comparisons X Y X' Y' f g eX eY hcomm a b ha hb
  let N : schemeDerivedQCohCategory Y' := ⟨a.inverse.obj M.obj,
    Scheme.scheme_iso_derived_inverse_preserves_qcoh eY a ha M⟩
  let E : schemeDerivedQCohCategory X' := ⟨b.inverse.obj L.obj,
    Scheme.scheme_iso_derived_inverse_preserves_qcoh eX b hb L⟩
  let q := ProjectionMateTransport.transportAdj a b
    (derivedPullback f) (schemeDerivedDirectImage f)
    (derivedPullback g) (schemeDerivedDirectImage g) α β p
  let s := ProjectionMateTransport.transportTensor a b
    (derivedPullback f) (derivedPullback g) α τa τb t
  refine ⟨a, q, s, N, E, ⟨?_⟩⟩
  exact ProjectionMateTransport.transportMateIso a b
    (derivedPullback f) (schemeDerivedDirectImage f)
    (derivedPullback g) (schemeDerivedDirectImage g) α β p τa τb t N.obj E.obj ≪≫
      ProjectionMateTransport.mateCongrIso
        (derivedPullback f) (schemeDerivedDirectImage f) p t
        (a.counitIso.app M.obj) (b.counitIso.app L.obj)

end AlgebraicGeometry
