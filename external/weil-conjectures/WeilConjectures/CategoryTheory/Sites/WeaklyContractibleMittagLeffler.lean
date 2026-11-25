/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitMittagLeffler
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts

/-!
# Mittag-Leffler towers of sheaves on sites with enough weakly contractible objects

If every object of a site is covered by weakly contractible objects, then `R¹lim` vanishes for
a tower `F` of sheaves of modules whose section modules over every weakly contractible object
form a Mittag-Leffler tower, in the form that `1 - t` is an epimorphism on `∏ Fₙ` (blueprint
`proposition-milnor-sequence`, last paragraph; Stacks 0947, 07KW). This holds in particular when the
tower of sheaves itself is Mittag-Leffler in the sense that the image subobjects of the
transition maps `Fₖ ⟶ Fₙ` stabilise: over a weakly contractible object, sections of the image
of a morphism are the image of its sections.

## Main results

- `CategoryTheory.GrothendieckTopology.epi_one_sub_of_forall_mittagLeffler`: Mittag-Leffler on
  weakly contractible sections implies that `1 - t` is an epimorphism.
- `CategoryTheory.GrothendieckTopology.range_app_le_of_imageSubobject_le`: over a weakly
  contractible object, an inclusion of image subobjects gives an inclusion of the images of
  sections.
- `CategoryTheory.GrothendieckTopology.epi_one_sub_of_mittagLeffler_imageSubobject`: the
  Mittag-Leffler condition on image subobjects implies that `1 - t` is an epimorphism.
- `CategoryTheory.GrothendieckTopology.epi_one_sub_of_forall_finite`: the same when the
  sections over weakly contractible objects are finite.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [Ring R]
  [HasSheafify J (ModuleCat.{w} R)] [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))] (P : C → Prop)
  (hP : ∀ V : C, ∃ (ι : Type w') (W : ι → C) (f : ∀ i, W i ⟶ V),
    (∀ i, P (W i)) ∧ Sieve.ofArrows W f ∈ J V)
  (hPW : ∀ W, P W → J.IsWeaklyContractible.{w} W)

include hP hPW in
/-- **Mittag-Leffler on weakly contractible sections kills `R¹lim`** (blueprint
`proposition-milnor-sequence`, Stacks 0947, 07KW). If every object of the site is covered by weakly
contractible objects satisfying `P`, and over every such `W` the tower of section modules
`Fₙ(W)` is Mittag-Leffler, then the map `1 - t` on a product `∏ Fₙ` is an epimorphism, where
`t` has components `∏ Fₘ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
lemma epi_one_sub_of_forall_mittagLeffler {F : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R)}
    {Pf : Fan fun n : ℕ ↦ F.obj (op n)} (hPf : IsLimit Pf) (t : Pf.pt ⟶ Pf.pt)
    (ht : ∀ n : ℕ, t ≫ Pf.proj n = Pf.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hML : ∀ W, P W → ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      LinearMap.range ((F.map (homOfLE hN).op).hom.app (op W)).hom ≤
        LinearMap.range ((F.map (homOfLE hk).op).hom.app (op W)).hom) :
    Epi (𝟙 Pf.pt - t) := by
  rw [epi_iff_of_forall_exists P hP hPW]
  intro W hW
  let E := sheafToPresheaf J (ModuleCat.{w} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op W)
  have hPf' : IsLimit (Fan.mk Pf.pt Pf.proj) :=
    IsLimit.ofIsoLimit hPf (Cone.ext (Iso.refl _) fun ⟨_⟩ ↦ (Category.id_comp _).symm)
  have := ModuleCat.epi_one_sub_of_mittagLeffler (F := F ⋙ E)
    (isLimitFanMkObjOfIsLimit E _ _ hPf') (E.map t)
    (fun n ↦ by simpa [E] using congrArg E.map (ht n)) (hML W hW)
  change Epi (E.map (𝟙 Pf.pt - t))
  rw [E.map_sub, E.map_id]
  exact this

include hP hPW in
/-- Over a weakly contractible object `W`, sections of the image of a morphism of sheaves of
modules are the image of its sections; hence an inclusion of image subobjects
`im f ≤ im g` gives an inclusion `im f(W) ≤ im g(W)` of images of sections. -/
lemma range_app_le_of_imageSubobject_le {F G H : Sheaf J (ModuleCat.{w} R)} {f : F ⟶ H}
    {g : G ⟶ H} (h : imageSubobject f ≤ imageSubobject g) (W : C) (hW : P W) :
    LinearMap.range (f.hom.app (op W)).hom ≤ LinearMap.range (g.hom.app (op W)).hom := by
  let E := sheafToPresheaf J (ModuleCat.{w} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op W)
  rintro _ ⟨y, rfl⟩
  have hg := (ModuleCat.epi_iff_surjective _).1
    ((epi_iff_of_forall_exists P hP hPW (factorThruImageSubobject g)).1 inferInstance W hW)
  obtain ⟨v, hv⟩ :=
    hg ((E.map (Subobject.ofLE _ _ h)).hom ((E.map (factorThruImageSubobject f)).hom y))
  refine ⟨v, ?_⟩
  have hf : f = (factorThruImageSubobject f ≫ Subobject.ofLE _ _ h) ≫
      (imageSubobject g).arrow := by
    rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  have hf' := congrArg (fun φ ↦ (E.map φ).hom y) hf
  have hg' := congrArg (fun φ ↦ (E.map φ).hom v) (imageSubobject_arrow_comp g)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply] at hf' hg'
  exact hg'.symm.trans ((congrArg (E.map (imageSubobject g).arrow).hom hv).trans hf'.symm)

include hP hPW in
/-- **Mittag-Leffler towers of sheaves have `R¹lim = 0`.** If every object of the site is
covered by weakly contractible objects, and the tower `F` of sheaves of modules is
Mittag-Leffler in the sense that for every `n` there is `N ≥ n` with
`im (F_N ⟶ Fₙ) ≤ im (Fₖ ⟶ Fₙ)` as subobjects for every `k ≥ n`, then the map `1 - t` on a
product `∏ Fₙ` is an epimorphism (Stacks 0947, 07KW). -/
lemma epi_one_sub_of_mittagLeffler_imageSubobject {F : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R)}
    {Pf : Fan fun n : ℕ ↦ F.obj (op n)} (hPf : IsLimit Pf) (t : Pf.pt ⟶ Pf.pt)
    (ht : ∀ n : ℕ, t ≫ Pf.proj n = Pf.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hML : ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject (F.map (homOfLE hN).op) ≤ imageSubobject (F.map (homOfLE hk).op)) :
    Epi (𝟙 Pf.pt - t) :=
  epi_one_sub_of_forall_mittagLeffler P hP hPW hPf t ht fun W hW n ↦ by
    obtain ⟨N, hN, hk⟩ := hML n
    exact ⟨N, hN, fun k hk' ↦ range_app_le_of_imageSubobject_le P hP hPW (hk k hk') W hW⟩

include hP hPW in
/-- **Towers with finite weakly contractible sections have `R¹lim = 0`.** If every object of
the site is covered by weakly contractible objects satisfying `P`, and the section modules
`Fₙ(W)` of the tower `F` over every such `W` are finite, then the map `1 - t` on a product
`∏ Fₙ` is an epimorphism (towers of finite modules are Mittag-Leffler, Stacks 0596). -/
lemma epi_one_sub_of_forall_finite {F : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R)}
    {Pf : Fan fun n : ℕ ↦ F.obj (op n)} (hPf : IsLimit Pf) (t : Pf.pt ⟶ Pf.pt)
    (ht : ∀ n : ℕ, t ≫ Pf.proj n = Pf.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hfin : ∀ W, P W → ∀ n : ℕ, Finite ((F.obj (op n)).obj.obj (op W))) :
    Epi (𝟙 Pf.pt - t) :=
  epi_one_sub_of_forall_mittagLeffler P hP hPW hPf t ht fun W hW ↦
    ModuleCat.mittagLeffler_of_finite
      (F := F ⋙ sheafToPresheaf J _ ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op W)) (hfin W hW)

end CategoryTheory.GrothendieckTopology
