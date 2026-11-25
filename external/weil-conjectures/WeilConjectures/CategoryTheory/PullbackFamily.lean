/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist

/-!

# Families of pullbacks

Let `P` be a family of functors `P f : D Y ⥤ D X`, indexed by the morphisms `f : X ⟶ Y` of a
category `C`, contravariant up to composition isomorphisms `c f g : P (f ≫ g) ≅ P g ⋙ P f`
satisfying the associativity law (`CategoryTheory.PullbackAssoc`, a pseudofunctor `Cᵒᵖ ⥤ Cat`
without unit). The pullbacks of module objects on the pro-étale sites are such a family.

For a morphism `g : W ⟶ X` intertwining endomorphisms `e_W` and `e_X`, the comparison
`CategoryTheory.pullbackFamilyComparison : P g ⋙ P e_W ≅ P e_X ⋙ P g` transports algebras for
`P e_X` to algebras for `P e_W`. This file proves:

- `CategoryTheory.pullbackFamilyStalkComparison_pullbackFamilyComparison`: for a point `w : S ⟶ W`
  fixed by `e_W` up to an endomorphism `s` of `S` with `τ : P s ≅ 𝟭`, the composition isomorphism
  `P (w ≫ g) F ≅ P w (P g F)` intertwines the two stalk structures;
- `Endofunctor.IsoAlgebra.nonempty_mapOfNatIso_pullback_iso`: a pseudonatural family of
  comparisons `θ f : H Y ⋙ P f ≅ L f ⋙ H X` between two families of pullbacks
  (`CategoryTheory.PullbackPseudonatural`) is compatible with the transport of algebras along
  pullbacks;
- `CategoryTheory.PullbackPseudonatural.lifted`: pseudonaturality is preserved by restriction along
  fully faithful functors.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Over

/-- An equation `a ≫ b = c ≫ d` in `Over T` holds for the underlying morphisms. -/
lemma left_comp_left_eq_of_comp_eq {S : Type*} [Category S] {T : S} {A B C D : Over T}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) :
    a.left ≫ b.left = c.left ≫ d.left := by
  rw [← Over.comp_left, h, Over.comp_left]

end CategoryTheory.Over

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : C → Type*} [∀ X, Category (D X)]
  (P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X)
  (c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)

/-- The associativity law of the composition isomorphisms `c f g : P (f ≫ g) ≅ P g ⋙ P f` of a
family of pullbacks. -/
def PullbackAssoc : Prop :=
  ∀ {X Y Z V : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V),
    c f (g ≫ h) ≪≫ Functor.isoWhiskerRight (c g h) (P f) ≪≫ (P h).associator (P g) (P f) =
      eqToIso (congrArg (fun x ↦ P x) (Category.assoc f g h).symm) ≪≫ c (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (P h) (c f g)

variable {P c}

/-- The associativity law of a family of pullbacks, at an object. -/
lemma PullbackAssoc.hom_app (hc : PullbackAssoc P c) {X Y Z V : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ V) (M : D V) :
    (c (f ≫ g) h).hom.app M ≫ (c f g).hom.app ((P h).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (c f (g ≫ h)).hom.app M ≫
        (P f).map ((c g h).hom.app M) := by
  have := congrArg (fun e ↦ e.hom.app M) (hc f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id, eqToIso.hom, eqToHom_app] at this
  rw [this, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The associativity law, solved for `c f (g ≫ h)` followed by `P f (c g h)`. -/
@[reassoc]
lemma PullbackAssoc.hom_app_comp_map_hom_app (hc : PullbackAssoc P c) {X Y Z V : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Z ⟶ V) (M : D V) :
    (c f (g ≫ h)).hom.app M ≫ (P f).map ((c g h).hom.app M) =
      eqToHom (by rw [Category.assoc]) ≫ (c (f ≫ g) h).hom.app M ≫
        (c f g).hom.app ((P h).obj M) := by
  rw [hc.hom_app f g h M, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

section Transport

variable {X Y Z : C}

include c in
/-- Transport of the composition isomorphism along an equation of its first morphism. -/
@[reassoc]
lemma pullbackComp_hom_app_comp_eqToHom_left {f f' : X ⟶ Y} (h : f = f') (g : Y ⟶ Z)
    (M : D Z) :
    (c f g).hom.app M ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (c f' g).hom.app M := by
  subst h
  simp

include c in
/-- Transport of the composition isomorphism along an equation of its second morphism. -/
@[reassoc]
lemma pullbackComp_hom_app_comp_eqToHom_right {g g' : Y ⟶ Z} (f : X ⟶ Y) (h : g = g')
    (M : D Z) :
    (c f g).hom.app M ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (c f g').hom.app M := by
  subst h
  simp

/-- Transport of the image of a morphism along an equation of morphisms. -/
@[reassoc]
lemma map_comp_eqToHom_of_eq {f f' : X ⟶ Y} (h : f = f') {M N : D Y} (u : M ⟶ N) :
    (P f).map u ≫ eqToHom (by rw [h]) = eqToHom (by rw [h]) ≫ (P f').map u := by
  subst h
  simp

end Transport

/-- The comparison `P g ⋙ P e_W ≅ P e_X ⋙ P g` for a morphism `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X`: the composite of the composition isomorphisms and the transport along
`e_W ≫ g = g ≫ e_X`. -/
def pullbackFamilyComparison {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X)
    (hg : eW ≫ g = g ≫ eX) : P g ⋙ P eW ≅ P eX ⋙ P g :=
  (c eW g).symm ≪≫ eqToIso (congrArg (fun f ↦ P f) hg) ≪≫ c g eX

lemma pullbackFamilyComparison_hom_app {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X)
    (hg : eW ≫ g = g ≫ eX) (M : D X) :
    (pullbackFamilyComparison (c := c) g eW eX hg).hom.app M =
      (c eW g).inv.app M ≫ eqToHom (by rw [hg]) ≫ (c g eX).hom.app M := by
  simp [pullbackFamilyComparison, eqToHom_app]

section Stalk

variable {S : C} {s : S ⟶ S}

/-- The stalk comparison `P x ≅ P e ⋙ P x` at a point `x : S ⟶ V` fixed by `e : V ⟶ V` up to an
endomorphism `s` of `S` with `τ : P s ≅ 𝟭` (`x ≫ e = s ≫ x`): the composite
`P x ≅ P x ⋙ P s ≅ P (s ≫ x) = P (x ≫ e) ≅ P e ⋙ P x`. -/
def pullbackFamilyStalkComparison (τ : P s ≅ 𝟭 (D S)) {V : C} (x : S ⟶ V) (e : V ⟶ V)
    (h : x ≫ e = s ≫ x) :
    P x ⋙ 𝟭 (D S) ≅ P e ⋙ P x :=
  Functor.isoWhiskerLeft _ τ.symm ≪≫ (c s x).symm ≪≫ eqToIso (congrArg (fun f ↦ P f) h.symm) ≪≫
    c x e

lemma pullbackFamilyStalkComparison_hom_app (τ : P s ≅ 𝟭 (D S)) {V : C} (x : S ⟶ V) (e : V ⟶ V)
    (h : x ≫ e = s ≫ x) (M : D V) :
    (pullbackFamilyStalkComparison (c := c) τ x e h).hom.app M =
      τ.inv.app ((P x).obj M) ≫ (c s x).inv.app M ≫ eqToHom (by rw [h]) ≫ (c x e).hom.app M := by
  simp [pullbackFamilyStalkComparison, eqToHom_app]

/-- **Stalks of a pullback**: for `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`, an object `F` of `D X`
with `φ : P e_X F ≅ F` and a point `w : S ⟶ W` with `w ≫ e_W = s ≫ w`, the composition
isomorphism `P w (P g F) ≅ P (w ≫ g) F` intertwines the stalk structure of the pullback
`(P g F, pullbackFamilyComparison ≫ P g φ)` at `w` with the stalk structure of `(F, φ)` at `w ≫ g`.
-/
theorem pullbackFamilyStalkComparison_pullbackFamilyComparison (hc : PullbackAssoc P c)
    (τ : P s ≅ 𝟭 (D S))
    {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X) (hg : eW ≫ g = g ≫ eX) {F : D X}
    (φ : (P eX).obj F ≅ F) (w : S ⟶ W) (hw : w ≫ eW = s ≫ w)
    (hwg : (w ≫ g) ≫ eX = s ≫ (w ≫ g)) :
    (pullbackFamilyStalkComparison (c := c) τ w eW hw).hom.app ((P g).obj F) ≫
        (P w).map ((pullbackFamilyComparison (c := c) g eW eX hg).hom.app F ≫ (P g).map φ.hom) ≫
        (c w g).inv.app F =
      (c w g).inv.app F ≫ (pullbackFamilyStalkComparison (c := c) τ (w ≫ g) eX hwg).hom.app F ≫
        (P (w ≫ g)).map φ.hom := by
  have nat₁ := (c w g).inv.naturality φ.hom
  have nat₂ := τ.inv.naturality ((c w g).inv.app F)
  simp only [Functor.comp_map, Functor.id_map] at nat₁ nat₂
  simp only [pullbackFamilyStalkComparison_hom_app, pullbackFamilyComparison_hom_app,
    Functor.map_comp,
    Category.assoc]
  rw [nat₁, reassoc_of% nat₂]
  refine congrArg (τ.inv.app _ ≫ ·) ?_
  simp only [← Category.assoc]
  refine congrArg (· ≫ (P (w ≫ g)).map φ.hom) ?_
  simp only [Category.assoc]
  rw [← cancel_epi ((c (s ≫ w) g).hom.app F ≫ (c s w).hom.app ((P g).obj F))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have k₁ : (P s).map ((c w g).hom.app F) ≫ (P s).map ((c w g).inv.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  have k₂ : (P w).map ((c eW g).hom.app F) ≫ (P w).map ((c eW g).inv.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rw [reassoc_of% (hc.hom_app s w g F), reassoc_of% k₁, Iso.hom_inv_id_app_assoc,
    pullbackComp_hom_app_comp_eqToHom_left_assoc (c := c) hw.symm,
    reassoc_of% (hc.hom_app w eW g F), reassoc_of% k₂, eqToHom_map,
    pullbackComp_hom_app_comp_eqToHom_right_assoc (c := c) w hg,
    hc.hom_app_comp_map_hom_app_assoc, Iso.hom_inv_id_app, Category.comp_id]
  simp only [eqToHom_trans_assoc]

/-- `pullbackFamilyStalkComparison_pullbackFamilyComparison`, for a structure isomorphism `ψ` of
the pullback given through its underlying morphism, bracketed as the condition on a
morphism of algebras. -/
theorem pullbackFamilyStalkComparison_pullbackFamilyComparison' (hc : PullbackAssoc P c)
    (τ : P s ≅ 𝟭 (D S))
    {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X) (hg : eW ≫ g = g ≫ eX) {F : D X}
    (φ : (P eX).obj F ≅ F) (ψ : (P eW).obj ((P g).obj F) ⟶ (P g).obj F)
    (hψ : ψ = (pullbackFamilyComparison (c := c) g eW eX hg).hom.app F ≫ (P g).map φ.hom)
    (w : S ⟶ W) (hw : w ≫ eW = s ≫ w) (hwg : (w ≫ g) ≫ eX = s ≫ (w ≫ g)) :
    (c w g).inv.app F ≫ ((pullbackFamilyStalkComparison (c := c) τ (w ≫ g) eX hwg).hom.app F ≫
        (P (w ≫ g)).map φ.hom) =
      ((pullbackFamilyStalkComparison (c := c) τ w eW hw).hom.app ((P g).obj F) ≫ (P w).map ψ) ≫
        (c w g).inv.app F := by
  rw [hψ, Category.assoc]
  exact (pullbackFamilyStalkComparison_pullbackFamilyComparison hc τ g eW eX hg φ w hw hwg).symm

end Stalk

end CategoryTheory

/-! ### Pseudonatural comparisons between two families of pullbacks -/

namespace CategoryTheory

section Pseudonatural

variable {C : Type*} [Category C] {D E : C → Type*} [∀ X, Category (D X)] [∀ X, Category (E X)]
  {P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X}
  {c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f}
  {L : ∀ {X Y : C}, (X ⟶ Y) → E Y ⥤ E X}
  {Lc : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), L (f ≫ g) ≅ L g ⋙ L f}
  {H : ∀ X : C, E X ⥤ D X}

variable (c Lc) in
/-- A family of comparisons `θ f : H Y ⋙ P f ≅ L f ⋙ H X` between two families of pullbacks is
*pseudonatural* if it is compatible with the composition isomorphisms. -/
def PullbackPseudonatural (θ : ∀ {X Y : C} (f : X ⟶ Y), H Y ⋙ P f ≅ L f ⋙ H X) : Prop :=
  ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    Functor.isoWhiskerLeft (H Z) (c f g) ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (θ g) (P f) ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (L g) (θ f) =
      θ (f ≫ g) ≪≫ Functor.isoWhiskerRight (Lc f g) (H X) ≪≫ Functor.associator _ _ _

variable {θ : ∀ {X Y : C} (f : X ⟶ Y), H Y ⋙ P f ≅ L f ⋙ H X}

/-- Pseudonaturality, at an object. -/
lemma PullbackPseudonatural.hom_app (hθ : PullbackPseudonatural c Lc θ) {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : E Z) :
    (c f g).hom.app ((H Z).obj K) ≫ (P f).map ((θ g).hom.app K) ≫ (θ f).hom.app ((L g).obj K) =
      (θ (f ≫ g)).hom.app K ≫ (H X).map ((Lc f g).hom.app K) := by
  have := congrArg (fun e ↦ e.hom.app K) (hθ f g)
  simpa using this

/-- Pseudonaturality can be checked at objects. -/
lemma PullbackPseudonatural.of_hom_app
    (h : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (K : E Z),
      (c f g).hom.app ((H Z).obj K) ≫ (P f).map ((θ g).hom.app K) ≫ (θ f).hom.app ((L g).obj K) =
        (θ (f ≫ g)).hom.app K ≫ (H X).map ((Lc f g).hom.app K)) :
    PullbackPseudonatural c Lc θ := by
  intro X Y Z f g
  ext K
  simpa using h f g K

/-- Transport of the comparison along an equation of morphisms. -/
@[reassoc]
lemma pullbackPseudonatural_eqToHom {X Y : C} {f f' : X ⟶ Y} (h : f = f') (K : E Y) :
    eqToHom (by rw [h]) ≫ (θ f').hom.app K = (θ f).hom.app K ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The comparison square of a pseudonatural family along `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X`. -/
lemma PullbackPseudonatural.pullbackFamilyComparison (hθ : PullbackPseudonatural c Lc θ) {W X : C}
    (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X) (hg : eW ≫ g = g ≫ eX) (K : E X) :
    (pullbackFamilyComparison (c := c) g eW eX hg).hom.app ((H X).obj K) ≫
        (P g).map ((θ eX).hom.app K) ≫ (θ g).hom.app ((L eX).obj K) =
      (P eW).map ((θ g).hom.app K) ≫ (θ eW).hom.app ((L g).obj K) ≫
        (H W).map ((pullbackFamilyComparison (c := Lc) g eW eX hg).hom.app K) := by
  simp only [pullbackFamilyComparison_hom_app, Category.assoc, Functor.map_comp]
  rw [hθ.hom_app g eX K, ← Category.assoc ((P eW).map _), ← Category.assoc,
    ← cancel_epi ((c eW g).hom.app ((H X).obj K))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (hθ.hom_app eW g K)]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, eqToHom_map]
  rw [pullbackPseudonatural_eqToHom_assoc (θ := θ) hg]

/-- **The comparison of a pseudonatural family transports Weil structures compatibly with
pullbacks**: for `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X` and an algebra `K` for `L e_X`, the
comparison `θ g` is an isomorphism between the transport along `θ e_W` of the pullback of `K`
and the pullback of the transport of `K` along `θ e_X`. The functors are given through
equations, so that concrete instances can use their own functors.

Implementation note: the categories are passed as variables, with their category instances, together
with `Sigma`-type equations to the generic ones, and the functors through `HEq` hypotheses. This
works around elaboration problems: instantiated directly with the pullbacks of module objects,
the generic statement makes the elaborator and the kernel unfold these pullbacks while comparing
the instances of the generic categories with the concrete ones. Concrete callers pass their own
categories and functors, together with `rfl` and functor-level equations. -/
theorem Endofunctor.IsoAlgebra.nonempty_mapOfNatIso_pullback_iso (hθ : PullbackPseudonatural c Lc θ)
    {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X) (hg : eW ≫ g = g ≫ eX)
    (𝒦X 𝒦W 𝒮X 𝒮W : Type _) {i𝒦X : Category 𝒦X} {i𝒦W : Category 𝒦W} {i𝒮X : Category 𝒮X}
    {i𝒮W : Category 𝒮W} (A₁ : 𝒦X ⥤ 𝒮X) (B₁ : 𝒦X ⥤ 𝒦W) (A₂ : 𝒦W ⥤ 𝒮W) (B₂ : 𝒮X ⥤ 𝒮W)
    (K : 𝒦X)
    (h𝒦X : (⟨𝒦X, i𝒦X⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (L eX), inferInstance⟩)
    (h𝒦W : (⟨𝒦W, i𝒦W⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (L eW), inferInstance⟩)
    (h𝒮X : (⟨𝒮X, i𝒮X⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eX), inferInstance⟩)
    (h𝒮W : (⟨𝒮W, i𝒮W⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eW), inferInstance⟩)
    (hA₁ : HEq A₁ (Endofunctor.IsoAlgebra.mapOfNatIso (θ eX)))
    (hB₁ : HEq B₁ (Endofunctor.IsoAlgebra.mapOfNatIso
      (pullbackFamilyComparison (c := Lc) g eW eX hg)))
    (hA₂ : HEq A₂ (Endofunctor.IsoAlgebra.mapOfNatIso (θ eW)))
    (hB₂ : HEq B₂ (Endofunctor.IsoAlgebra.mapOfNatIso
      (pullbackFamilyComparison (c := c) g eW eX hg))) :
    Nonempty (A₂.obj (B₁.obj K) ≅ B₂.obj (A₁.obj K)) := by
  cases h𝒦X
  cases h𝒦W
  cases h𝒮X
  cases h𝒮W
  cases hA₁
  cases hB₁
  cases hA₂
  cases hB₂
  refine ⟨Endofunctor.IsoAlgebra.isoMk ((θ g).app K.carrier).symm ?_⟩
  change (P eW).map ((θ g).inv.app K.carrier) ≫
      ((pullbackFamilyComparison (c := c) g eW eX hg).hom.app ((H X).obj K.carrier) ≫
        (P g).map ((θ eX).hom.app K.carrier ≫ (H X).map K.str.hom)) =
    ((θ eW).hom.app ((L g).obj K.carrier) ≫
      (H W).map ((pullbackFamilyComparison (c := Lc) g eW eX hg).hom.app K.carrier ≫
        (L g).map K.str.hom)) ≫ (θ g).inv.app K.carrier
  have nat := (θ g).inv.naturality K.str.hom
  simp only [Functor.comp_map] at nat
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, nat,
    ← cancel_epi ((P eW).map ((θ g).hom.app K.carrier)), ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  rw [← cancel_mono ((θ g).hom.app ((L eX).obj K.carrier))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact (hθ.pullbackFamilyComparison g eW eX hg K.carrier).trans (by erw [Category.comp_id])

section Restriction

variable {T : C} {Q : ObjectProperty (Over T)} {E' : Q.FullSubcategory → Type*}
  [∀ V, Category (E' V)] (ι : ∀ V : Q.FullSubcategory, E' V ⥤ E V.obj.left)
  (hι : ∀ V : Q.FullSubcategory, (ι V).FullyFaithful)
  (L' : ∀ {V W : Q.FullSubcategory}, (V ⟶ W) → E' W ⥤ E' V)
  (κ : ∀ {V W : Q.FullSubcategory} (f : V ⟶ W), L' f ⋙ ι V ≅ ι W ⋙ L f.hom.left)

variable (Lc) in
/-- The composition isomorphisms of a family of pullbacks lifted along fully faithful functors
`ι V : E' V ⥤ E V.obj.left`. -/
noncomputable def liftedPullbackComp {X Y Z : Q.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    L' (f ≫ g) ≅ L' g ⋙ L' f :=
  ((hι X).whiskeringRight _).preimageIso
    (κ (f ≫ g) ≪≫ Functor.isoWhiskerLeft _ (Lc f.hom.left g.hom.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (κ g).symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (κ f).symm ≪≫ (Functor.associator _ _ _).symm)

variable (θ) in
/-- The comparisons of a pseudonatural family restricted along the functors `ι V`. -/
noncomputable def liftedComparison {V W : Q.FullSubcategory} (f : V ⟶ W) :
    (ι W ⋙ H W.obj.left) ⋙ P f.hom.left ≅ L' f ⋙ (ι V ⋙ H V.obj.left) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (θ f.hom.left) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (κ f).symm _ ≪≫
    Functor.associator _ _ _

/-- The restriction of a pseudonatural family along fully faithful functors is pseudonatural. -/
theorem PullbackPseudonatural.lifted (hθ : PullbackPseudonatural c Lc θ) :
    PullbackPseudonatural (C := Q.FullSubcategory) (D := fun V ↦ D V.obj.left) (E := E')
      (P := fun {X Y : Q.FullSubcategory} (f : X ⟶ Y) ↦ P f.hom.left)
      (fun {X Y Z : Q.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) ↦ c f.hom.left g.hom.left)
      (fun {X Y Z : Q.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
        liftedPullbackComp Lc ι hι L' κ f g)
      (H := fun V ↦ ι V ⋙ H V.obj.left) (liftedComparison θ ι L' κ) := by
  intro X Y Z f g
  ext K
  have hp : (ι X).map ((liftedPullbackComp Lc ι hι L' κ f g).hom.app K) =
      (κ (f ≫ g)).hom.app K ≫ (Lc f.hom.left g.hom.left).hom.app ((ι Z).obj K) ≫
        (L f.hom.left).map ((κ g).inv.app K) ≫ (κ f).inv.app ((L' g).obj K) := by
    have := congrArg (fun α ↦ α.app K)
      (((hι X).whiskeringRight (E' Z)).map_preimage
        (κ (f ≫ g) ≪≫ Functor.isoWhiskerLeft _ (Lc f.hom.left g.hom.left) ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (κ g).symm _ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (κ f).symm ≪≫
          (Functor.associator _ _ _).symm).hom)
    set_option linter.unnecessarySimpa false in simpa [liftedPullbackComp] using this
  have h := hθ.hom_app f.hom.left g.hom.left ((ι Z).obj K)
  have n₁ := (θ f.hom.left).hom.naturality ((κ g).inv.app K)
  simp only [Functor.comp_map] at n₁
  simp only [liftedComparison, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc, hp, Iso.symm_hom]
  rw [← Functor.map_comp_assoc (H X.obj.left) ((κ (f ≫ g)).inv.app K), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% n₁, reassoc_of% h]
  rfl

end Restriction

end Pseudonatural

end CategoryTheory
