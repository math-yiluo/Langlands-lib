/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# A formalism of pullbacks, pushforwards and extensions by zero

This is the formal structure underlying compactly supported direct images, indexed by an
arbitrary category `𝒞` with a class `𝒪` of morphisms playing the role of the open immersions:
a category for each object of `𝒞`, a pullback pseudofunctor `f ↦ f^*`, right adjoints `f_*` and
left adjoints `j_!` of `j^*` for `j ∈ 𝒪` (`CategoryTheory.ExchangeFormalism`). The formalism
of compactly supported direct images on all schemes, `AlgebraicGeometry.CompactSupportFormalism`,
is the case of the category of schemes with the open immersions; an arbitrary index category
allows coefficient categories, such as bounded constructible complexes, that are only defined
for schemes of finite type over a field.

All the comparison maps of the theory (base change for `j_!`, the exchange `j_! g'_* ⟶ g''_* j'_!`,
the base change of the pushforwards) are mates of the composition isomorphisms of the pullbacks,
and their coherence is formal. This file defines

- `pbComp'`, `pfComp'`, `shComp'`: the flexible composition isomorphisms of `f^*`, `f_*`, `j_!`,
  the last two as conjugates of the first;
- `sqIso`: the isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` of a commutative square;
- `baseChange`: the base change map `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*` for the extension by zero;
- `exchange`: the exchange map `g'_* ⋙ j_! ⟶ j'_! ⋙ g''_*` of a square whose base change map is
  an isomorphism.
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory



set_option linter.checkUnivs false in
/-- **A formalism of pullbacks, pushforwards and extensions by zero** indexed by a category `𝒞`
with a class `𝒪` of morphisms (the open immersions): a category `obj X` for each `X : 𝒞`, a
pullback pseudofunctor `f ↦ pb f`, a right adjoint `pf f` of each `pb f`, and a left adjoint
`sh j` of `pb j` for each `j` in `𝒪`. -/
structure ExchangeFormalism (𝒞 : Type u) [Category.{v} 𝒞] (𝒪 : MorphismProperty 𝒞) where
  /-- The category attached to an object. -/
  obj : 𝒞 → Type w
  /-- The categories attached to the objects. -/
  [category (X : 𝒞) : Category.{v₁} (obj X)]
  /-- The pullback `f^*`. -/
  pb {X Y : 𝒞} (f : X ⟶ Y) : obj Y ⥤ obj X
  /-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭`. -/
  pbId (X : 𝒞) : pb (𝟙 X) ≅ 𝟭 (obj X)
  /-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*`. -/
  pbComp {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) : pb (f ≫ g) ≅ pb g ⋙ pb f
  pbComp_assoc {X Y Z W : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : obj W) :
    (pbComp (f ≫ g) h).hom.app M ≫ (pbComp f g).hom.app ((pb h).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (pbComp f (g ≫ h)).hom.app M ≫
        (pb f).map ((pbComp g h).hom.app M)
  pbId_comp {X Y : 𝒞} (f : X ⟶ Y) (M : obj Y) :
    (pbComp (𝟙 X) f).hom.app M ≫ (pbId X).hom.app ((pb f).obj M) =
      eqToHom (by simp)
  pbComp_id {X Y : 𝒞} (f : X ⟶ Y) (M : obj Y) :
    (pbComp f (𝟙 Y)).hom.app M ≫ (pb f).map ((pbId Y).hom.app M) =
      eqToHom (by simp)
  /-- The pushforward `f_*`. -/
  pf {X Y : 𝒞} (f : X ⟶ Y) : obj X ⥤ obj Y
  /-- The adjunction `f^* ⊣ f_*`. -/
  adj {X Y : 𝒞} (f : X ⟶ Y) : pb f ⊣ pf f
  /-- The extension by zero `j_!` along an open immersion. -/
  sh {X Y : 𝒞} (j : X ⟶ Y) [Fact (𝒪 j)] : obj X ⥤ obj Y
  /-- The adjunction `j_! ⊣ j^*`. -/
  shAdj {X Y : 𝒞} (j : X ⟶ Y) [Fact (𝒪 j)] : sh j ⊣ pb j

namespace ExchangeFormalism

attribute [instance] category

/-- An identity belongs to a class of morphisms containing the identities. -/
instance fact_id_mem {𝒞 : Type u} [Category.{v} 𝒞] (𝒪 : MorphismProperty 𝒞) [𝒪.ContainsIdentities]
    (X : 𝒞) : Fact (𝒪 (𝟙 X)) :=
  ⟨𝒪.id_mem X⟩

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section Pullback

variable {X Y Z W : 𝒞}

/-- The composition isomorphism `h^* ≅ g^* ⋙ f^*` for `f ≫ g = h`. -/
def pbComp' (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    F.pb h ≅ F.pb g ⋙ F.pb f :=
  eqToIso (by rw [w]) ≪≫ F.pbComp f g

@[simp]
lemma pbComp'_rfl (f : X ⟶ Y) (g : Y ⟶ Z) : F.pbComp' f g (f ≫ g) rfl = F.pbComp f g := by
  ext; simp [pbComp']

/-- The isomorphism `f^* ≅ g^*` for `f = g`. -/
def pbCongr {f g : X ⟶ Y} (h : f = g) : F.pb f ≅ F.pb g := eqToIso (by rw [h])

@[simp]
lemma pbCongr_rfl (f : X ⟶ Y) : F.pbCongr (rfl : f = f) = Iso.refl _ := rfl

@[reassoc]
lemma pbComp'_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W)
    (fgh : X ⟶ W) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh)
    (M : F.obj W) :
    (F.pbComp' fg h fgh hfgh).hom.app M ≫ (F.pbComp' f g fg hfg).hom.app ((F.pb h).obj M) =
      (F.pbComp' f gh fgh (by rw [← hfgh, ← hfg, ← hgh, Category.assoc])).hom.app M ≫
        (F.pb f).map ((F.pbComp' g h gh hgh).hom.app M) := by
  subst hfg hgh hfgh
  rw [pbComp'_rfl, pbComp'_rfl, pbComp'_rfl, F.pbComp_assoc]
  simp [pbComp']

@[reassoc]
lemma pbComp'_id_left (f : X ⟶ Y) (f' : X ⟶ Y) (hf : 𝟙 X ≫ f = f') (M : F.obj Y) :
    (F.pbComp' (𝟙 X) f f' hf).hom.app M ≫ (F.pbId X).hom.app ((F.pb f).obj M) =
      eqToHom (by rw [← hf, Category.id_comp]; rfl) := by
  subst hf
  simpa using F.pbId_comp f M

@[reassoc]
lemma pbComp'_id_right (f : X ⟶ Y) (f' : X ⟶ Y) (hf : f ≫ 𝟙 Y = f') (M : F.obj Y) :
    (F.pbComp' f (𝟙 Y) f' hf).hom.app M ≫ (F.pb f).map ((F.pbId Y).hom.app M) =
      eqToHom (by rw [← hf, Category.comp_id]; rfl) := by
  subst hf
  simpa using F.pbComp_id f M

end Pullback


section Pushforward

variable {X Y Z W : 𝒞}

/-- The composition isomorphism `h_* ≅ f_* ⋙ g_*` for `f ≫ g = h`, conjugate to
`ExchangeFormalism.pbComp'`. -/
def pfComp' (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    F.pf h ≅ F.pf f ⋙ F.pf g :=
  conjugateIsoEquiv (F.adj h) ((F.adj g).comp (F.adj f)) (F.pbComp' f g h w).symm

/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭`, conjugate to `ExchangeFormalism.pbId`. -/
def pfId (X : 𝒞) : F.pf (𝟙 X) ≅ 𝟭 (F.obj X) :=
  conjugateIsoEquiv (F.adj (𝟙 X)) Adjunction.id (F.pbId X).symm

end Pushforward

section ExtensionByZero

variable {X Y Z : 𝒞}

/-- The composition isomorphism `j_! ≅ j₁_! ⋙ j₂_!` for open immersions with `j₁ ≫ j₂ = j`,
conjugate to `ExchangeFormalism.pbComp'`. -/
def shComp' (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) (j : X ⟶ Z) [Fact (𝒪 j₁)] [Fact (𝒪 j₂)]
    [Fact (𝒪 j)] (w : j₁ ≫ j₂ = j) : F.sh j ≅ F.sh j₁ ⋙ F.sh j₂ :=
  (conjugateIsoEquiv ((F.shAdj j₁).comp (F.shAdj j₂)) (F.shAdj j)).symm (F.pbComp' j₁ j₂ j w).symm

/-- The identity isomorphism `(𝟙 X)_! ≅ 𝟭`, conjugate to `ExchangeFormalism.pbId`. -/
def shId (X : 𝒞) [Fact (𝒪 (𝟙 X))] : F.sh (𝟙 X) ≅ 𝟭 (F.obj X) :=
  (conjugateIsoEquiv Adjunction.id (F.shAdj (𝟙 X))).symm (F.pbId X).symm

end ExtensionByZero

section Square

variable {U' U Z' Z : 𝒞}

/-- The isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` attached to a commutative square `t ≫ r = l ≫ b`. -/
def sqIso (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b) :
    F.pb r ⋙ F.pb t ≅ F.pb b ⋙ F.pb l :=
  (F.pbComp' t r (t ≫ r) rfl).symm ≪≫ F.pbComp' l b (t ≫ r) w.symm

/-- **The base change map of the extension by zero**: for a commutative square
`t ≫ r = l ≫ b` with `l` and `r` open immersions, the map `t^* ⋙ l_! ⟶ r_! ⋙ b^*`, i.e.
`l_! t^* ⟶ b^* r_!`, the mate of `ExchangeFormalism.sqIso` under the adjunctions
`r_! ⊣ r^*` and `l_! ⊣ l^*`.
```
U' --t--> U
|l        |r
Z' --b--> Z
```
-/
def baseChange (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [Fact (𝒪 l)]
    [Fact (𝒪 r)] (w : t ≫ r = l ≫ b) :
    TwoSquare (F.pb t) (F.sh r) (F.sh l) (F.pb b) :=
  (mateEquiv (F.shAdj r) (F.shAdj l)).symm (F.sqIso t l r b w).hom

/-- **The exchange map of an extension by zero and a pushforward**: for a commutative square
`t ≫ r = l ≫ b` with `l` and `r` open immersions whose base change map is an isomorphism, the
map `t_* ⋙ r_! ⟶ l_! ⋙ b_*`, i.e. `r_! t_* ⟶ b_* l_!`, the mate of the inverse of
`ExchangeFormalism.baseChange` under the adjunctions `t^* ⊣ t_*` and `b^* ⊣ b_*`.
-/
noncomputable def exchange (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [Fact (𝒪 l)]
    [Fact (𝒪 r)] (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w)] :
    TwoSquare (F.pf t) (F.sh l) (F.sh r) (F.pf b) :=
  mateEquiv (F.adj t) (F.adj b) (inv (F.baseChange t l r b w))

end Square

end ExchangeFormalism

end CategoryTheory
