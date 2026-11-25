/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.Elements
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Geometric points of the small étale site: the universe of the coefficients, and base change

For a scheme `S : Scheme.{u}`, Mathlib's geometric points `S.pointSmallEtale` have fibre
functors with values in `Type u`, and Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms`
applies to a coefficient category concrete over that same `Type u`. The coefficient
categories used in the six functor formalism have `Hom`-types in `Type (u + 1)` and are
concrete over `Type (u + 1)` (this is the case of `ModuleCat.{u + 1} Λ`), so the geometric
points have to be moved up one universe first. This file does that: the family
`AlgebraicGeometry.Scheme.uliftPointSmallEtale` of geometric points at `Type (u + 1)` is
conservative, and hence jointly reflects isomorphisms of `A`-valued étale sheaves. Its
members are the points `AlgebraicGeometry.Scheme.algClosurePoint s` given by the *algebraic*
closures of the residue fields, so that the results which ask for an algebraically closed
residue field apply to them.

This file also identifies the geometric points of the small étale site under base change.
Let `f : X ⟶ Y` be a morphism of schemes and let `s : Spec Ω ⟶ X` be a geometric point of
`X`, that is, `Ω` is a separably closed field. Base change along `f` is the functor
`f.Etale : Y.Etale ⥤ X.Etale` between the small étale sites; it is representably flat and
preserves covers, so `CategoryTheory.GrothendieckTopology.Point.comap` turns the geometric
point `AlgebraicGeometry.Scheme.pointSmallEtale s` of `X` into a point of the small étale
site of `Y`. That point is the geometric point `s ≫ f` of `Y`.

On an object `V` of `Y.Etale` the identification is the universal property of the pullback:
a morphism `Spec Ω ⟶ V ×_Y X` over `X` is the same thing as a morphism `Spec Ω ⟶ V` over
`Y`. It is therefore an instance of the adjunction `CategoryTheory.Over.mapPullbackAdj`
between post-composition with `f` and base change along `f` on the slice categories, read
through `CategoryTheory.Adjunction.compCoyonedaIso`.

Finally, when `f = i` is a *closed immersion* the base change functor on pointed étale
neighbourhoods is **initial**. Initiality is obtained from
`CategoryTheory.Functor.initial_of_exists_of_isCofiltered`, so no connectedness argument is
written by hand: the categories of elements of the fibre functors of points are cofiltered,
and only the two hypotheses of that criterion are proved here. The first is
`AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion`, the local lifting of
étale morphisms along a closed immersion. The second combines the open agreement locus of
`AlgebraicGeometry.FormallyUnramified.eqLocus` with the fact that `V ×_X Z ⟶ V` is a closed
immersion, hence inducing on the underlying spaces, so that the agreement locus is the trace
of an open of `V`.

## Main definitions

- `AlgebraicGeometry.Scheme.algClosurePoint`: the geometric point of `S` at `s` given by the
  algebraic closure of the residue field of `s`.
- `AlgebraicGeometry.Scheme.uliftPointSmallEtale`: the geometric point of the small étale
  site of `S` at `s`, with its fibre functor taking values in `Type (u + 1)`.
- `AlgebraicGeometry.Scheme.pointSmallEtaleFiberEtaleIso`: the fibre functor of the
  geometric point `s` of `X`, composed with base change along `f`, is the fibre functor of
  the geometric point `s ≫ f` of `Y`.
- `AlgebraicGeometry.Scheme.pointSmallEtaleComapIso`: the point of the small étale site of
  `Y` obtained from `s` by `CategoryTheory.GrothendieckTopology.Point.comap` along base
  change *is* the geometric point `s ≫ f`, as an isomorphism of points.
- `AlgebraicGeometry.Scheme.pointSmallEtaleElementsBaseChange`: base change as a functor
  between the categories of elements of the two fibre functors, that is, between the
  categories of pointed étale neighbourhoods of `s ≫ f` in `Y` and of `s` in `X`.
- `AlgebraicGeometry.Scheme.pointSmallEtaleCongr`,
  `AlgebraicGeometry.Scheme.uliftPointSmallEtaleCongr`: reparametrising a geometric point
  `s : Spec Ω ⟶ S` by an isomorphism `e : Spec Ω' ≅ Spec Ω` does not change the point:
  `e ≫ s` and `s` are isomorphic points of the small étale site.

## Main results

- `AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale`: the
  universe-lifted geometric points of `S` form a conservative family; the variant
  `..._of_iUnion_range_eq_univ` says the same for an arbitrary jointly surjective family of
  geometric points of `S`.
- `AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map`: a morphism of `A`-valued sheaves
  on the small étale site of `S` which is invertible on all these fibres is invertible.
- `AlgebraicGeometry.Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint`: two morphisms of
  `A`-valued sheaves on the small étale site of `S` which agree on all these fibres are
  equal.
- `AlgebraicGeometry.Scheme.initial_pointSmallEtaleElementsBaseChange`: for a closed
  immersion `i`, base change is initial on pointed étale neighbourhoods.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

/-- Compatibility projection for the underlying morphism of an element morphism. -/
alias CategoryTheory.Functor.Elements.Hom.val :=
  CategoryTheory.Functor.Elements.Hom.hom

namespace AlgebraicGeometry.Scheme

section Ulift

variable (S : Scheme.{u})

/-- The geometric point of `S` at `s` given by the algebraic closure of the residue field
of `s`. -/
noncomputable def algClosurePoint (s : S) :
    Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  (SpecToEquivOfField (AlgebraicClosure (S.residueField s)) _).2
    ⟨s, CommRingCat.ofHom (algebraMap (S.residueField s) _)⟩

@[simp]
lemma algClosurePoint_base (s : S) (x : Spec (.of (AlgebraicClosure (S.residueField s)))) :
    (S.algClosurePoint s).base x = s := by
  simp [algClosurePoint, SpecToEquivOfField]

lemma iUnion_range_algClosurePoint : ⋃ s : S, Set.range (S.algClosurePoint s) = Set.univ := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨s, default, by simp⟩

/-- The geometric point of the small étale site of `S` at `s`, given by the algebraic closure
of the residue field of `s`, with its fibre functor taking values in `Type (u + 1)`.

The residue field is replaced by its algebraic closure rather than by its separable closure,
so that the results which need an algebraically closed residue field, such as the stalk
formula for a finite direct image, apply to this family as well. -/
noncomputable def uliftPointSmallEtale (s : S) : S.smallEtaleTopology.Point.{u + 1} :=
  (pointSmallEtale (S.algClosurePoint s)).ulift.{u + 1}

/-- **The universe-lifted geometric points of a jointly surjective family of geometric points
of `S` form a conservative family.** This is Mathlib's
`AlgebraicGeometry.Scheme.isConservative_pointSmallEtale` moved up one universe, so that it
can be used with coefficients concrete over `Type (u + 1)`. -/
lemma isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    {ι : Type u} {Ω : ι → Type u} [∀ i, Field (Ω i)] [∀ i, IsSepClosed (Ω i)]
    (s : ∀ i, Spec (.of (Ω i)) ⟶ S) (hs : ⋃ i, Set.range (s i) = Set.univ) :
    (ObjectProperty.ofObj fun i ↦
      (pointSmallEtale (s i)).ulift.{u + 1}).IsConservativeFamilyOfPoints :=
  -- the universes are, in order: the one we lift to, the one of the fibres of
  -- `pointSmallEtale`, and those of the morphisms, the objects and the index type of `S.Etale`
  (isConservative_pointSmallEtale s hs).ulift.{u + 1, u, u, u + 1, u} _

/-- **The universe-lifted geometric points of `S` form a conservative family**
(blueprint `lemma-openclosed-point-ulift`). -/
lemma isConservativeFamilyOfPoints_ulift_pointSmallEtale :
    (ObjectProperty.ofObj S.uliftPointSmallEtale).IsConservativeFamilyOfPoints :=
  isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ S
    S.algClosurePoint S.iUnion_range_algClosurePoint

variable (A : Type u') [Category.{u + 1} A] [HasColimitsOfSize.{u + 1, u + 1} A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)} [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{u + 1} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- **The universe-lifted geometric points of `S` jointly reflect isomorphisms of `A`-valued
étale sheaves.** Besides the usual assumptions on the coefficient category `A`, this needs
`A` to be concrete over `Type (u + 1)` in a way compatible with filtered colimits and
sheafification; this holds for `A = ModuleCat.{u + 1} Λ`. -/
lemma jointlyReflectIsomorphisms_ulift_pointSmallEtale :
    JointlyReflectIsomorphisms
      (fun (Φ : (ObjectProperty.ofObj S.uliftPointSmallEtale).FullSubcategory) ↦
        Φ.obj.sheafFiber (A := A)) :=
  (isConservativeFamilyOfPoints_ulift_pointSmallEtale S).jointlyReflectIsomorphisms A

variable {S A}

include hJ in
/-- A morphism of `A`-valued sheaves on the small étale site of `S` whose fibre at every
geometric point of `S` is invertible is invertible
(blueprint `lemma-weil-pbc-geometric-stalk-conservative`). -/
lemma isIso_of_isIso_sheafFiber_map {F G : Sheaf S.smallEtaleTopology A} (φ : F ⟶ G)
    (h : ∀ s : S, IsIso ((S.uliftPointSmallEtale s).sheafFiber.map φ)) :
    IsIso φ :=
  ((jointlyReflectIsomorphisms_ulift_pointSmallEtale S A).isIso_iff φ).2
    (by
      rintro ⟨-, ⟨s⟩⟩
      exact h s)

include hJ in
/-- Two morphisms of `A`-valued sheaves on the small étale site of `S` which agree on the
fibres at the geometric points `S.algClosurePoint s` of `S` are equal. -/
lemma sheafHom_ext_of_sheafFiber_map_algClosurePoint [HasColimitsOfSize.{u, u} A]
    [AB5OfSize.{u + 1, u + 1} A] [HasFiniteLimits A] {F G : Sheaf S.smallEtaleTopology A}
    {φ ψ : F ⟶ G}
    (h : ∀ s : S, (pointSmallEtale (S.algClosurePoint s)).sheafFiber.map φ =
      (pointSmallEtale (S.algClosurePoint s)).sheafFiber.map ψ) : φ = ψ := by
  refine ((isConservativeFamilyOfPoints_ulift_pointSmallEtale S).jointlyFaithful A).map_injective
    ?_
  rintro ⟨-, ⟨s⟩⟩
  dsimp only [uliftPointSmallEtale]
  have e := GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
    (pointSmallEtale (S.algClosurePoint s)) A
  rw [← Iso.cancel_iso_hom_right _ _ (e.app G), Iso.app_hom, e.hom.naturality,
    e.hom.naturality, h s]

end Ulift

section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

/-- For a geometric point `s : Spec Ω ⟶ X` and a morphism `f : X ⟶ Y`, the fibre functor of
`s` composed with base change along `f` is the fibre functor of the geometric point `s ≫ f`
of `Y`: on `V : Y.Etale` the left hand side is the set of morphisms `Spec Ω ⟶ V ×_Y X` over
`X` and the right hand side is the set of morphisms `Spec Ω ⟶ V` over `Y`, and these agree
by the universal property of the pullback. -/
noncomputable def pointSmallEtaleFiberEtaleIso :
    f.Etale ⋙ (pointSmallEtale s).fiber ≅ (pointSmallEtale (s ≫ f)).fiber :=
  Functor.isoWhiskerLeft (Etale.forget Y)
    ((Adjunction.compCoyonedaIso (CategoryTheory.Over.mapPullbackAdj f)).app
      (op (CategoryTheory.Over.mk s))).symm

/-- The category of elements of the fibre functor of `pointSmallEtale s` composed with base
change is initially small, being equivalent by
`AlgebraicGeometry.Scheme.pointSmallEtaleFiberEtaleIso` to the category of elements of the
fibre functor of `pointSmallEtale (s ≫ f)`. This is the remaining hypothesis of
`CategoryTheory.GrothendieckTopology.Point.comap`. -/
instance initiallySmall_elements_etale_comp_pointSmallEtaleFiber :
    InitiallySmall.{u} (f.Etale ⋙ (pointSmallEtale s).fiber).Elements :=
  initiallySmall_of_initial_of_initiallySmall
    (NatIso.mapElements (pointSmallEtaleFiberEtaleIso f s).symm).functor

/-- Pulling a geometric point `s : Spec Ω ⟶ X` back along base change for a morphism
`f : X ⟶ Y` gives the geometric point `s ≫ f` of `Y`. -/
noncomputable def pointSmallEtaleComapIso :
    (pointSmallEtale s).comap f.Etale (Hom.coverPreserving_etale f) ≅
      pointSmallEtale (s ≫ f) :=
  GrothendieckTopology.Point.isoMk (pointSmallEtaleFiberEtaleIso f s)

/-- A morphism `Spec Ω ⟶ V ×_Y X` over `X` is carried by
`AlgebraicGeometry.Scheme.pointSmallEtaleFiberEtaleIso` to its composite with the first
projection, a morphism `Spec Ω ⟶ V` over `Y`. -/
@[simp]
lemma pointSmallEtaleFiberEtaleIso_hom_app_left (V : Y.Etale)
    (x : (f.Etale ⋙ (pointSmallEtale s).fiber).obj V) :
    ((pointSmallEtaleFiberEtaleIso f s).hom.app V x).left =
      x.left ≫ Limits.pullback.fst V.hom f :=
  rfl

/-- The morphism `Spec Ω ⟶ V ×_Y X` attached to a morphism `v : Spec Ω ⟶ V` over `Y` by
`AlgebraicGeometry.Scheme.pointSmallEtaleFiberEtaleIso` has first component `v`. -/
@[reassoc (attr := simp)]
lemma pointSmallEtaleFiberEtaleIso_inv_app_left_fst (V : Y.Etale)
    (v : (pointSmallEtale (s ≫ f)).fiber.obj V) :
    ((pointSmallEtaleFiberEtaleIso f s).inv.app V v).left ≫ Limits.pullback.fst V.hom f =
      v.left := by
  rw [← pointSmallEtaleFiberEtaleIso_hom_app_left f s V
    ((pointSmallEtaleFiberEtaleIso f s).inv.app V v),
    (pointSmallEtaleFiberEtaleIso f s).inv_hom_id_app_apply]

/-- The morphism `Spec Ω ⟶ V ×_Y X` attached to a morphism `v : Spec Ω ⟶ V` over `Y` by
`AlgebraicGeometry.Scheme.pointSmallEtaleFiberEtaleIso` has second component `s`; it is a
morphism over `X`. -/
@[reassoc (attr := simp)]
lemma pointSmallEtaleFiberEtaleIso_inv_app_left_snd (V : Y.Etale)
    (v : (pointSmallEtale (s ≫ f)).fiber.obj V) :
    ((pointSmallEtaleFiberEtaleIso f s).inv.app V v).left ≫ Limits.pullback.snd V.hom f =
      s :=
  CategoryTheory.Over.w ((pointSmallEtaleFiberEtaleIso f s).inv.app V v)

/-- Base change along `f : X ⟶ Y` as a functor between the categories of elements of the
fibre functors of the geometric points `s ≫ f` of `Y` and `s` of `X`: a pointed étale
neighbourhood `(V, v)` of `s ≫ f` in `Y` is sent to the pointed étale neighbourhood
`(V ×_Y X, (v, s))` of `s` in `X`.

Over `Y.Etale` this is nothing but base change, see
`AlgebraicGeometry.Scheme.pointSmallEtaleElementsBaseChange_comp_π`. -/
noncomputable def pointSmallEtaleElementsBaseChange :
    (pointSmallEtale (s ≫ f)).fiber.Elements ⥤ (pointSmallEtale s).fiber.Elements :=
  NatTrans.mapElements (pointSmallEtaleFiberEtaleIso f s).inv ⋙
    Functor.Elements.precomp f.Etale (pointSmallEtale s).fiber

@[simp]
lemma pointSmallEtaleElementsBaseChange_obj_fst
    (c : (pointSmallEtale (s ≫ f)).fiber.Elements) :
    ((pointSmallEtaleElementsBaseChange f s).obj c).obj = f.Etale.obj c.obj :=
  rfl

@[simp]
lemma pointSmallEtaleElementsBaseChange_map_val
    {c c' : (pointSmallEtale (s ≫ f)).fiber.Elements} (t : c ⟶ c') :
    ((pointSmallEtaleElementsBaseChange f s).map t).val = f.Etale.map t.val :=
  rfl

/-- `AlgebraicGeometry.Scheme.pointSmallEtaleElementsBaseChange` lies over base change: the
square
```
Elements (pointSmallEtale (s ≫ f)).fiber --- base change ---> Elements (pointSmallEtale s).fiber
             |                                                             |
             π                                                             π
             ↓                                                             ↓
          Y.Etale ------------------- f.Etale -----------------------> X.Etale
```
commutes, on the nose. -/
lemma pointSmallEtaleElementsBaseChange_comp_π :
    pointSmallEtaleElementsBaseChange f s ⋙
        Functor.Elements.π (pointSmallEtale s).fiber =
      Functor.Elements.π (pointSmallEtale (s ≫ f)).fiber ⋙ f.Etale :=
  rfl


end BaseChange

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)

/-- Every pointed étale neighbourhood of a geometric point `s` of `Z` is dominated by the
base change of a pointed étale neighbourhood of `s ≫ i` in `X`. This is the first hypothesis
of `CategoryTheory.Functor.initial_of_exists_of_isCofiltered`, and its content is
`AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion`. -/
private theorem exists_hom_pointSmallEtaleElementsBaseChange
    (d : (pointSmallEtale s).fiber.Elements) :
    ∃ c, Nonempty ((pointSmallEtaleElementsBaseChange i s).obj c ⟶ d) := by
  obtain @⟨W, w⟩ := d
  -- lift `W` locally along `i` to an étale `X`-scheme `q : V ⟶ X`, in a way compatible with
  -- the marked point `w` of `W`
  obtain ⟨V, q, hq, g, hg, t, ht⟩ :=
    AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion i W.hom w.left
  have := hq
  have hts : t ≫ pullback.snd q i = s := by
    rw [← hg, ← Category.assoc, ht]
    exact CategoryTheory.Over.w w
  have hv : (t ≫ pullback.fst q i) ≫ q = s ≫ i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hts]
  refine ⟨Functor.elementsMk _ (Scheme.Etale.mk q)
      (CategoryTheory.Over.homMk (t ≫ pullback.fst q i) hv),
    ⟨Functor.Elements.homMk (MorphismProperty.Over.homMk g hg) ?_⟩⟩
  -- the marked point of `V ×_X Z` is `t`, since its two components are those of `t`
  have hp : ((pointSmallEtaleFiberEtaleIso i s).inv.app (Scheme.Etale.mk q)
      (CategoryTheory.Over.homMk (t ≫ pullback.fst q i) hv)).left = t := by
    refine pullback.hom_ext ?_ ?_
    · rw [pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
      rfl
    · rw [pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
      exact hts.symm
  apply CategoryTheory.Over.OverMorphism.ext
  change ((pointSmallEtaleFiberEtaleIso i s).inv.app (Scheme.Etale.mk q)
    (CategoryTheory.Over.homMk (t ≫ pullback.fst q i) hv)).left ≫ g = w.left
  rw [hp, ht]

/-- Two morphisms out of the base change `V ×_X Z` of a pointed étale neighbourhood of
`s ≫ i` into an étale `Z`-scheme which agree over `Z` are equalised after shrinking `V`.
This is the second hypothesis of
`CategoryTheory.Functor.initial_of_exists_of_isCofiltered`.

The two morphisms agree on the open `AlgebraicGeometry.FormallyUnramified.eqLocus` of
`V ×_X Z`, which contains the marked point. Since `V ×_X Z ⟶ V` is a closed immersion it is
inducing on the underlying spaces, so that agreement locus is the trace of an open `V₀` of
`V`; and `V₀` is the required shrinking of `V`. -/
private theorem exists_map_comp_eq_pointSmallEtaleElementsBaseChange
    {d : (pointSmallEtale s).fiber.Elements}
    {c : (pointSmallEtale (s ≫ i)).fiber.Elements}
    (σ σ' : (pointSmallEtaleElementsBaseChange i s).obj c ⟶ d) :
    ∃ (c' : (pointSmallEtale (s ≫ i)).fiber.Elements) (τ : c' ⟶ c),
      (pointSmallEtaleElementsBaseChange i s).map τ ≫ σ =
        (pointSmallEtaleElementsBaseChange i s).map τ ≫ σ' := by
  obtain @⟨V, v⟩ := c
  obtain @⟨W, w⟩ := d
  -- `p` is the marked point of `V ×_X Z`; both `σ` and `σ'` send it to the marked point of `W`
  set p : Spec (.of Ω) ⟶ pullback V.hom i :=
    ((pointSmallEtaleFiberEtaleIso i s).inv.app V v).left
  have key : ∀ τ : (pointSmallEtaleElementsBaseChange i s).obj (Functor.elementsMk _ V v) ⟶
      Functor.elementsMk _ W w,
      p ≫ τ.hom.left = w.left := fun τ ↦ congrArg CategoryTheory.Over.Hom.left τ.map_val
  have hab : σ.hom.left ≫ W.hom = σ'.hom.left ≫ W.hom := by
    rw [CategoryTheory.Over.w, CategoryTheory.Over.w]
  have hpab : p ≫ σ.hom.left = p ≫ σ'.hom.left := by rw [key σ, key σ']
  have hvfst : p ≫ pullback.fst V.hom i = v.left :=
    pointSmallEtaleFiberEtaleIso_inv_app_left_fst i s V v
  -- the agreement locus of `σ` and `σ'` is the trace of an open `V₀` of `V`
  obtain ⟨S, hS, hSU⟩ :=
    (pullback.fst V.hom i).isClosedEmbedding.isInducing.isOpen_iff.1
      (FormallyUnramified.eqLocus W.hom σ.hom.left σ'.hom.left hab).2
  set V₀ : V.left.Opens := ⟨S, hS⟩
  -- `V₀` contains the marked point of `V`, which is the image of `p`
  have hVrange : Set.range v.left.base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx := FormallyUnramified.range_subset_eqLocus W.hom σ.hom.left σ'.hom.left hab p hpab
      (Set.mem_range_self x)
    have hx' : (pullback.fst V.hom i).base (p.base x) ∈ S := by
      rwa [← Set.mem_preimage, hSU]
    rw [← hvfst]
    exact hx'
  set v₀ := IsOpenImmersion.lift V₀.ι v.left hVrange
  have hv₀ι : v₀ ≫ V₀.ι = v.left := IsOpenImmersion.lift_fac _ _ _
  set θ : Scheme.Etale.mk (V₀.ι ≫ V.hom) ⟶ V :=
    MorphismProperty.Over.homMk V₀.ι rfl with hθ
  have hmfst : (i.Etale.map θ).left ≫ pullback.fst V.hom i =
      pullback.fst (Scheme.Etale.mk (V₀.ι ≫ V.hom)).hom i ≫ V₀.ι := by
    simp [Scheme.Hom.Etale, hθ]
  refine ⟨Functor.elementsMk _ (Scheme.Etale.mk (V₀.ι ≫ V.hom))
      (CategoryTheory.Over.homMk v₀ ?_),
    Functor.Elements.homMk θ ?_, ?_⟩
  · change v₀ ≫ V₀.ι ≫ V.hom = s ≫ i
    rw [← Category.assoc, hv₀ι]
    exact CategoryTheory.Over.w v
  · exact CategoryTheory.Over.OverMorphism.ext hv₀ι
  · -- `V₀ ×_X Z` lands in the agreement locus, so `σ` and `σ'` agree on it
    have hmr : Set.range (i.Etale.map θ).left.base ⊆
        Set.range (FormallyUnramified.eqLocus W.hom σ.hom.left σ'.hom.left hab).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      have h₁ : (pullback.fst V.hom i) ((i.Etale.map θ).left x) =
          V₀.ι ((pullback.fst (Scheme.Etale.mk (V₀.ι ≫ V.hom)).hom i) x) :=
        congrArg (fun m ↦ m.base x) hmfst
      have hmem : (i.Etale.map θ).left.base x ∈ ⇑(pullback.fst V.hom i) ⁻¹' S := by
        change (pullback.fst V.hom i) ((i.Etale.map θ).left x) ∈ S
        rw [h₁]
        exact (Scheme.Opens.range_ι V₀).subset (Set.mem_range_self _)
      rwa [hSU] at hmem
    refine Functor.Elements.hom_ext (MorphismProperty.Over.Hom.ext ?_)
    change (i.Etale.map θ).left ≫ σ.hom.left = (i.Etale.map θ).left ≫ σ'.hom.left
    rw [← IsOpenImmersion.lift_fac
      (FormallyUnramified.eqLocus W.hom σ.hom.left σ'.hom.left hab).ι _ hmr,
      Category.assoc, Category.assoc, FormallyUnramified.eqLocus_ι_comp_eq]

/-- Blueprint `lemma-finite-direct-images--1`, first assertion: **Base change along a closed
immersion is initial on pointed étale neighbourhoods.** For
a closed immersion `i : Z ⟶ X` and a geometric point `s` of `Z`, every pointed étale
neighbourhood of `s` in `Z` is dominated by one of the form `V ×_X Z`, and two maps out of
such a `V ×_X Z` are equalised after shrinking `V`; the categories of pointed étale
neighbourhoods being cofiltered, this is initiality by
`CategoryTheory.Functor.initial_of_exists_of_isCofiltered`. -/
theorem initial_pointSmallEtaleElementsBaseChange :
    (pointSmallEtaleElementsBaseChange i s).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (exists_hom_pointSmallEtaleElementsBaseChange i s)
    (fun σ σ' ↦ exists_map_comp_eq_pointSmallEtaleElementsBaseChange i s σ σ')

end ClosedImmersion

section Reparametrization

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  (e : Spec (.of Ω') ≅ Spec (.of Ω)) (s : Spec (.of Ω) ⟶ S)

/-- The isomorphism of fibre functors underlying
`AlgebraicGeometry.Scheme.pointSmallEtaleCongr`: a lift `t : Spec Ω' ⟶ U` of `e ≫ s` to an
étale `U ⟶ S` is sent to the lift `e⁻¹ ≫ t` of `s`,

```
  Spec Ω --e⁻¹--> Spec Ω' --t--> U
        \                       |
         s                      v
          --------------------> S
```
-/
noncomputable def pointSmallEtaleFiberCongr :
    (pointSmallEtale (e.hom ≫ s)).fiber ≅ (pointSmallEtale s).fiber :=
  Functor.isoWhiskerLeft (Etale.forget S)
    (coyoneda.mapIso (Over.isoMk e.symm).op)

/-- Reparametrising a geometric point `s : Spec Ω ⟶ S` by an isomorphism
`e : Spec Ω' ≅ Spec Ω` gives an isomorphic point of the small étale site: `e ≫ s ≅ s`, by
`AlgebraicGeometry.Scheme.pointSmallEtaleFiberCongr` on fibre functors. -/
noncomputable def pointSmallEtaleCongr : pointSmallEtale (e.hom ≫ s) ≅ pointSmallEtale s :=
  GrothendieckTopology.Point.isoMk (pointSmallEtaleFiberCongr e s)

/-- The universe-lifted form of `AlgebraicGeometry.Scheme.pointSmallEtaleCongr`. -/
noncomputable def uliftPointSmallEtaleCongr :
    (pointSmallEtale (e.hom ≫ s)).ulift.{u + 1} ≅ (pointSmallEtale s).ulift.{u + 1} :=
  GrothendieckTopology.Point.isoMk
    (Functor.isoWhiskerRight (pointSmallEtaleFiberCongr e s) uliftFunctor.{u + 1})

end Reparametrization

end AlgebraicGeometry.Scheme
