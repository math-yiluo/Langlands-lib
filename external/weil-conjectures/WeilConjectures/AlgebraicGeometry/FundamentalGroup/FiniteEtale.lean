/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Galois.Equivalence
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The category of finite étale schemes and its fibre functor

Let `Y` be a scheme and `s : Spec Ω ⟶ Y` a geometric point, `Ω` a separably closed field.
The finite étale `Y`-schemes form the category `AlgebraicGeometry.Scheme.FiniteEtale Y`, a full
subcategory of the small étale site `Y.Etale`, and taking the geometric fibre at `s`,
i.e. the `Y`-morphisms `Spec Ω ⟶ P`, is the fibre functor
`AlgebraicGeometry.Scheme.FiniteEtale.fiber s` to finite sets.

A geometric point of `Y` lifts along a finite étale morphism `f : P ⟶ Y` as soon as its image
lies in the image of `f` (`AlgebraicGeometry.Scheme.Hom.exists_lift_of_isSepClosed`), since the
fibre of `f` over it is a disjoint union of copies of `Spec Ω`.

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale`: the category of finite étale `Y`-schemes.
- `AlgebraicGeometry.Scheme.FiniteEtale.fiber`: the fibre functor at a geometric point.
- `AlgebraicGeometry.Scheme.FiniteEtale.ofIsClopen`: an open and closed subscheme of a finite
  étale `Y`-scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

/-- A geometric point `y : Spec Ω ⟶ Y`, `Ω` separably closed, whose image lies in the image of a
finite étale morphism `f : P ⟶ Y` lifts along `f`: the fibre `P ×_Y Spec Ω` is a nonempty
disjoint union of copies of `Spec Ω`, so it has a section. -/
lemma Scheme.Hom.exists_lift_of_isSepClosed {P Y : Scheme.{u}} (f : P ⟶ Y) [IsFinite f] [Etale f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (h : ∃ z, y z ∈ Set.range f) : ∃ x : Spec (.of Ω) ⟶ P, x ≫ f = y := by
  obtain ⟨z, w, hw⟩ := h
  obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w z hw
  obtain ⟨ι, _, -, ⟨e⟩⟩ := f.exists_overIso_sigma_of_isSepClosed y
  obtain ⟨i, -⟩ := (sigmaMk fun _ : ι ↦ Spec (.of Ω)).symm (e.hom.left t)
  have he : e.inv.left ≫ pullback.snd f y = Sigma.desc fun _ : ι ↦ 𝟙 (Spec (.of Ω)) :=
    Over.w e.inv
  refine ⟨Sigma.ι (fun _ : ι ↦ Spec (.of Ω)) i ≫ e.inv.left ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv.left, he,
    Sigma.ι_comp_desc_assoc, Category.id_comp]

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u})

/-- The category `FÉt(Y)` of finite étale `Y`-schemes, as a full subcategory of the small étale
site of `Y`. -/
protected abbrev FiniteEtale : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun P : Y.Etale ↦ IsFinite P.hom

namespace FiniteEtale

variable {Y} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

lemma hom_ext {P Q : Y.FiniteEtale} {f g : P ⟶ Q}
    (h : f.hom.left = g.hom.left) : f = g :=
  ObjectProperty.hom_ext _ (MorphismProperty.Over.Hom.ext h)

lemma hom_left_comp {P Q : Y.FiniteEtale}
    (f : P ⟶ Q) : f.hom.left ≫ Q.obj.hom = P.obj.hom := by
  simp

/-- Blueprint `rem-ptr-galois-categories-1`: the geometric fibre of a finite étale `Y`-scheme
at a geometric point is finite.

The geometric fibre `|P_s|` is the set of `Y`-morphisms `Spec Ω ⟶ P`, which are the sections of
the base change `P ×_Y Spec Ω ⟶ Spec Ω`; by blueprint `lem-galois-geometric-fibre`
(`AlgebraicGeometry.Scheme.Hom.exists_overIso_sigma_of_isSepClosed`) this base change is finite
étale, so its sections are the `Ω`-algebra maps out of a finite `Ω`-algebra, of which there are
finitely many. -/
lemma finite_fiber (P : Y.FiniteEtale) : Finite ((pointSmallEtale s).fiber.obj P.obj) := by
  have : IsFinite P.obj.hom := P.property
  set h := pullback.snd P.obj.hom s
  have : IsAffine (pullback P.obj.hom s) := isAffine_of_isAffineHom h
  let := h.ΓAlgebra
  have := h.etale_ΓAlgebra
  have := Algebra.FormallyUnramified.finite_of_free Ω Γ(pullback P.obj.hom s, ⊤)
  have hid : Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let φ (x : (pointSmallEtale s).fiber.obj P.obj) :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω))) ⟶ Over.mk h :=
    Over.homMk (pullback.lift x.left (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)))
      (by simpa [hid] using Over.w x)) (by simp [h])
  refine Finite.of_injective (h.overHomEquivAlgHom Ω ∘ φ) fun x y hxy ↦ ?_
  have := congrArg (fun u ↦ u.left ≫ pullback.fst P.obj.hom s)
    ((h.overHomEquivAlgHom Ω).injective hxy)
  exact Over.OverMorphism.ext (by simpa [φ] using this)

/-- Blueprint `def-galois-fibre-functor`: The fibre functor.

The fibre functor `F_s : FÉt(Y) ⥤ FintypeCat` at a geometric point `s : Spec Ω ⟶ Y`, sending a
finite étale `P ⟶ Y` to the finite set of `Y`-morphisms `Spec Ω ⟶ P`. -/
noncomputable def fiber : Y.FiniteEtale ⥤ FintypeCat.{u} :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (pointSmallEtale s).fiber) (finite_fiber s)

@[simp]
lemma fiber_obj_obj (P : Y.FiniteEtale) :
    ((fiber s).obj P).obj = (pointSmallEtale s).fiber.obj P.obj := rfl

lemma fiber_map_apply {P Q : Y.FiniteEtale} (f : P ⟶ Q) (x : (fiber s).obj P) :
    (fiber s).map f x = (pointSmallEtale s).fiber.map f.hom x := rfl


lemma fiber_map_left {P Q : Y.FiniteEtale}
    (f : P ⟶ Q) (x : (fiber s).obj P) : ((fiber s).map f x).left = x.left ≫ f.hom.left := rfl

lemma fiber_ext {P : Y.FiniteEtale}
    {x y : (fiber s).obj P} (h : x.left = y.left) : x = y :=
  Over.OverMorphism.ext h

lemma fiber_left_comp {P : Y.FiniteEtale}
    (x : (fiber s).obj P) : x.left ≫ P.obj.hom = s :=
  Over.w x

/-- The geometric fibre of a nonempty finite étale scheme over a connected scheme is nonempty:
the image of `P` is open and closed, hence everything, so `s` lifts. -/
lemma nonempty_fiber_of_nonempty [ConnectedSpace Y] (P : Y.FiniteEtale)
    (h : Nonempty P.obj.left) : Nonempty ((fiber s).obj P) := by
  let f : P.obj.left ⟶ Y := P.obj.hom
  have : IsFinite f := P.property
  have : Etale f := P.obj.prop
  have hc : IsClopen (Set.range f) := ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  obtain ⟨x⟩ := h
  have hr : Set.range f = Set.univ := hc.eq_univ ⟨_, x, rfl⟩
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  obtain ⟨t, ht⟩ := f.exists_lift_of_isSepClosed s ⟨z, hr ▸ Set.mem_univ _⟩
  exact ⟨Over.homMk t ht⟩

/-- The fibre of a finite étale scheme is nonempty if and only if the scheme is, over a
connected base. -/
lemma nonempty_fiber_iff [ConnectedSpace Y] (P : Y.FiniteEtale) :
    Nonempty ((fiber s).obj P) ↔ Nonempty P.obj.left := by
  refine ⟨fun ⟨x⟩ ↦ ?_, nonempty_fiber_of_nonempty s P⟩
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  exact ⟨x.left z⟩

/-- A morphism of finite étale `Y`-schemes is finite. -/
instance isFinite_hom_left {P Q : Y.FiniteEtale} (φ : P ⟶ Q) : IsFinite φ.hom.left := by
  have : IsFinite P.obj.hom := P.property
  have : IsFinite Q.obj.hom := Q.property
  have : IsFinite (φ.hom.left ≫ Q.obj.hom) := by rw [hom_left_comp]; infer_instance
  exact IsFinite.of_comp φ.hom.left Q.obj.hom

/-- A morphism of finite étale `Y`-schemes is étale. -/
instance etale_hom_left {P Q : Y.FiniteEtale} (φ : P ⟶ Q) : Etale φ.hom.left := by
  have : Etale P.obj.hom := P.obj.prop
  have : Etale Q.obj.hom := Q.obj.prop
  have : Etale (φ.hom.left ≫ Q.obj.hom) := by rw [hom_left_comp]; infer_instance
  exact Etale.of_comp φ.hom.left Q.obj.hom

/-- A morphism of finite étale `Y`-schemes whose underlying morphism is surjective induces a
surjection on geometric fibres. -/
lemma surjective_fiber_map_of_surjective {P Q : Y.FiniteEtale} (φ : P ⟶ Q)
    (h : Function.Surjective φ.hom.left) : Function.Surjective ((fiber s).map φ) := by
  intro x
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  obtain ⟨t, ht⟩ := φ.hom.left.exists_lift_of_isSepClosed x.left ⟨z, h _⟩
  refine ⟨Over.homMk t ?_, fiber_ext s ?_⟩
  · change t ≫ P.obj.hom = s
    rw [← hom_left_comp φ, ← Category.assoc, ht, fiber_left_comp]
  · rw [fiber_map_left]
    exact ht

/-- The open and closed subscheme `V` of a finite étale `Y`-scheme `P`, as a finite étale
`Y`-scheme. -/
noncomputable abbrev ofIsClopen (P : Y.FiniteEtale) (V : P.obj.left.Opens)
    (hV : IsClosed (V : Set P.obj.left)) : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (V.ι ≫ P.obj.hom) (by have : Etale P.obj.hom := P.obj.prop
                                                    infer_instance),
    by
      have : IsFinite P.obj.hom := P.property
      have : IsClosedImmersion V.ι := IsClosedImmersion.of_isOpenImmersion V.ι (by simpa using hV)
      exact inferInstanceAs (IsFinite (V.ι ≫ P.obj.hom))⟩

/-- The inclusion of an open and closed subscheme of a finite étale `Y`-scheme. -/
noncomputable abbrev ofIsClopenι (P : Y.FiniteEtale) (V : P.obj.left.Opens)
    (hV : IsClosed (V : Set P.obj.left)) : ofIsClopen P V hV ⟶ P :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk V.ι rfl)

instance (P : Y.FiniteEtale) (V : P.obj.left.Opens) (hV : IsClosed (V : Set P.obj.left)) :
    Mono (ofIsClopenι P V hV) :=
  ⟨fun _ _ h ↦ hom_ext ((cancel_mono V.ι).1 congr(($h).hom.left))⟩

section Connected

variable [ConnectedSpace Y]

/-- A finite étale scheme over a connected scheme with nonempty geometric fibre is surjective:
its image is open, as étale morphisms are open, closed, as finite morphisms are closed, and
nonempty. -/
lemma surjective_of_nonempty_fiber
    (P : Y.FiniteEtale) (h : Nonempty ((fiber s).obj P)) : Surjective P.obj.hom := by
  let f : P.obj.left ⟶ Y := P.obj.hom
  have : IsFinite f := P.property
  have : Etale f := P.obj.prop
  have hc : IsClopen (Set.range f) := ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  obtain ⟨x⟩ := h
  let x' : Spec (.of Ω) ⟶ P.obj.left := x.left
  have hne : (Set.range f).Nonempty := ⟨_, x' default, rfl⟩
  exact ⟨fun y ↦ (hc.eq_univ hne ▸ Set.mem_univ y : y ∈ Set.range f)⟩

end Connected

end FiniteEtale

end AlgebraicGeometry.Scheme
