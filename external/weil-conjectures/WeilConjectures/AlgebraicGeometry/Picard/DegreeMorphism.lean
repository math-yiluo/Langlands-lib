/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# The degree morphism `Pic_{X/S} ⟶ ℤ` and its kernel

Let `f: X ⟶ S` be a proper, flat morphism locally of finite presentation. This file packages
the degree `AlgebraicGeometry.picardDegree` of sections of the relative Picard functor as a
morphism of fppf sheaves to the constant sheaf `ℤ`, and identifies, over a field `k`, the
degree-`d` part `Pic^d_{X/k}` with the classes of `Pic_{X/k}` of degree `d`.

## Main definitions

- `AlgebraicGeometry.locallyConstantIntPresheaf`: the presheaf `T ↦ {locally constant T → ℤ}`
  on `Over S`, and `AlgebraicGeometry.locallyConstantIntSheaf`: the same presheaf as an fppf
  sheaf, the constant sheaf `ℤ`.
- `AlgebraicGeometry.picardDegreeMorphism`: the degree morphism `Pic_{X/S} ⟶ ℤ`.
- `AlgebraicGeometry.picardDegreeSubfunctor`: the subfunctor of `Pic_{X/S}` of the classes of
  degree `d`; for `d = 0` this is `ker(deg) = Pic⁰_{X/S}`.
- `AlgebraicGeometry.picardFunctorDegreeι`: the canonical morphism `Pic^d_{X/k} ⟶ Pic_{X/k}`,
  the sheafification of the inclusion of the degree-`d` subfunctor of the Picard presheaf.

## Main statements

- `AlgebraicGeometry.isSheaf_locallyConstantIntPresheaf`: locally constant functions glue along
  fppf coverings.
- `AlgebraicGeometry.range_picardFunctorDegreeι`: the morphism `Pic^d_{X/k} ⟶ Pic_{X/k}` is a
  monomorphism whose image is exactly the subfunctor of classes of degree `d`; in particular
  `Pic⁰_{X/k}` is `ker(deg)` (`AlgebraicGeometry.picardFunctorDegreeIsoSubfunctor`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section ConstantSheaf

variable (S : Scheme.{u})

/-- The presheaf of **locally constant integer-valued functions** on schemes over `S`: its value
on `T` is the group of locally constant functions `T → ℤ`, and pullback along `T' ⟶ T` is
composition. It is lifted to `Type (u + 1)` to match the values of the relative Picard functor. -/
noncomputable def locallyConstantIntPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := ULift.{u + 1} (LocallyConstant T.unop.left ℤ)
  map g := ↾fun s ↦ ⟨(ULift.down s).comap g.unop.left.base.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable {S}

@[simp]
lemma locallyConstantIntPresheaf_map_apply {T T' : Over S} (g : T' ⟶ T)
    (s : (locallyConstantIntPresheaf S).obj (op T)) (t : T'.left) :
    ULift.down ((locallyConstantIntPresheaf S).map g.op s) t = ULift.down s (g.left t) :=
  rfl

/-- The members of a compatible family of locally constant functions along a sieve agree at
points with the same image. -/
lemma locallyConstantIntPresheaf_compatible_apply {T : Over S} {R : Sieve T}
    {x : Presieve.FamilyOfElements (locallyConstantIntPresheaf S) R.arrows} (hx : x.Compatible)
    {Z Z' : Over S} {g : Z ⟶ T} {g' : Z' ⟶ T} (hg : R g) (hg' : R g') {z : Z.left}
    {z' : Z'.left} (h : g.left z = g'.left z') :
    ULift.down (x g hg) z = ULift.down (x g' hg') z' := by
  let W : Over S := Over.mk (pullback.fst g.left g'.left ≫ Z.hom)
  let p : W ⟶ Z := Over.homMk (pullback.fst g.left g'.left)
  let p' : W ⟶ Z' := Over.homMk (pullback.snd g.left g'.left) (by
    simp only [W, Over.mk_hom, ← Over.w g, ← Over.w g', pullback.condition_assoc])
  have hpp : p ≫ g = p' ≫ g' := by
    ext
    simp [p, p', pullback.condition]
  obtain ⟨w, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback z z' h
  exact congrArg (fun s : (locallyConstantIntPresheaf S).obj (op W) ↦ ULift.down s w)
    (hx p p' hg hg' hpp)

variable (S) in
/-- **Locally constant functions glue along fppf coverings**: the presheaf
`T ↦ {locally constant T → ℤ}` is an fppf sheaf. A covering is jointly surjective through flat
morphisms locally of finite presentation, which are open, so a compatible family defines a
function on `T` which is locally constant. -/
theorem isSheaf_locallyConstantIntPresheaf :
    Presheaf.IsSheaf (fppfTopology.over S) (locallyConstantIntPresheaf S) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro T R hR x hx
  have H (t : T.left) : ∃ (Z : Over S) (g : Z ⟶ T) (_ : R g) (_ : Flat g.left)
      (_ : LocallyOfFinitePresentation g.left) (z : Z.left), g.left z = t := by
    obtain ⟨Z, g, hg, h₁, h₂, z, hz⟩ := exists_flat_mem_of_mem_fppfTopology_over hR t
    exact ⟨Z, g, hg, h₁, h₂, z, hz⟩
  choose Z g hg hflat hlfp z hz using H
  let φ : T.left → ℤ := fun t ↦ ULift.down (x (g t) (hg t)) (z t)
  have key {Z' : Over S} (g' : Z' ⟶ T) (hg' : R g') (z' : Z'.left) :
      φ (g'.left z') = ULift.down (x g' hg') z' :=
    locallyConstantIntPresheaf_compatible_apply hx _ _ (hz _)
  have hφ : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    have := hflat t
    have := hlfp t
    let s := ULift.down (x (g t) (hg t))
    refine ⟨(g t).left.base '' (s ⁻¹' {s (z t)}), (g t).left.isOpenMap _
      (s.isLocallyConstant.isOpen_fiber _), ⟨z t, rfl, hz t⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [key]
    exact hv
  refine ⟨ULift.up (⟨φ, hφ⟩ : LocallyConstant T.left ℤ), fun Y g' hg' ↦ ?_, fun y hy ↦ ?_⟩
  · exact ULift.ext (LocallyConstant.ext fun z' ↦ key g' hg' z')
  · refine ULift.ext (LocallyConstant.ext fun t ↦ ?_)
    rw [← hz t]
    exact (congrArg (fun s : (locallyConstantIntPresheaf S).obj (op (Z t)) ↦ ULift.down s (z t))
      (hy (g t) (hg t))).trans (key _ (hg t) (z t)).symm

variable (S) in
/-- The **constant sheaf `ℤ`** on the big fppf site of `S`: the sheaf of locally constant
integer-valued functions. -/
noncomputable def locallyConstantIntSheaf : Sheaf (fppfTopology.over S) (Type (u + 1)) :=
  ⟨locallyConstantIntPresheaf S, isSheaf_locallyConstantIntPresheaf S⟩

end ConstantSheaf

section DegreeMorphism

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]

/-- The **degree morphism** `deg: Pic_{X/S} ⟶ ℤ` from the relative Picard functor to the
constant sheaf `ℤ`, for `f` proper, flat and locally of finite presentation: a section `x` over
`T` goes to the locally constant function `AlgebraicGeometry.picardDegree f x: T → ℤ`. -/
noncomputable def picardDegreeMorphism [Flat f] : picardFunctor f ⟶ locallyConstantIntSheaf S :=
  ObjectProperty.homMk
    { app T := ↾fun x ↦ ULift.up ⟨picardDegree f x, isLocallyConstant_picardDegree f x⟩
      naturality T T' g := by
        ext x
        refine ULift.ext (LocallyConstant.ext fun t ↦ ?_)
        exact picardDegree_map f g.unop x t }

@[simp]
lemma picardDegreeMorphism_hom_app_apply [Flat f] {T : Over S}
    (x : (picardFunctor f).obj.obj (op T)) (t : T.left) :
    ULift.down ((picardDegreeMorphism f).hom.app (op T) x) t = picardDegree f x t :=
  rfl

/-- The subfunctor of the relative Picard functor `Pic_{X/S}` of the classes of **degree `d`**:
the sections whose degree function is identically `d`. For `d = 0` it is the kernel
`Pic⁰_{X/S} = ker(deg)` of the degree morphism. -/
noncomputable def picardDegreeSubfunctor (d : ℤ) : Subfunctor (picardFunctor f).obj where
  obj T := {x | ∀ t, picardDegree f x t = d}
  map g x hx t := by
    have h := picardDegree_map f g.unop x t
    rw [Quiver.Hom.op_unop] at h
    rw [h]
    exact hx _

lemma mem_picardDegreeSubfunctor_iff (d : ℤ) {T : Over S} (x : (picardFunctor f).obj.obj (op T)) :
    x ∈ (picardDegreeSubfunctor f d).obj (op T) ↔ ∀ t, picardDegree f x t = d :=
  Iff.rfl

/-- A class has degree `d` exactly when its image under the degree morphism is the constant
function `d`; for `d = 0` this says that it lies in `ker(deg)`. -/
lemma mem_picardDegreeSubfunctor_iff_picardDegreeMorphism [Flat f] (d : ℤ) {T : Over S}
    (x : (picardFunctor f).obj.obj (op T)) :
    x ∈ (picardDegreeSubfunctor f d).obj (op T) ↔
      ULift.down ((picardDegreeMorphism f).hom.app (op T) x) = LocallyConstant.const _ d := by
  rw [mem_picardDegreeSubfunctor_iff, LocallyConstant.ext_iff]
  rfl

end DegreeMorphism

section DegreePart

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

instance (d : ℤ) : Mono (picardFunctorDegreeι f d).hom :=
  (NatTrans.mono_iff_mono_app _).2 fun T ↦
    (mono_iff_injective _).2 (injective_picardFunctorDegreeι_app f d T.unop)

variable [IsProper f] [LocallyOfFinitePresentation f]

/-- **`Pic^d_{X/k}` is the subfunctor of classes of degree `d`**: the image of the monomorphism
`Pic^d_{X/k} ⟶ Pic_{X/k}` consists exactly of the classes whose degree function is identically
`d`. In particular `Pic⁰_{X/k} = ker(deg)`. -/
theorem range_picardFunctorDegreeι (d : ℤ) :
    Subfunctor.range (picardFunctorDegreeι f d).hom = picardDegreeSubfunctor f d := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 (picardFunctor f).property
  have hR : Presieve.IsSheaf (fppfTopology.over (Spec (.of k)))
      (Subfunctor.range (picardFunctorDegreeι f d).hom).toFunctor :=
    Presieve.isSheaf_iso _ (asIso (Subfunctor.toRange _))
      ((isSheaf_iff_isSheaf_of_type _ _).1 (picardFunctorDegree f d).property)
  apply le_antisymm
  · rintro ⟨T⟩ _ ⟨y, rfl⟩ t
    obtain ⟨Z, g, ⟨L, hL⟩, -, -, z, rfl⟩ := exists_flat_mem_of_mem_fppfTopology_over
      (Presheaf.imageSieve_mem _
        (toSheafify (fppfTopology.over (Spec (.of k))) (picardSubfunctorDegree f d).toFunctor)
        y) t
    rw [picardDegree_eq f _ g L.val (by
      rw [← picardFunctorDegreeι_app_toSheafify, hL]
      exact NatTrans.naturality_apply (picardFunctorDegreeι f d).hom g.op y) z]
    exact (mem_picardSubfunctorDegree_iff f d L.val).1 L.2 z
  · rintro ⟨T⟩ x hx
    refine (Subfunctor.isSheaf_iff _ hF).1 hR _ x ((fppfTopology.over _).superset_covering ?_
      (Presheaf.imageSieve_mem _ (toPicardFunctor f) x))
    rintro Z g ⟨L, hL⟩
    have hL' : L ∈ (picardSubfunctorDegree f d).obj (op Z) := by
      rw [mem_picardSubfunctorDegree_iff]
      intro z
      rw [← picardDegree_toPicardFunctor, hL, picardDegree_map]
      exact hx _
    exact ⟨(toSheafify (fppfTopology.over (Spec (.of k)))
      (picardSubfunctorDegree f d).toFunctor).app (op Z) ⟨L, hL'⟩, by
      rw [picardFunctorDegreeι_app_toSheafify, hL]⟩

instance (d : ℤ) : IsIso (Subfunctor.lift (picardFunctorDegreeι f d).hom
    (range_picardFunctorDegreeι f d).le) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  refine ⟨fun a b h ↦ injective_picardFunctorDegreeι_app f d T.unop (congrArg Subtype.val h),
    fun ⟨x, hx⟩ ↦ ?_⟩
  rw [← range_picardFunctorDegreeι] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

/-- **`Pic^d_{X/k}` is isomorphic to the subfunctor of `Pic_{X/k}` of classes of degree `d`**,
through the canonical morphism `Pic^d_{X/k} ⟶ Pic_{X/k}`; for `d = 0` this identifies
`Pic⁰_{X/k}` with `ker(deg)`. -/
noncomputable def picardFunctorDegreeIsoSubfunctor (d : ℤ) :
    (picardFunctorDegree f d).obj ≅ (picardDegreeSubfunctor f d).toFunctor :=
  asIso (Subfunctor.lift (picardFunctorDegreeι f d).hom (range_picardFunctorDegreeι f d).le)

@[reassoc (attr := simp)]
lemma picardFunctorDegreeIsoSubfunctor_hom_ι (d : ℤ) :
    (picardFunctorDegreeIsoSubfunctor f d).hom ≫ (picardDegreeSubfunctor f d).ι =
      (picardFunctorDegreeι f d).hom :=
  rfl

end DegreePart

end AlgebraicGeometry
