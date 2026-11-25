/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction

import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension

/-!
# Scalar functions and geometric evaluation for bounded condensed coefficients

Source: RefactorInstruction, Section 4, coefficient realization and geometric evaluation
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Geometric fiber data, separating the constructed functors from their naturality proofs.
Source: RefactorInstruction, Section 4, geometric fibers
(auxiliary; not a blueprint node). -/
structure CondensedQbarFiberData (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) where
  /-- Geometric evaluation, after choosing an algebraic closure above the point. -/
  fiber (U : X.ProEt) (x : U.left) :
    Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left) ⥤
        ModuleCat.{u + 1} (PadicAlgCl ℓ)
  fiber_additive (U : X.ProEt) (x : U.left) : (fiber U x).Additive
  fiber_colimits (U : X.ProEt) (x : U.left) : PreservesFiniteColimits (fiber U x)
  /-- The regular module has its ordinary one-dimensional coordinates. -/
  fiber_regular (U : X.ProEt) (x : U.left) :
    (fiber U x).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)) ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ

/-- The fiber data are actual algebraic-closure pullbacks and terminal evaluations.
Source: RefactorInstruction, Section 4, geometric fibers
(auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def condensedQbarCanonicalFiberData
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : CondensedQbarFiberData ℓ X where
  fiber U x := CondensedQbarGeometricEvaluation.fiber ℓ U.left x
  fiber_additive _ _ := inferInstance
  fiber_colimits _ _ := inferInstance
  fiber_regular U x := CondensedQbarGeometricEvaluation.fiberRegularCoordinates ℓ U.left x

/-- The remaining naturality and basis properties of the explicitly constructed
coefficient action and geometric fibers. All data have already been constructed.
Source: RefactorInstruction, Section 4, coefficient naturality and geometric comparison
(auxiliary; not a blueprint node). -/
structure CondensedQbarCoefficientProperties (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (d : CondensedQbarFiberData ℓ X) : Prop where
  /-- On the affine weakly contractible basis every scalar endomorphism is a function. -/
  scalar_surjective (U : X.ProEt) (hU : IsAffine U.left)
      (wU : PointLanWeaklyContractible U.left (Scheme.ProEt.mk (𝟙 U.left))) :
      Function.Surjective
        (condensedQbarScalar ℓ U.left)
  /-- Scalar actions commute with restriction along morphisms over X. -/
  scalar_restrict_mk {Y Z : Scheme.{u}}
      (f : Y ⟶ X) (g : Z ⟶ Y) [WeaklyEtale f] [WeaklyEtale g]
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y)
      (b : PadicAlgCl.finiteIntermediateFieldValued ℓ Z)
      (hab : b.1 = a.1.comp g.base.hom) :
    (condensedQbarRegularPullbackIso ℓ g).inv ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map
        (condensedQbarScalar ℓ Y a).asHom ≫ (condensedQbarRegularPullbackIso ℓ g).hom =
      (condensedQbarScalar ℓ Z b).asHom
  /-- In these coordinates a scalar acts by its value at the point. -/
  fiber_scalar (U : X.ProEt) (x : U.left)
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ U.left) :
    regularScalarValue (d.fiber U x) (d.fiber_regular U x)
      (condensedQbarScalar ℓ U.left a).asHom = a.1 x
  /-- Evaluating a module pulled back from X depends only on its base point. -/
  fiber_compare (U V : X.ProEt) (x : U.left) (y : V.left) (h : U.hom x = V.hom y) :
    Nonempty
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.hom ⋙
          d.fiber U x ≅
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.hom ⋙
          d.fiber V y)

/-- Naturality and basis properties for the fixed, explicitly constructed fiber data.
Source: RefactorInstruction, Section 4, coefficient naturality and geometric fibers
(auxiliary; not a blueprint node). -/
abbrev CondensedQbarCanonicalCoefficientProperties
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : Prop :=
  CondensedQbarCoefficientProperties ℓ X (condensedQbarCanonicalFiberData ℓ X)

/-- Coefficient functions, their restriction, and their geometric evaluation.
All data concern only regular modules and coefficient pullbacks; there is no
presentation, chosen module, or matrix in this interface.
Source: RefactorInstruction, Section 4, coefficient realization and geometric evaluation
(auxiliary; not a blueprint node). -/
structure CondensedQbarFunctionCoefficients (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) where
  /-- On the affine weakly contractible basis every scalar endomorphism is a function. -/
  scalar_surjective (U : X.ProEt) (hU : IsAffine U.left)
      (wU : PointLanWeaklyContractible U.left (Scheme.ProEt.mk (𝟙 U.left))) :
      Function.Surjective
        (condensedQbarScalar ℓ U.left)
  /-- Scalar actions commute with restriction along morphisms over X. -/
  scalar_restrict_mk {Y Z : Scheme.{u}}
      (f : Y ⟶ X) (g : Z ⟶ Y) [WeaklyEtale f] [WeaklyEtale g]
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y)
      (b : PadicAlgCl.finiteIntermediateFieldValued ℓ Z)
      (hab : b.1 = a.1.comp g.base.hom) :
    (condensedQbarRegularPullbackIso ℓ g).inv ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map
        (condensedQbarScalar ℓ Y a).asHom ≫ (condensedQbarRegularPullbackIso ℓ g).hom =
      (condensedQbarScalar ℓ Z b).asHom
  /-- Geometric evaluation, after choosing an algebraic closure above the point. -/
  fiber (U : X.ProEt) (x : U.left) :
    Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left) ⥤
        ModuleCat.{u + 1} (PadicAlgCl ℓ)
  fiber_additive (U : X.ProEt) (x : U.left) : (fiber U x).Additive
  fiber_colimits (U : X.ProEt) (x : U.left) : PreservesFiniteColimits (fiber U x)
  /-- The regular module has its ordinary one-dimensional coordinates. -/
  fiber_regular (U : X.ProEt) (x : U.left) :
    (fiber U x).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)) ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ
  /-- In these coordinates a scalar acts by its value at the point. -/
  fiber_scalar (U : X.ProEt) (x : U.left)
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ U.left) :
    regularScalarValue (fiber U x) (fiber_regular U x)
      (condensedQbarScalar ℓ U.left a).asHom = a.1 x
  /-- Evaluating a module pulled back from X depends only on its base point. -/
  fiber_compare (U V : X.ProEt) (x : U.left) (y : V.left) (h : U.hom x = V.hom y) :
    Nonempty
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.hom ⋙ fiber U x ≅
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.hom ⋙ fiber V y)

/-- Assemble coefficient properties over abstract fiber data, so dependent type
comparisons do not unfold the geometric construction in downstream presentation proofs.
Source: RefactorInstruction, Section 4, geometric fibers
(auxiliary; not a blueprint node). -/
noncomputable def CondensedQbarFunctionCoefficients.ofData
    {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} (d : CondensedQbarFiberData ℓ X)
    (p : CondensedQbarCoefficientProperties ℓ X d) : CondensedQbarFunctionCoefficients ℓ X where
  scalar_surjective := p.scalar_surjective
  scalar_restrict_mk := p.scalar_restrict_mk
  fiber := d.fiber
  fiber_additive := d.fiber_additive
  fiber_colimits := d.fiber_colimits
  fiber_regular := d.fiber_regular
  fiber_scalar := p.fiber_scalar
  fiber_compare := p.fiber_compare

/-- The scalar action is constructed, by sheafifying multiplication and transporting
through the explicit filtered-colimit ring realization.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable abbrev CondensedQbarFunctionCoefficients.scalar
    {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
    (_q : CondensedQbarFunctionCoefficients ℓ X) (U : X.ProEt) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ U.left →+*
      End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)) :=
  condensedQbarScalar ℓ U.left

/-- A comparison stated directly for scheme morphisms, avoiding reduction of the
site-object constructor inside a module inverse image.
Source: RefactorInstruction, Section 4, geometric evaluation
(auxiliary; not a blueprint node). -/
theorem CondensedQbarFunctionCoefficients.fiber_compare_mk
    {ℓ : ℕ} [Fact ℓ.Prime] {X Y Z : Scheme.{u}}
    (q : CondensedQbarFunctionCoefficients ℓ X)
    (f : Y ⟶ X) (g : Z ⟶ X) [WeaklyEtale f] [WeaklyEtale g]
    (x : Y) (y : Z) (h : f x = g y) :
    Nonempty
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f ⋙
          q.fiber (Scheme.ProEt.mk f) x ≅
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g ⋙
          q.fiber (Scheme.ProEt.mk g) y) :=
  q.fiber_compare (Scheme.ProEt.mk f) (Scheme.ProEt.mk g) x y h

set_option backward.isDefEq.respectTransparency false in
/-- Bounded functions on a finite disjoint union are tuples of bounded functions.
Glue the underlying continuous functions, and bound them by the finite compositum of
all bounds on the summands. The supremum over an empty family is the base field.
Source: RefactorInstruction, Section 4, coefficient realization;
Stacks Project, Tag 0F4P, finite disjoint unions
(auxiliary; not a blueprint node). -/
private lemma bounded_coproduct_bijective (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (I : Type u) [Finite I] (V : I → X.ProEt) (W : X.ProEt)
    (ι : ∀ i, V i ⟶ W) (e : (∐ fun i ↦ (V i).left) ≅ W.left)
    (hι : ∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.hom = (ι i).left)
    (hsec : ∀ F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)),
      Function.Bijective (fun s : F.obj.obj (op W) ↦
        fun i ↦ F.obj.map (ι i).op s)) :
    Function.Bijective (fun s : (CondensedQbarScalarConstruction.boundedP ℓ X).obj (op W) ↦
      fun i ↦ (CondensedQbarScalarConstruction.boundedP ℓ X).map (ι i).op s) := by
  classical
  let F := (sheafCompose (Scheme.ProEt.topology X) (forget RingCat.{u + 1})).obj
    (continuousMapRingSheaf X (PadicAlgCl ℓ))
  constructor
  · intro a b hab
    apply ULift.ext
    apply Subtype.ext
    have h : (ULift.up a.down.1 : F.obj.obj (op W)) = ULift.up b.down.1 := by
      apply (hsec F).1
      funext i
      exact congrArg (fun t ↦ ULift.up t.down.1) (congrFun hab i)
    exact congrArg ULift.down h
  · intro a
    obtain ⟨s, hs⟩ := (hsec F).2 (fun i ↦ ULift.up (a i).down.1)
    choose E hE ha using fun i ↦ (a i).down.property
    let _ (i : I) : FiniteDimensional ℚ_[ℓ] (E i) := hE i
    have hb : s.down ∈ PadicAlgCl.finiteIntermediateFieldValued ℓ W.left := by
      refine ⟨⨆ i, E i, inferInstance, ?_⟩
      intro x
      obtain ⟨z, rfl⟩ := (Scheme.homeoOfIso e).surjective x
      obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun i ↦ (V i).left)).surjective z
      rw [sigmaMk_mk]
      have hxy : e.hom (Sigma.ι (fun i ↦ (V i).left) i y) = (ι i).left y :=
        congrArg (fun f ↦ f y) (hι i)
      change s.down (e.hom (Sigma.ι (fun i ↦ (V i).left) i y)) ∈ _
      rw [hxy]
      have hv : s.down ((ι i).left y) = (a i).down.1 y :=
        congrArg (fun t ↦ t.down y) (congrFun hs i)
      rw [hv]
      exact (le_iSup E i) (ha i y)
    refine ⟨ULift.up ⟨s.down, hb⟩, ?_⟩
    funext i
    apply ULift.ext
    apply Subtype.ext
    exact congrArg ULift.down (congrFun hs i)

set_option backward.isDefEq.respectTransparency false in
/-- The bounded-function presheaf has unchanged sections on a weakly contractible affine.
Use finite-coproduct evaluation and the general unit-isomorphism implementation of the
weakly contractible sheafification lemma. Its finite-product hypothesis follows from
`bounded_coproduct_bijective`, without any component-quotient comparison.
Source: Bhatt--Scholze, Section 4.2, Lemma 4.2.13(1), sheafification argument;
RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
private lemma bounded_unit_isIso (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (U : X.ProEt) [IsAffine U.left] (wU : PointLanWeaklyContractible X U) :
    IsIso ((toSheafify (Scheme.ProEt.topology X)
      (CondensedQbarScalarConstruction.boundedP ℓ X)).app (op U)) := by
  apply unit_iso_of_refinement X Ab (CondensedQbarScalarConstruction.boundedP ℓ X)
    U inferInstance wU
  intro I _ V ha hw
  have hqc (i : I) : CompactSpace (V i).left := by let _ := ha i; infer_instance
  have hqs (i : I) : QuasiSeparatedSpace (V i).left := by let _ := ha i; infer_instance
  obtain ⟨W, ι, e, hι, _, _, _, ⟨hr⟩, _, hsec, _, _⟩ :=
    Scheme.ProEt.finite_coproduct_evaluation.{u, u, u + 1} X I V hqc hqs
  let c : Cofan V := Cofan.mk W ι
  have hc : IsColimit c := isColimitOfReflects (Scheme.ProEt.topology X).uliftYoneda
    ((Cofan.isColimitMapCoconeEquiv _ V c).symm hr)
  refine ⟨c, ⟨hc⟩, ?_⟩
  let P := CondensedQbarScalarConstruction.boundedP ℓ X
  let b := Equiv.ofBijective _ (bounded_coproduct_bijective ℓ X I V W ι e hι hsec)
  have ht : IsLimit (Fan.mk ((forget Ab).obj (P.obj (op W)))
      (fun i ↦ (forget Ab).map (P.map (ι i).op))) := by
    refine Fan.IsLimit.mk _ (fun s ↦ ↾fun x ↦ b.symm (fun i ↦ s.proj i x)) ?_ ?_
    · intro s i
      ext x
      exact congrFun (b.apply_symm_apply (fun i ↦ s.proj i x)) i
    · intro s m hm
      ext x
      apply b.injective
      change b (m x) = b (b.symm (fun i ↦ s.proj i x))
      rw [b.apply_symm_apply]
      funext i
      exact ConcreteCategory.congr_hom (hm i) x
  exact ⟨isLimitOfReflects (forget Ab)
    ((Fan.isLimitMapConeEquiv (forget Ab) _ _).symm ht)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The ring unit of monoidal sheafification is the sheafified presheaf unit.
This follows from the monoidal unit isomorphism and naturality of the adjunction unit.
Source: RefactorInstruction, Section 4, monoidal coefficient realization
(auxiliary; not a blueprint node). -/
private lemma sheafification_one (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :
    Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) ≫
      (MonObj.one (X := padicAlgClSheaf Y ℓ)).hom =
    MonObj.one (X := CondensedQbarScalarConstruction.boundedP ℓ Y) ≫
      toSheafify (Scheme.ProEt.topology Y)
        (CondensedQbarScalarConstruction.boundedP ℓ Y) := by
  let J := Scheme.ProEt.topology Y
  let L := presheafToSheaf J Ab.{u + 1}
  let R := sheafToPresheaf J Ab.{u + 1}
  let adj := sheafificationAdjunction J Ab.{u + 1}
  have he : Functor.LaxMonoidal.ε R =
      adj.homEquiv _ _ (Functor.OplaxMonoidal.η L) := rfl
  change Functor.LaxMonoidal.ε R ≫ R.map
    (Functor.LaxMonoidal.ε L ≫ L.map
      (MonObj.one (X := CondensedQbarScalarConstruction.boundedP ℓ Y))) = _
  rw [he, Adjunction.homEquiv_unit, Category.assoc, ← R.map_comp,
    Functor.Monoidal.η_ε_assoc]
  exact (adj.unit.naturality _).symm

set_option backward.isDefEq.respectTransparency false in
/-- A map out of the constant integer presheaf is determined by one at the final object.
Naturality transports that value to every object, and integer linearity determines
all other values.
Source: RefactorInstruction, Section 4, regular-module scalar realization
(auxiliary; not a blueprint node). -/
private lemma unit_presheaf_hom_ext (Y : Scheme.{u}) (P : Y.ProEtᵒᵖ ⥤ Ab.{u + 1})
    (f g : 𝟙_ (Y.ProEtᵒᵖ ⥤ Ab.{u + 1}) ⟶ P)
    (h : f.app (op (Scheme.ProEt.mk (𝟙 Y))) (ULift.up 1) =
      g.app (op (Scheme.ProEt.mk (𝟙 Y))) (ULift.up 1)) : f = g := by
  apply NatTrans.ext
  funext U
  have h1 : f.app U (ULift.up 1) = g.app U (ULift.up 1) := by
    let t : U.unop ⟶ Scheme.ProEt.mk (𝟙 Y) :=
      MorphismProperty.Over.homMk U.unop.hom
    have hf := ConcreteCategory.congr_hom (f.naturality t.op) (ULift.up 1)
    have hg := ConcreteCategory.congr_hom (g.naturality t.op) (ULift.up 1)
    exact hf.trans ((congrArg (P.map t.op) h).trans hg.symm)
  apply ConcreteCategory.hom_ext
  intro n
  have hn : n = n.down • (ULift.up (1 : ℤ) : ULift.{u + 1} ℤ) := by
    apply ULift.ext
    simp
  rw [hn, map_zsmul, map_zsmul, h1]

set_option backward.isDefEq.respectTransparency false in
/-- Every regular-module endomorphism of the bounded coefficient sheaf is a bounded scalar.
Lift its value at the unit on the final object through the invertible sheafification
unit. A regular-module map is determined by its composite with the ring unit. The
monoidal adjunction and naturality reduce equality of those composites to the lifted
value, since the source presheaf is the constant integer presheaf.
Source: RefactorInstruction, Section 4, regular-module scalar realization
(auxiliary; not a blueprint node). -/
private lemma sheafScalar_surjective (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [IsAffine Y] (wY : PointLanWeaklyContractible Y (Scheme.ProEt.mk (𝟙 Y))) :
    Function.Surjective (CondensedQbarScalarConstruction.sheafScalar ℓ Y) := by
  let J := Scheme.ProEt.topology Y
  let P := CondensedQbarScalarConstruction.boundedP ℓ Y
  let T := Scheme.ProEt.mk (𝟙 Y)
  let η := toSheafify J P
  have : IsAffine T.left := inferInstanceAs (IsAffine Y)
  have : IsIso (η.app (op T)) := bounded_unit_isIso ℓ Y T wY
  intro f
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (η.app (op T))).2
    (f.asHom.hom.hom.app (op T) (η.app (op T) (ULift.up 1)))
  refine ⟨a.down, ?_⟩
  apply End.ext
  apply (Mod.bijective_one_comp_hom (Mod.regular (padicAlgClSheaf Y ℓ))).1
  apply Sheaf.unit_hom_ext
  change Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
      ((MonObj.one (X := padicAlgClSheaf Y ℓ)).hom ≫
        (CondensedQbarScalarConstruction.sheafScalar ℓ Y a.down).asHom.hom.hom) =
    Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
      ((MonObj.one (X := padicAlgClSheaf Y ℓ)).hom ≫ f.asHom.hom.hom)
  rw [← Category.assoc, ← Category.assoc, sheafification_one]
  apply unit_presheaf_hom_ext Y
  change ((CondensedQbarScalarConstruction.sheafScalar ℓ Y a.down).asHom.hom.hom.app (op T))
      (η.app (op T) (ULift.up 1)) =
    f.asHom.hom.hom.app (op T) (η.app (op T) (ULift.up 1))
  change (sheafifyMap J (CondensedQbarScalarConstruction.boundedMul ℓ Y a.down)).app
    (op T) (η.app (op T) (ULift.up 1)) = _
  have hs := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      (CondensedQbarScalarConstruction.boundedMul ℓ Y a.down)) (op T)) (ULift.up 1)
  change η.app (op T) (ULift.up (1 *
    CondensedQbarScalarConstruction.restrictBounded ℓ Y T a.down)) =
    (sheafifyMap J (CondensedQbarScalarConstruction.boundedMul ℓ Y a.down)).app
      (op T) (η.app (op T) (ULift.up 1)) at hs
  rw [← hs, one_mul]
  convert ha using 1
  apply congrArg (η.app (op T))
  apply ULift.ext
  apply Subtype.ext
  ext x
  rfl

private lemma condensedQbarScalar_surjective (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) [IsAffine Y]
    (wY : PointLanWeaklyContractible Y (Scheme.ProEt.mk (𝟙 Y))) :
    Function.Surjective (condensedQbarScalar ℓ Y) := by
  let e := CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv e.inv.hom)
  let d := Mod.regularIsoOfIsIso e.inv.hom
  have : F.Full :=
    inferInstanceAs ((Mod.comapEquivalenceOfIsIso (inv e.inv.hom)).functor.Full)
  intro f
  obtain ⟨a, ha⟩ := sheafScalar_surjective ℓ Y wY
    (End.of (F.preimage (d.hom ≫ f.asHom ≫ d.inv)))
  refine ⟨a, ?_⟩
  change CondensedQbarScalarConstruction.transportedScalar ℓ Y e a = f
  apply End.ext
  unfold CondensedQbarScalarConstruction.transportedScalar
  change d.inv ≫ F.map (CondensedQbarScalarConstruction.sheafScalar ℓ Y a).asHom ≫ d.hom = f.asHom
  rw [congrArg End.asHom ha, F.map_preimage]
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private lemma fieldRegularCoordinates_apply (K : Type u) [Field K] [IsAlgClosed K]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (m : (CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))))) :
    CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ m =
      (((CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom) m).down := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma field_scalar (K : Type u) [Field K] [IsAlgClosed K]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ (Spec (.of K))) :
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ)
      ((CondensedQbarGeometricEvaluation.fieldFiber K ℓ).map
        (condensedQbarScalar ℓ (Spec (.of K)) a).asHom
          ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ).symm 1)) =
      a.1 default := by
  let Y := Spec (.of K)
  let T := Scheme.ProEt.mk (𝟙 Y)
  let P := CondensedQbarScalarConstruction.boundedP ℓ Y
  let η := toSheafify (Scheme.ProEt.topology Y) P
  let e := CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y
  let m : (CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :=
    e.inv.hom.hom.app (op T) (η.app (op T) (ULift.up 1))
  have hm : CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ m = 1 := by
    rw [fieldRegularCoordinates_apply]
    let d := ((sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).mapIso
      ((Mon.forget _).mapIso e)).app (op T)
    change ((CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
      ((CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ).inv.hom
        (d.hom (d.inv (η.app (op T) (ULift.up 1)))))).down = 1
    rw [Iso.inv_hom_id_apply]
    let d' := (Mon.forget _).mapIso (CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ)
    change ((CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
      (d'.inv (d'.hom (ULift.up 1)))).down = 1
    rw [Iso.hom_inv_id_apply]
    rfl
  have hm' : (CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ).symm 1 = m :=
    (LinearEquiv.symm_apply_eq _).mpr hm.symm
  rw [hm', fieldRegularCoordinates_apply]
  change (((CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom)
    (((condensedQbarScalar ℓ Y a).asHom.hom.hom.app (op T)) m)).down = _
  unfold condensedQbarScalar CondensedQbarScalarConstruction.transportedScalar
  let d := ((sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).mapIso
    ((Mon.forget _).mapIso e)).app (op T)
  change (((CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom)
    (((inv e.inv.hom ≫ (CondensedQbarScalarConstruction.sheafScalar ℓ Y a).asHom.hom ≫
      e.inv.hom).hom.app (op T)) m)).down = _
  rw [show inv e.inv.hom = e.hom.hom from
    (IsIso.inv_eq_of_hom_inv_id (show e.inv.hom ≫ e.hom.hom = 𝟙 _ from
      congrArg (fun f ↦ f.hom) e.inv_hom_id))]
  let σ := sheafifyMap (Scheme.ProEt.topology Y)
    (CondensedQbarScalarConstruction.boundedMul ℓ Y a)
  change ((CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
    ((CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ).inv.hom
      (d.hom (d.inv (σ.app (op T)
        (d.hom (d.inv (η.app (op T) (ULift.up 1))))))))).down = _
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  have hs := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (Scheme.ProEt.topology Y)
      (CondensedQbarScalarConstruction.boundedMul ℓ Y a)) (op T)) (ULift.up 1)
  change η.app (op T) (ULift.up (1 *
    CondensedQbarScalarConstruction.restrictBounded ℓ Y T a)) =
    σ.app (op T) (η.app (op T) (ULift.up 1)) at hs
  rw [← hs, one_mul]
  let d' := (Mon.forget _).mapIso (CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ)
  change ((CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
    (d'.inv (d'.hom (ULift.up a)))).down = _
  rw [Iso.hom_inv_id_apply]
  rfl

section FiberComparison
attribute [local irreducible] CondensedRing.upperStar
  CondensedQbarGeometricEvaluation.fieldFiber

private lemma fiber_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : Y) : Nonempty
    (CondensedQbarGeometricEvaluation.fiber ℓ X (f x) ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f ⋙
        CondensedQbarGeometricEvaluation.fiber ℓ Y x) := by
  let κs := X.residueField (f x)
  let κt := Y.residueField x
  let : Algebra κs (AlgebraicClosure κt) :=
    ((algebraMap κt (AlgebraicClosure κt)).comp (f.residueFieldMap x).hom).toAlgebra
  let ψ : AlgebraicClosure κs →ₐ[κs] AlgebraicClosure κt := IsAlgClosed.lift
  let ι := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hι : ι ≫ CondensedQbarGeometricEvaluation.geometricPoint X (f x) =
      CondensedQbarGeometricEvaluation.geometricPoint Y x ≫ f := by
    unfold CondensedQbarGeometricEvaluation.geometricPoint
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  obtain ⟨e⟩ := condensedQbar_fieldFiber_extension ℓ (AlgebraicClosure κs) (AlgebraicClosure κt)
    ψ.toRingHom
  unfold CondensedQbarGeometricEvaluation.fiber
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  exact ⟨Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((CondensedRing.upperStarComp Λ ι
        (CondensedQbarGeometricEvaluation.geometricPoint X (f x))).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar Λ) hι) ≪≫
        CondensedRing.upperStarComp Λ
          (CondensedQbarGeometricEvaluation.geometricPoint Y x) f) _ ≪≫
    Functor.associator _ _ _⟩

end FiberComparison

private lemma map_conjugate
    {C : Type v} [Category C] {D : Type w} [Category D]
    (E : C ⥤ D) {A B : C} (e : A ≅ B) (f : A ⟶ A) (q : B ⟶ B)
    (h : e.inv ≫ f ≫ e.hom = q) :
    (E.mapIso e).inv ≫ E.map f ≫ (E.mapIso e).hom = E.map q := by
  rw [Functor.mapIso_inv, Functor.mapIso_hom, ← E.map_comp, ← E.map_comp, h]

private lemma coordinates_conjugate
    {R : Type w} [CommRing R] {A B : ModuleCat.{z} R} (e : A ≅ B)
    (c : B ≃ₗ[R] R) (f : A ⟶ A) (q : B ⟶ B)
    (h : e.inv ≫ f ≫ e.hom = q) (b : R)
    (hb : c (q (c.symm 1)) = b) :
    (e.toLinearEquiv.trans c) (f ((e.toLinearEquiv.trans c).symm 1)) = b := by
  simp only [LinearEquiv.trans_apply, LinearEquiv.trans_symm,
    Iso.toLinearEquiv_apply, Iso.toLinearEquiv_symm, Iso.symm_hom]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, h]
  exact hb

private lemma regularScalarValue_comp
    {R : Type w} [CommRing R] {C : Type v} [Category C]
    {D : Type z} [Category D] (H : C ⥤ D) (E : D ⥤ ModuleCat.{u} R)
    {A : C} (c : (H ⋙ E).obj A ≃ₗ[R] R) (f : A ⟶ A) :
    regularScalarValue (H ⋙ E) c f = regularScalarValue E c (H.map f) := by
  unfold regularScalarValue
  rfl

private lemma regularScalarValue_conjugate
    {R : Type w} [CommRing R] {C : Type v} [Category C]
    (E : C ⥤ ModuleCat.{u} R) {A B : C} (e : A ≅ B)
    (c : E.obj B ≃ₗ[R] R) (f : A ⟶ A) (q : B ⟶ B)
    (h : e.inv ≫ f ≫ e.hom = q) :
    regularScalarValue E ((E.mapIso e).toLinearEquiv.trans c) f =
      regularScalarValue E c q := by
  rw [regularScalarValue_def, regularScalarValue_def]
  exact coordinates_conjugate (E.mapIso e) c _ _ (map_conjugate E e f q h) _ rfl

section FiberScalar
attribute [local irreducible] CondensedQbarGeometricEvaluation.fieldFiber
  CondensedRing.upperStar CondensedQbarGeometricEvaluation.fieldRegularCoordinates
attribute [local semireducible] CondensedQbarGeometricEvaluation.fiber
  CondensedQbarGeometricEvaluation.fiberRegularCoordinates

private lemma fiber_scalar (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (x : Y)
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    regularScalarValue (CondensedQbarGeometricEvaluation.fiber ℓ Y x)
      (CondensedQbarGeometricEvaluation.fiberRegularCoordinates ℓ Y x)
      (condensedQbarScalar ℓ Y a).asHom = a.1 x := by
  have hpoint : (CondensedQbarGeometricEvaluation.geometricPoint Y x) default = x :=
    Scheme.fromSpecResidueField_apply x _
  change regularScalarValue ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
    (CondensedQbarGeometricEvaluation.geometricPoint Y x)) ⋙
    (CondensedQbarGeometricEvaluation.fieldFiber (AlgebraicClosure (Y.residueField x)) ℓ))
    (((CondensedQbarGeometricEvaluation.fieldFiber (AlgebraicClosure (Y.residueField x)) ℓ).mapIso
    (condensedQbarRegularPullbackIso ℓ (CondensedQbarGeometricEvaluation.geometricPoint Y
    x))).toLinearEquiv.trans (CondensedQbarGeometricEvaluation.fieldRegularCoordinates
    (AlgebraicClosure (Y.residueField x)) ℓ))
    (condensedQbarScalar ℓ Y a).asHom = _
  rw [regularScalarValue_comp, regularScalarValue_conjugate
    (CondensedQbarGeometricEvaluation.fieldFiber (AlgebraicClosure (Y.residueField x)) ℓ)
    (condensedQbarRegularPullbackIso ℓ (CondensedQbarGeometricEvaluation.geometricPoint Y x))
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates (AlgebraicClosure (Y.residueField x))
    ℓ) _ _
    (condensedQbar_scalar_pullback ℓ (CondensedQbarGeometricEvaluation.geometricPoint Y x) a)]
  exact (regularScalarValue_def _ _ _).trans
    ((field_scalar _ ℓ (CondensedQbarScalarConstruction.boundedComp ℓ
      (CondensedQbarGeometricEvaluation.geometricPoint Y x).base.hom a)).trans
      (congrArg a.1 hpoint))

end FiberScalar

private lemma fibers_compare (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}
    (U V : X.ProEt) (x : U.left) (y : V.left) (h : U.hom x = V.hom y) :
    Nonempty (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.hom ⋙
        CondensedQbarGeometricEvaluation.fiber ℓ U.left x ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.hom ⋙
        CondensedQbarGeometricEvaluation.fiber ℓ V.left y) := by
  obtain ⟨eU⟩ := fiber_pullback ℓ U.hom x
  obtain ⟨eV⟩ := fiber_pullback ℓ V.hom y
  exact ⟨eU.symm ≪≫ eqToIso
    (congrArg (CondensedQbarGeometricEvaluation.fiber ℓ X) h) ≪≫ eV⟩

attribute [local semireducible] condensedQbarCanonicalFiberData

/-- Bounded condensed coefficients admit scalar realization and compatible geometric
fiber functors, independently of any module or presentation.

Source: RefactorInstruction, Section 4, coefficient realization and geometric-fiber
comparison, steps 2--3 of the finite-matrix argument
(auxiliary; not a blueprint node).

Proof in words: the explicit construction above realizes the bounded coefficient ring
on every scheme by the filtered colimit of its canonical finite-extension realizations.
Its scalar action is multiplication on the bounded-function presheaf, followed by
monoidal sheafification and transport through that constructed ring isomorphism. These
constructions and their ring laws are already proved above. To finish the scalar
properties, use the normalization of the finite-extension realizations on profinite
test functions. Their uniqueness makes them compatible with localization along every
small-site object U to X. The bounded-function presheaf unit and multiplication commute
with restriction, giving scalar_restrict_mk after passage to the filtered colimit.
For the bounded-function presheaf, finite disjoint unions give products: glue the
underlying continuous functions and use the finite compositum of their field bounds.
The general weakly contractible sheafification argument then shows that its unit is
invertible on affine weakly contractible objects. Lift an endomorphism's image of one
through this unit at the final object. The regular module is free on the monoidal
unit, and naturality transports the lifted value to every object, so the endomorphism
is sheafified multiplication by that bounded function. This proves scalar_surjective.

For fiber U x choose an algebraic closure of the residue field of x, pull modules to
its spectrum, and evaluate at the terminal object. The coefficient comparison there
identifies coefficient sections with Qbar_l. Transport the action through this
identification to obtain the stated module functor and fiber_regular. Inverse image
preserves finite colimits; evaluation on an algebraically closed field does so because
every pro-etale cover of the field splits. Colimits of module objects are created on
the underlying abelian sheaves. These facts give fiber_additive and fiber_colimits.
Naturality of coefficient realization identifies the action of a bounded function
with its point value, proving fiber_scalar. If two points have the same image in X,
choose a common algebraically closed overfield of their residue fields. The geometric
field extension comparison identifies both evaluated pullbacks from X with evaluation
at that common point, naturally in the module. This yields fiber_compare. No finite
presentation, matrix, corank, local constancy, or freeness assertion is used. Empty
objects have no point evaluations, and the scalar statement there uses the zero ring.
-/
theorem condensedQbar_canonical_coefficient_properties
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    CondensedQbarCanonicalCoefficientProperties ℓ X := by
  change CondensedQbarCoefficientProperties ℓ X
    { fiber := fun U x ↦ CondensedQbarGeometricEvaluation.fiber ℓ U.left x
      fiber_additive := fun _ _ ↦ inferInstance
      fiber_colimits := fun _ _ ↦ inferInstance
      fiber_regular := fun U x ↦
        CondensedQbarGeometricEvaluation.fiberRegularCoordinates ℓ U.left x }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U hU wU
    let := hU
    exact condensedQbarScalar_surjective ℓ U.left wU
  · intro Y Z f g _ _ a b hab
    exact (condensedQbar_scalar_pullback ℓ g a).trans
      (congrArg (fun b ↦ (condensedQbarScalar ℓ Z b).asHom) (Subtype.ext hab).symm)
  · intro U x a
    exact fiber_scalar ℓ U.left x a
  · exact fibers_compare ℓ

/-- Assemble the constructed scalar action, geometric fibers, regular coordinates,
and their proved additive and finite-colimit properties with coefficient naturality.
Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers
(auxiliary; not a blueprint node). -/
theorem exists_condensedQbar_function_coefficients
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (_hcoeff : Nonempty
      (Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
        Mon.mk (padicAlgClSheaf X ℓ))) :
    Nonempty (CondensedQbarFunctionCoefficients ℓ X) := by
  exact ⟨CondensedQbarFunctionCoefficients.ofData (condensedQbarCanonicalFiberData ℓ X)
    (condensedQbar_canonical_coefficient_properties ℓ X)⟩

end AlgebraicGeometry.ProEtale
