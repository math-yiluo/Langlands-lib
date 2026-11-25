/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category

/-!
# The Galois point and larger geometric points of the spectrum of a field

Let `K` be a field, `Ks` a separable closure of `K` and `Ω` a separably closed field
containing `Ks`. Every `K`-morphism from `Spec Ω` to an étale `K`-scheme factors uniquely
through `Spec Ω ⟶ Spec Ks`, because the residue fields of an étale `K`-scheme are finite
separable over `K`. Hence the geometric point `Spec Ω ⟶ Spec K` and the Galois point
`AlgebraicGeometry.Scheme.galoisPoint K Ks` have isomorphic fibre functors, and the stalk
functors at these two points are isomorphic, compatibly with germs and with the Galois action.

## Main definitions and statements

- `AlgebraicGeometry.Scheme.galoisPointIso`: the isomorphism of points
  `galoisPoint K Ks ≅ (pointSmallEtale (Spec Ω ⟶ Spec K)).ulift`.
- `AlgebraicGeometry.Scheme.galoisPointSheafFiberIso`: the induced isomorphism of stalk
  functors on abelian sheaves, with its germ description
  `AlgebraicGeometry.Scheme.galoisPointSheafFiberIso_hom_app_toPresheafFiber`.
- `AlgebraicGeometry.Scheme.galoisPointSheafFiberIso_presheafFiberAct`: under this
  isomorphism, `σ ∈ Gal(Ks/K)` acts on germs at `Spec Ω` by changing the lift by any
  automorphism of `Ω` extending `σ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : Point.{u} J)
  (A : Type*) [Category* A] [HasColimitsOfSize.{u + 1, u + 1} A]

/-- The germ description of `CategoryTheory.GrothendieckTopology.Point.uliftSheafFiberIso`:
it sends the germ at a lifted point `ULift.up x` to the germ at `x`. -/
lemma toPresheafFiber_uliftSheafFiberIso_hom_app (F : Sheaf J A) (X : C) (x : Φ.fiber.obj X) :
    haveI : HasColimitsOfSize.{u, u} A := hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A
    (Φ.ulift.{u + 1}).toPresheafFiber X (ULift.up x) F.obj ≫
        (Φ.uliftSheafFiberIso.{u + 1} A).hom.app F =
      Φ.toPresheafFiber X x F.obj := by
  simp only [uliftSheafFiberIso, uliftPresheafFiberIso, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.Final.colimIso, NatIso.ofComponents_hom_app,
    Functor.Final.colimitIso, toPresheafFiber]
  have : HasColimitsOfSize.{u, u} A := hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A
  rw [asIso_hom]
  exact colimit.ι_pre ((Functor.Elements.π Φ.fiber).op ⋙ F.obj)
    (Functor.Elements.uliftEquivalence.{u + 1} Φ.fiber).functor.op
    (op (Functor.elementsMk _ X (ULift.up x)))

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Scheme

/-- Precomposition with `Spec L ⟶ Spec M` for a field extension `L → M` is injective on
morphisms `Spec M ⟶ Y`. -/
lemma specMap_comp_injective {L M : Type u} [Field L] [Field M] (f : L →+* M)
    (Y : Scheme.{u}) :
    Function.Injective fun y : Spec (.of L) ⟶ Y ↦ Spec.map (CommRingCat.ofHom f) ≫ y := by
  intro y₁ y₂ h
  obtain ⟨⟨p₁, φ₁⟩, rfl⟩ := (SpecToEquivOfField L Y).symm.surjective y₁
  obtain ⟨⟨p₂, φ₂⟩, rfl⟩ := (SpecToEquivOfField L Y).symm.surjective y₂
  have h' : (SpecToEquivOfField M Y).symm ⟨p₁, φ₁ ≫ CommRingCat.ofHom f⟩ =
      (SpecToEquivOfField M Y).symm ⟨p₂, φ₂ ≫ CommRingCat.ofHom f⟩ := by
    simpa [SpecToEquivOfField, Spec.map_comp] using h
  obtain ⟨e, he⟩ := SpecToEquivOfField_eq_iff.1 ((SpecToEquivOfField M Y).symm.injective h')
  dsimp only at e he
  subst e
  congr 2
  ext a
  apply f.injective
  simpa using congr($(he).hom a)

/-- The residue fields of an étale `K`-scheme are separable over `K`. -/
lemma isSeparable_residueFieldAlgebraMap_of_etale {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K)) [Etale f] (p : Y) :
    letI : Algebra K (Y.residueField p) := (f.residueFieldAlgebraMap p).toAlgebra
    Algebra.IsSeparable K (Y.residueField p) := by
  let : Algebra K (Y.residueField p) := (f.residueFieldAlgebraMap p).toAlgebra
  have hb : Function.Bijective
      (Hom.residueFieldAlgebraMap (𝟙 (Spec (.of K))) (f.base p)) := by
    simpa using Hom.bijective_residueFieldAlgebraMap_of_comp_eq_id (𝟙 (Spec (.of K)))
      (𝟙 _) (Category.id_comp _) (f.base p)
  have h := Hom.residueFieldAlgebraMap_comp f (𝟙 (Spec (.of K))) p
  rw [Category.comp_id] at h
  have : (f.residueFieldAlgebraMap p).Etale := by
    rw [h]
    exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hb)
      (f.etale_residueFieldMap p)
  have : Algebra.Etale K (Y.residueField p) := RingHom.etale_algebraMap.mp this
  exact (Algebra.FormallyEtale.iff_isSeparable K (Y.residueField p)).mp inferInstance

section comparison

variable (K : Type u) [Field K] (Ks : Type u) [Field Ks] [Algebra K Ks]
  (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsScalarTower K Ks Ω]

/-- The morphism `Spec Ω ⟶ Spec Ks` of geometric points of `Spec K`. -/
noncomputable def specAlgebraMapOverHom :
    Over.mk (specAlgebraMap K Ω) ⟶ Over.mk (specAlgebraMap K Ks) :=
  Over.homMk (specAlgebraMap Ks Ω) (by
    dsimp only [specAlgebraMap, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

@[simp]
lemma specAlgebraMapOverHom_left :
    (specAlgebraMapOverHom K Ks Ω).left = specAlgebraMap Ks Ω :=
  rfl

variable [IsSepClosed Ks] [Algebra.IsSeparable K Ks]

variable {K Ks Ω} in
/-- Every `K`-morphism `Spec Ω ⟶ X` to an étale `K`-scheme factors through `Spec Ks`. -/
lemma exists_specAlgebraMap_comp_eq (X : (Spec (.of K)).Etale) (y : Spec (.of Ω) ⟶ X.left)
    (hy : y ≫ X.hom = specAlgebraMap K Ω) :
    ∃ z : Spec (.of Ks) ⟶ X.left, specAlgebraMap Ks Ω ≫ z = y := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (SpecToEquivOfField Ω X.left).symm.surjective y
  have : Etale X.hom := X.prop
  have ha : Spec.map (CommRingCat.ofHom (X.hom.residueFieldAlgebraMap p)) =
      X.left.fromSpecResidueField p ≫ X.hom :=
    X.hom.specMap_residueFieldAlgebraMap p
  have hw : CommRingCat.ofHom (X.hom.residueFieldAlgebraMap p) ≫ φ =
      CommRingCat.ofHom (algebraMap K Ω) := by
    rw [← Spec.map_inj, Spec.map_comp, ha, ← Category.assoc]
    exact hy
  let : Algebra K (X.left.residueField p) := (X.hom.residueFieldAlgebraMap p).toAlgebra
  have : Algebra.IsSeparable K (X.left.residueField p) :=
    isSeparable_residueFieldAlgebraMap_of_etale X.hom p
  let φ' : X.left.residueField p →ₐ[K] Ω := { φ.hom with commutes' r := congr($(hw).hom r) }
  let j : Ks →ₐ[K] separableClosure K Ω :=
    { toFun t := ⟨algebraMap Ks Ω t,
        (Algebra.IsSeparable.isSeparable K t).map
          (IsScalarTower.toAlgHom K Ks Ω) (algebraMap Ks Ω).injective⟩
      map_one' := Subtype.ext (map_one (algebraMap Ks Ω))
      map_mul' a b := Subtype.ext (map_mul (algebraMap Ks Ω) a b)
      map_zero' := Subtype.ext (map_zero (algebraMap Ks Ω))
      map_add' a b := Subtype.ext (map_add (algebraMap Ks Ω) a b)
      commutes' t := Subtype.ext (IsScalarTower.algebraMap_apply K Ks Ω t).symm }
  let c : Ks ≃ₐ[K] separableClosure K Ω := AlgEquiv.ofBijective j
    (Algebra.IsAlgebraic.algHom_bijective₂ j
      (IsSepClosed.lift : separableClosure K Ω →ₐ[K] Ks)).1
  let φs : X.left.residueField p →ₐ[K] separableClosure K Ω :=
    φ'.codRestrict (separableClosure K Ω).toSubalgebra fun a ↦
      (Algebra.IsSeparable.isSeparable K a).map φ' φ'.injective
  let ψ : X.left.residueField p →ₐ[K] Ks := c.symm.toAlgHom.comp φs
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.left.fromSpecResidueField p, ?_⟩
  change _ = Spec.map φ ≫ X.left.fromSpecResidueField p
  rw [← Category.assoc, specAlgebraMap, ← Spec.map_comp]
  congr 2
  ext a
  exact congrArg Subtype.val (c.apply_symm_apply (φs a))

variable [IsSepClosed Ω]

/-- Composition with `Spec Ω ⟶ Spec Ks` identifies the fibre functors of the geometric points
`Spec Ks ⟶ Spec K` and `Spec Ω ⟶ Spec K` of the small étale site of `Spec K`. -/
noncomputable def pointSmallEtaleFiberIso :
    (pointSmallEtale (specAlgebraMap K Ks)).fiber ≅
      (pointSmallEtale (specAlgebraMap K Ω)).fiber :=
  have : IsIso (Functor.whiskerLeft (Etale.forget (Spec (.of K)))
      (coyoneda.map (specAlgebraMapOverHom K Ks Ω).op)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    refine (isIso_iff_bijective _).2 ⟨?_, ?_⟩
    · intro y₁ y₂ h
      refine Over.OverMorphism.ext (specMap_comp_injective (algebraMap Ks Ω) X.left ?_)
      exact congrArg CommaMorphism.left h
    · intro y
      obtain ⟨z, hz⟩ := exists_specAlgebraMap_comp_eq (Ks := Ks) X y.left (Over.w y)
      refine ⟨Over.homMk z ?_, Over.OverMorphism.ext hz⟩
      refine specMap_comp_injective (algebraMap Ks Ω) _ ?_
      dsimp only
      rw [← Category.assoc]
      erw [hz]
      exact (Over.w y).trans (Over.w (specAlgebraMapOverHom K Ks Ω)).symm
  asIso (Functor.whiskerLeft (Etale.forget (Spec (.of K)))
      (coyoneda.map (specAlgebraMapOverHom K Ks Ω).op))

@[simp]
lemma pointSmallEtaleFiberIso_hom_app {X : (Spec (.of K)).Etale}
    (x : (pointSmallEtale (specAlgebraMap K Ks)).fiber.obj X) :
    (pointSmallEtaleFiberIso K Ks Ω).hom.app X x = specAlgebraMapOverHom K Ks Ω ≫ x :=
  rfl


/-- The Galois point `galoisPoint K Ks` is isomorphic to the (universe-lifted) geometric point
`Spec Ω ⟶ Spec K`, for any separably closed `Ω` containing `Ks`. -/
noncomputable def galoisPointIso :
    galoisPoint K Ks ≅ (pointSmallEtale (specAlgebraMap K Ω)).ulift.{u + 1} :=
  GrothendieckTopology.Point.isoMk
    (Functor.isoWhiskerRight (pointSmallEtaleFiberIso K Ks Ω) uliftFunctor.{u + 1})

/-- The stalk functor at the Galois point `galoisPoint K Ks` is isomorphic to the stalk functor
at the geometric point `Spec Ω ⟶ Spec K`, for any separably closed `Ω` containing `Ks`. On germs
it is given by composition with `Spec Ω ⟶ Spec Ks`
(`AlgebraicGeometry.Scheme.galoisPointSheafFiberIso_hom_app_toPresheafFiber`). -/
noncomputable def galoisPointSheafFiberIso :
    (galoisPoint K Ks).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (pointSmallEtale (specAlgebraMap K Ω)).sheafFiber :=
  GrothendieckTopology.Point.sheafFiberIso (galoisPointIso K Ks Ω) ≪≫
    (pointSmallEtale (specAlgebraMap K Ω)).uliftSheafFiberIso.{u + 1} AddCommGrpCat.{u + 1}

lemma galoisPointSheafFiberIso_hom_app_toPresheafFiber
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (X : (Spec (.of K)).Etale) (x : (galoisPoint K Ks).fiber.obj X) :
    (galoisPoint K Ks).toPresheafFiber X x F.obj ≫ (galoisPointSheafFiberIso K Ks Ω).hom.app F =
      (pointSmallEtale (specAlgebraMap K Ω)).toPresheafFiber X
        (specAlgebraMapOverHom K Ks Ω ≫ x.down) F.obj := by
  have h : (galoisPoint K Ks).toPresheafFiber X x F.obj ≫
      (GrothendieckTopology.Point.sheafFiberIso (galoisPointIso K Ks Ω)).hom.app F =
      ((pointSmallEtale (specAlgebraMap K Ω)).ulift.{u + 1}).toPresheafFiber X
        (ULift.up (specAlgebraMapOverHom K Ks Ω ≫ x.down)) F.obj := by
    simp [GrothendieckTopology.Point.sheafFiberIso, galoisPointIso]
  rw [galoisPointSheafFiberIso, Iso.trans_hom, NatTrans.comp_app, reassoc_of% h,
    GrothendieckTopology.Point.toPresheafFiber_uliftSheafFiberIso_hom_app]

lemma galoisPointSheafFiberIso_hom_app_toPresheafFiber_apply
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (X : (Spec (.of K)).Etale) (x : (galoisPoint K Ks).fiber.obj X) (z : F.obj.obj (op X)) :
    (galoisPointSheafFiberIso K Ks Ω).hom.app F ((galoisPoint K Ks).toPresheafFiber X x F.obj z) =
      (pointSmallEtale (specAlgebraMap K Ω)).toPresheafFiber X
        (specAlgebraMapOverHom K Ks Ω ≫ x.down) F.obj z :=
  ConcreteCategory.congr_hom (galoisPointSheafFiberIso_hom_app_toPresheafFiber K Ks Ω F X x) z

lemma galoisPointSheafFiberIso_inv_app_toPresheafFiber_apply
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (X : (Spec (.of K)).Etale) (y : (pointSmallEtale (specAlgebraMap K Ks)).fiber.obj X)
    (z : F.obj.obj (op X)) :
    (galoisPointSheafFiberIso K Ks Ω).inv.app F
        ((pointSmallEtale (specAlgebraMap K Ω)).toPresheafFiber X
          (specAlgebraMapOverHom K Ks Ω ≫ y) F.obj z) =
      (galoisPoint K Ks).toPresheafFiber X (ULift.up y) F.obj z := by
  rw [← galoisPointSheafFiberIso_hom_app_toPresheafFiber_apply K Ks Ω F X (ULift.up y) z]
  exact Iso.hom_inv_id_apply ((galoisPointSheafFiberIso K Ks Ω).app F) _

variable {K Ks Ω} in
/-- Every element of the fibre at `Spec Ω` comes from a unique element of the fibre at
`Spec Ks`. -/
lemma exists_specAlgebraMapOverHom_comp_eq {X : (Spec (.of K)).Etale}
    (x : (pointSmallEtale (specAlgebraMap K Ω)).fiber.obj X) :
    ∃ y : (pointSmallEtale (specAlgebraMap K Ks)).fiber.obj X,
      specAlgebraMapOverHom K Ks Ω ≫ y = x := by
  refine ⟨(pointSmallEtaleFiberIso K Ks Ω).inv.app X x, ?_⟩
  exact ConcreteCategory.congr_hom ((pointSmallEtaleFiberIso K Ks Ω).inv_hom_id_app X) x

/-- Under `AlgebraicGeometry.Scheme.galoisPointSheafFiberIso`, the action of `σ ∈ Gal(Ks/K)`
on the stalk at the Galois point becomes, on germs at `Spec Ω`, the change of the lift by any
automorphism `τ` of `Ω` extending `σ`. -/
lemma galoisPointSheafFiberIso_presheafFiberAct
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (σ : Gal(Ks/K))
    (τ : Ω ≃ₐ[K] Ω)
    (hτ : (algebraMap Ks Ω).comp σ.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω))
    (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale (specAlgebraMap K Ω)).fiber.obj X)
    (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
    (z : F.obj.obj (op X)) :
    (galoisPointSheafFiberIso K Ks Ω).hom.app F
        ((galoisPoint K Ks).presheafFiberAct (galoisPointAct K Ks) F.obj σ
          ((galoisPointSheafFiberIso K Ks Ω).inv.app F
            ((pointSmallEtale (specAlgebraMap K Ω)).toPresheafFiber X x F.obj z))) =
      (pointSmallEtale (specAlgebraMap K Ω)).toPresheafFiber X x' F.obj z := by
  obtain ⟨y, rfl⟩ := exists_specAlgebraMapOverHom_comp_eq (Ks := Ks) x
  have h : specAlgebraMapOverHom K Ks Ω ≫ ((galoisPointAct K Ks σ).asHom.app X (ULift.up y)).down =
      x' := by
    apply Over.OverMorphism.ext
    rw [hx]
    change specAlgebraMap Ks Ω ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ y.left =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ specAlgebraMap Ks Ω ≫ y.left
    simp only [specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
  rw [galoisPointSheafFiberIso_inv_app_toPresheafFiber_apply,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberAct_apply,
    galoisPointSheafFiberIso_hom_app_toPresheafFiber_apply, h]

end comparison

end AlgebraicGeometry.Scheme
