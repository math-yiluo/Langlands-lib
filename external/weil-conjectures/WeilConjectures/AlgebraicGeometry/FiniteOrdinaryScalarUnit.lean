/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.SixFunctors.Finite.Stalk

/-! # Finite direct image preserves ordinary scalar-extension units

Source: Stacks Project, Tag 03QP, finite direct image and its finite stalk formula.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private noncomputable abbrev moduleScalar
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A) :
    ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} A :=
  ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ

private noncomputable abbrev scalar {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (moduleScalar φ)

private noncomputable abbrev scalarAdj {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) (X : Scheme.{u}) :
    scalar φ X ⊣ Sheaf.restrictScalars X.smallEtaleTopology φ :=
  Sheaf.adjunction X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

private noncomputable def scalarStalkIso
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (moduleScalar φ).obj ((Scheme.pointSmallEtale x).sheafFiber.obj F) ≅
      (Scheme.pointSmallEtale x).sheafFiber.obj ((scalar φ X).obj F) :=
  letI : (moduleScalar φ).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} A) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  letI : IsIso ((Scheme.pointSmallEtale x).presheafFiber.map
      (toSheafify X.smallEtaleTopology (F.obj ⋙ moduleScalar φ))) :=
    (Scheme.pointSmallEtale x).W_isInvertedBy_presheafFiber _
      (X.smallEtaleTopology.W_toSheafify _)
  ((Scheme.pointSmallEtale x).presheafFiberCompIso
    (A := ModuleCat.{u + 1} R) (B := ModuleCat.{u + 1} A)
    (moduleScalar φ)).symm.app F.obj ≪≫
      asIso ((Scheme.pointSmallEtale x).presheafFiber.map
        (toSheafify X.smallEtaleTopology (F.obj ⋙ moduleScalar φ)))

private theorem scalarStalkIso_germ
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : X.Etale) (z : (Scheme.pointSmallEtale x).fiber.obj U) :
    (moduleScalar φ).map
        ((Scheme.pointSmallEtale x).toPresheafFiber U z F.obj) ≫
      (scalarStalkIso φ x F).hom =
    (toSheafify X.smallEtaleTopology (F.obj ⋙ moduleScalar φ)).app (op U) ≫
      (Scheme.pointSmallEtale x).toPresheafFiber U z ((scalar φ X).obj F).obj := by
  have : (moduleScalar φ).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  dsimp only [scalarStalkIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
  rw [← (Scheme.pointSmallEtale x).toPresheafFiber_presheafFiberCompIso_hom_app]
  simp only [Iso.app_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  exact (Scheme.pointSmallEtale x).toPresheafFiber_naturality
    (toSheafify X.smallEtaleTopology (F.obj ⋙ moduleScalar φ)) U z

private noncomputable def finiteScalarMap
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {D T : Scheme.{u}} (i : D ⟶ T)
    (F : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (scalar φ T).obj ((lowerStar (ModuleCat.{u + 1} R) i).obj F) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj ((scalar φ D).obj F) :=
  ⟨sheafifyLift T.smallEtaleTopology
    (Functor.whiskerLeft i.Etale.op
      (toSheafify D.smallEtaleTopology (F.obj ⋙ moduleScalar φ)))
    ((lowerStar (ModuleCat.{u + 1} A) i).obj ((scalar φ D).obj F)).property⟩

private theorem finiteScalarMap_sections
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {D T : Scheme.{u}} (i : D ⟶ T)
    (F : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} R)) (U : T.Etale) :
    (toSheafify T.smallEtaleTopology
      (((lowerStar (ModuleCat.{u + 1} R) i).obj F).obj ⋙
        moduleScalar φ)).app (op U) ≫
      (finiteScalarMap φ i F).hom.app (op U) =
    (toSheafify D.smallEtaleTopology (F.obj ⋙ moduleScalar φ)).app
      (op (i.Etale.obj U)) :=
  NatTrans.congr_app (toSheafify_sheafifyLift T.smallEtaleTopology _ _) (op U)

private theorem finiteScalarMap_stalk
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsFinite i]
    (F : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T)
    (t : Scheme.Hom.GeometricFiber i y) :
    (scalarStalkIso φ y ((lowerStar (ModuleCat.{u + 1} R) i).obj F)).hom ≫
        (Scheme.pointSmallEtale y).sheafFiber.map (finiteScalarMap φ i F) ≫
          stalkRestrict (ModuleCat.{u + 1} A) i y t ((scalar φ D).obj F) =
      (moduleScalar φ).map (stalkRestrict (ModuleCat.{u + 1} R) i y t F) ≫
        (scalarStalkIso φ t.1 F).hom := by
  let E := moduleScalar φ
  let p := Scheme.pointSmallEtale y
  have : E.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  apply (isColimitOfPreserves E
    (p.isColimitPresheafFiberCocone ((lowerStar (ModuleCat.{u + 1} R) i).obj F).obj)).hom_ext
  intro j
  let U := j.unop.1
  let z := j.unop.2
  change E.map (p.toPresheafFiber U z _) ≫ _ =
    E.map (p.toPresheafFiber U z _) ≫
      E.map (stalkRestrict (ModuleCat.{u + 1} R) i y t F) ≫
        (scalarStalkIso φ t.1 F).hom
  erw [reassoc_of% (scalarStalkIso_germ φ y
    ((lowerStar (ModuleCat.{u + 1} R) i).obj F) U z)]
  erw [reassoc_of% (p.toPresheafFiber_naturality (finiteScalarMap φ i F).hom U z)]
  erw [toPresheafFiber_stalkRestrict (ModuleCat.{u + 1} A) i y t
    ((scalar φ D).obj F) (p.fiber.elementsMk U z)]
  erw [← E.map_comp_assoc,
    toPresheafFiber_stalkRestrict (ModuleCat.{u + 1} R) i y t F (p.fiber.elementsMk U z)]
  erw [scalarStalkIso_germ]
  erw [← Category.assoc, finiteScalarMap_sections]

private theorem finiteScalarMap_isIso_stalk
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsFinite i]
    (F : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T) :
    IsIso ((Scheme.pointSmallEtale y).sheafFiber.map (finiteScalarMap φ i F)) := by
  let E := moduleScalar φ
  have : E.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).left_adjoint_additive
  let f := fun t : Scheme.Hom.GeometricFiber i y ↦
    (Scheme.pointSmallEtale t.1).sheafFiber.obj F
  let e := E.mapIso (stalkIsoPi (ModuleCat.{u + 1} R) i y F) ≪≫
    PreservesProduct.iso E f ≪≫ Pi.mapIso (fun t ↦ scalarStalkIso φ t.1 F)
  have he :
      (scalarStalkIso φ y ((lowerStar (ModuleCat.{u + 1} R) i).obj F)).hom ≫
          (Scheme.pointSmallEtale y).sheafFiber.map (finiteScalarMap φ i F) ≫
            (stalkIsoPi (ModuleCat.{u + 1} A) i y ((scalar φ D).obj F)).hom = e.hom := by
    apply Pi.hom_ext
    intro t
    simp only [e, Category.assoc, stalkIsoPi_hom, Pi.lift_comp_π, Iso.trans_hom,
      Functor.mapIso_hom, Pi.mapIso_hom_π, PreservesProduct.iso_hom,
      piComparison_comp_π_assoc]
    rw [← E.map_comp_assoc, Pi.lift_comp_π]
    exact finiteScalarMap_stalk φ i F y t
  have : IsIso
      ((scalarStalkIso φ y ((lowerStar (ModuleCat.{u + 1} R) i).obj F)).hom ≫
        (Scheme.pointSmallEtale y).sheafFiber.map (finiteScalarMap φ i F) ≫
          (stalkIsoPi (ModuleCat.{u + 1} A) i y ((scalar φ D).obj F)).hom) := by
    rw [he]
    infer_instance
  have := IsIso.of_isIso_comp_left
    (scalarStalkIso φ y ((lowerStar (ModuleCat.{u + 1} R) i).obj F)).hom
    ((Scheme.pointSmallEtale y).sheafFiber.map (finiteScalarMap φ i F) ≫
      (stalkIsoPi (ModuleCat.{u + 1} A) i y ((scalar φ D).obj F)).hom)
  exact IsIso.of_isIso_comp_right
    ((Scheme.pointSmallEtale y).sheafFiber.map (finiteScalarMap φ i F))
    (stalkIsoPi (ModuleCat.{u + 1} A) i y ((scalar φ D).obj F)).hom

private theorem finiteScalarMap_isIso
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsFinite i]
    (F : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsIso (finiteScalarMap φ i F) := by
  apply Scheme.isIso_of_isIso_sheafFiber_map
  intro s
  let p := Scheme.pointSmallEtale (T.algClosurePoint s)
  let e := p.uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} A)
  have := finiteScalarMap_isIso_stalk φ i F (T.algClosurePoint s)
  have h : IsIso ((p.ulift.{u + 1}).sheafFiber.map (finiteScalarMap φ i F) ≫
      e.hom.app _) := by
    rw [e.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((p.ulift.{u + 1}).sheafFiber.map (finiteScalarMap φ i F))
    (e.hom.app ((lowerStar (ModuleCat.{u + 1} A) i).obj ((scalar φ D).obj F)))

private theorem scalarAdj_unit_sections
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : X.Etale) :
    ((scalarAdj φ X).unit.app F).hom.app (op U) =
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).unit.app
          (F.obj.obj (op U)) ≫
        (ModuleCat.restrictScalars φ).map
          ((toSheafify X.smallEtaleTopology (F.obj ⋙ moduleScalar φ)).app (op U)) := by
  rw [show ((scalarAdj φ X).unit.app F).hom = _ from
    Sheaf.adjunction_unit_app_hom X.smallEtaleTopology
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ) F]
  rfl

private theorem finiteScalarMap_unit
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {D T : Scheme.{u}} (i : D ⟶ T)
    (F : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (scalarAdj φ T).unit.app ((lowerStar (ModuleCat.{u + 1} R) i).obj F) ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map (finiteScalarMap φ i F) =
      (lowerStar (ModuleCat.{u + 1} R) i).map ((scalarAdj φ D).unit.app F) ≫
        (lowerStarCompRestrictScalarsIso φ i).inv.app ((scalar φ D).obj F) := by
  ext U : 3
  obtain ⟨U⟩ := U
  change ((scalarAdj φ T).unit.app _).hom.app (op U) ≫
    (ModuleCat.restrictScalars φ).map ((finiteScalarMap φ i F).hom.app (op U)) =
    ((scalarAdj φ D).unit.app F).hom.app (op (i.Etale.obj U)) ≫ 𝟙 _
  rw [scalarAdj_unit_sections, scalarAdj_unit_sections, Category.comp_id, Category.assoc,
    ← Functor.map_comp, finiteScalarMap_sections]
  rfl

/-- Finite direct image carries an ordinary scalar-extension unit to an ordinary unit.
Source: Stacks Project, Tag 03QP, together with the sheaf tensor universal property.
(auxiliary; not a blueprint node).

Proof: Write E_X for sheafified sectionwise extension of scalars on X. Its adjunction
with restriction identifies η with an isomorphism E_D F → G, by the given ordinary
Hom bijections and uniqueness of representing objects. Take the mate of the
restriction/direct-image comparison to obtain E_T(i_*F) → i_*(E_D F). It is invertible:
on every geometric stalk the finite-stalk formula identifies it with extension of
scalars commuting with a finite product of modules. Finite products are finite direct
sums and extension of scalars preserves these. The identification is normalized on
pure tensors, so geometric-stalk conservativity applies to the actual mate. Compose
with i_* of the isomorphism E_D F → G. Its adjunction transpose is precisely i_*(η)
followed by the inverse restriction comparison, by the mate unit equation. The
ordinary scalar adjunction therefore supplies the displayed Hom bijections. This
also covers the empty fibre and the zero coefficient rings. -/
theorem finite_ordinary_scalar_unit
    (T : Scheme.{u}) {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {D : Scheme.{u}} (i : D ⟶ T) [IsFinite i]
    (F : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} A))
    (η : F ⟶ (Sheaf.restrictScalars D.smallEtaleTopology φ).obj G)
    (hη : ∀ H : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} A),
      Function.Bijective (fun f : G ⟶ H ↦
        η ≫ (Sheaf.restrictScalars D.smallEtaleTopology φ).map f)) :
    ∀ H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      Function.Bijective (fun f : (lowerStar (ModuleCat.{u + 1} A) i).obj G ⟶ H ↦
        ((lowerStar (ModuleCat.{u + 1} R) i).map η ≫
          (lowerStarCompRestrictScalarsIso φ i).inv.app G) ≫
            (Sheaf.restrictScalars T.smallEtaleTopology φ).map f) := by
  let aD := scalarAdj φ D
  let aT := scalarAdj φ T
  let rD := Sheaf.restrictScalars D.smallEtaleTopology φ
  let rT := Sheaf.restrictScalars T.smallEtaleTopology φ
  let pR := lowerStar (ModuleCat.{u + 1} R) i
  let pA := lowerStar (ModuleCat.{u + 1} A) i
  let e := (aD.homEquiv F G).symm η
  have he : aD.unit.app F ≫ rD.map e = η :=
    (aD.homEquiv F G).apply_symm_apply η
  have : IsIso e := by
    apply isIso_of_coyoneda_map_bijective
    intro H
    constructor
    · intro f g h
      apply (hη H).1
      have hf := congrArg (aD.homEquiv F H) h
      simpa only [aD.homEquiv_naturality_right,
        show aD.homEquiv F G e = η from he] using hf
    · intro f
      obtain ⟨g, hg⟩ := (hη H).2 ((aD.homEquiv F H) f)
      refine ⟨g, (aD.homEquiv F H).injective ?_⟩
      change aD.unit.app F ≫ rD.map (e ≫ g) = _
      rw [rD.map_comp, ← Category.assoc, he]
      exact hg
  have := finiteScalarMap_isIso φ i F
  let k := finiteScalarMap φ i F ≫ pA.map e
  have : IsIso k := inferInstance
  have hk : aT.unit.app (pR.obj F) ≫ rT.map k =
      pR.map η ≫ (lowerStarCompRestrictScalarsIso φ i).inv.app G := by
    dsimp only [k]
    rw [rT.map_comp, ← Category.assoc, finiteScalarMap_unit]
    -- The restriction comparison is the identity, since both functors are sectionwise.
    change (pR.map (aD.unit.app F) ≫ 𝟙 _) ≫ pR.map (rD.map e) = pR.map η ≫ 𝟙 _
    rw [Category.comp_id, Category.comp_id, ← pR.map_comp, he]
  intro H
  have hb := ((aT.homEquiv (pR.obj F) H).bijective).comp
    ((isIso_iff_coyoneda_map_bijective k).mp inferInstance H)
  convert hb using 1
  funext f
  change (pR.map η ≫ (lowerStarCompRestrictScalarsIso φ i).inv.app G) ≫ rT.map f =
    aT.unit.app (pR.obj F) ≫ rT.map (k ≫ f)
  rw [rT.map_comp, ← Category.assoc, hk]

end AlgebraicGeometry.Etale
