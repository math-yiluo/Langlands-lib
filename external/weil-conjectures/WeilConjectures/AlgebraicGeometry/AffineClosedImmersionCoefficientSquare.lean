/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.AffineQuotientRestrictedIso

/-! # Affine coordinates for the closed-immersion coefficient morphism

Source: Stacks Project, Tags 01I9 and 0BQZ. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem surjective_quotient_coordinates {A : Type u} [CommRing A]
    (I : Ideal A) (f : ModuleCat.of A A ⟶ ModuleCat.of A (A ⧸ I))
    (hf : Function.Surjective f) :
    ∃ c : ModuleCat.of A (A ⧸ I) ≅ ModuleCat.of A (A ⧸ I),
      f ≫ c.hom = ModuleCat.ofHom I.mkQ := by
  have hmul (x : A) : f x = (Ideal.Quotient.mk I x) * f 1 := by
    simpa only [smul_eq_mul, mul_one, Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using
      f.hom.map_smul x 1
  obtain ⟨x, hx⟩ := hf 1
  have hu : IsUnit (f 1) := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨Ideal.Quotient.mk I x, by rw [mul_comm, ← hmul, hx]⟩
  let e := Units.mulRightLinearEquiv A hu.unit
  refine ⟨e.symm.toModuleIso, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change e.symm (f y) = Ideal.Quotient.mk I y
  apply e.injective
  rw [e.apply_symm_apply]
  exact hmul y

open Scheme.Modules in
private theorem restrict_equivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    (restrictFunctor e.hom).IsEquivalence := by
  let E : Y.Modules ≌ X.Modules := CategoryTheory.Equivalence.mk
    (restrictFunctor e.hom) (restrictFunctor e.inv)
    (restrictFunctorId.symm ≪≫ restrictFunctorCongr e.inv_hom_id.symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId)
  exact E.isEquivalence_functor

private theorem coefficient_epi {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] : Epi (SheafOfModules.unitToPushforwardObjUnit
      i.toRingCatSheafHom) := by
  let a := SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  have hlocal : TopCat.Presheaf.IsLocallySurjective
      ((Scheme.Modules.toPresheaf Y).map a) := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro W y x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    obtain ⟨z, hz⟩ := i.app_surjective V hV
      (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
        (CategoryTheory.homOfLE hVW).op y)
    exact ⟨V, hVW, ⟨z, hz⟩, hxV⟩
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf Y.ringCatSheaf).map a) := hlocal
  exact (SheafOfModules.toSheaf Y.ringCatSheaf).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

private theorem quotient_presentation {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (U : Y.affineOpens) :
    ∃ e : (i ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)),
    i ∣_ U.1 ≫ U.1.toSpecΓ =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (i.ker.ideal U))) := by
  let g := i ∣_ U.1 ≫ U.2.isoSpec.hom
  let φ := (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ g.appTop
  have hφ : φ = i.app U.1 ≫ (i ⁻¹ᵁ U.1).topIso.inv := by
    change (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
      (i ∣_ U.1 ≫ U.2.isoSpec.hom).appTop = _
    rw [Scheme.Hom.comp_appTop, U.2.isoSpec_hom_appTop]
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
      Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Scheme.Hom.appLE_eq_app]
  have hker : RingHom.ker φ.hom = i.ker.ideal U := by
    rw [hφ, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (i ⁻¹ᵁ U.1).topIso.inv).1,
      Scheme.Hom.ker_apply]
  have hsurj : Function.Surjective φ := by
    rw [hφ]
    exact (ConcreteCategory.bijective_of_isIso (i ⁻¹ᵁ U.1).topIso.inv).2.comp
      (i.app_surjective U.1 U.2)
  have : IsAffine (i ⁻¹ᵁ U.1).toScheme := U.2.preimage i
  let er := RingEquiv.ofBijective φ.hom.kerLift
    ⟨φ.hom.kerLift_injective, Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj⟩
  let e := Scheme.isoSpec (i ⁻¹ᵁ U.1).toScheme ≪≫ Scheme.Spec.mapIso
    er.toCommRingCatIso.op
  have he : g = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (RingHom.ker φ.hom))) := by
    dsimp [e, er]
    simp only [Iso.op_hom,
      Quiver.Hom.unop_op, Category.assoc, ← Spec.map_comp]
    change g = (i ⁻¹ᵁ U.1).toScheme.isoSpec.hom ≫ Spec.map φ
    simp only [Scheme.isoSpec, asIso_hom, Spec.map_comp,
      ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, φ]
    simp
  have hex : ∃ e : (i ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of ((Γ(Y, U.1) : Type u) ⧸ RingHom.ker φ.hom)),
      g = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom))) :=
    ⟨e, he⟩
  rw [hker] at hex
  exact hex

/-- On an affine chart the closed-immersion unit is the sheafified quotient map.
Source: Stacks Project, Tag 01I9, Lemma 26.7.3(2), and Tag 0BQZ,
Lemma 48.15.5, the coefficient map in its proof.
(blueprint: lem-sc-affine-closed-immersion-coefficient-square).

Proof: Put A = Gamma(Y,U) and I = ker(i)(U). The preimage of U is affine,
and the section map A -> Gamma(Z,i⁻¹U) is surjective with kernel I. Its
quotient isomorphism presents the restricted immersion as Spec(A/I) -> Spec A.
Use the affine quotient restricted isomorphism for the target coefficient
sheaf. For the source use tilde(A) = O_Spec(A), transport across isoSpec,
and the restriction isomorphism for O_Y. Choose the quotient identification
induced by the first isomorphism theorem, rather than an arbitrary object
isomorphism. On every basic open D(g), these identifications are the canonical
localization identifications: the restricted unit sends x/g^k to its image in
(A/I)_g. The pullback-unit isomorphism sends the tensor unit to 1, so the
adjunction formula in ha gives exactly this localized quotient map. Both
sides of the asserted equality therefore agree on every basic open. The
basis sheaf condition gives equality of the sheaf morphisms. The coefficient
map formula can also be read directly from
`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`
and `SheafOfModules.unitToPushforwardObjUnit_val_app_apply`. For I = top,
the target sheaf is zero; for the zero ring or empty chart all sections and
maps are unique. No sequence, complex, or regularity condition is involved. -/
theorem affine_closedImmersion_coefficient_square
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.affineOpens)
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom) :
    let A := (Γ(Y, U.1) : Type u)
    let I := i.ker.ideal U
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let R := Scheme.Modules.restrictFunctor U.1.ι
    ∃ (eO : R.obj (SheafOfModules.unit Y.ringCatSheaf) ≅ T.obj (ModuleCat.of A A))
      (eB : R.obj ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ≅ T.obj (ModuleCat.of A (A ⧸ I))),
      R.map a ≫ eB.hom = eO.hom ≫ T.map (ModuleCat.ofHom I.mkQ) := by
  let A := (Γ(Y, U.1) : Type u)
  let I := i.ker.ideal U
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let R := Scheme.Modules.restrictFunctor U.1.ι
  have hunit : a = SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom := by
    rw [ha]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have : Epi a := hunit.symm ▸ coefficient_epi i
  have : (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).IsEquivalence :=
    restrict_equivalence U.2.isoSpec
  let eO : R.obj (SheafOfModules.unit Y.ringCatSheaf) ≅ T.obj (ModuleCat.of A A) :=
    Scheme.Modules.restrictUnitIso U.1.ι ≪≫
      (Scheme.Modules.restrictUnitIso U.2.isoSpec.hom).symm ≪≫
      (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso tildeSelf.symm
  obtain ⟨e, he⟩ := quotient_presentation i U
  obtain ⟨b⟩ := affine_quotient_restricted_iso i U.1 U.2 I e he
  let eB := b.symm
  let f : ModuleCat.of A A ⟶ ModuleCat.of A (A ⧸ I) :=
    T.preimage (eO.inv ≫ R.map a ≫ eB.hom)
  have hfmap : T.map f = eO.inv ≫ R.map a ≫ eB.hom := T.map_preimage _
  have : Epi (T.map f) := by rw [hfmap]; infer_instance
  have : Epi f := T.epi_of_epi_map inferInstance
  obtain ⟨c, hc⟩ := surjective_quotient_coordinates I f
    ((ModuleCat.epi_iff_surjective f).mp inferInstance)
  refine ⟨eO, eB ≪≫ T.mapIso c, ?_⟩
  change R.map a ≫ (eB.hom ≫ T.map c.hom) = _
  rw [← Category.assoc]
  have hs : R.map a ≫ eB.hom = eO.hom ≫ T.map f := by
    rw [hfmap]
    simp
  rw [hs, Category.assoc, ← T.map_comp, hc]

end AlgebraicGeometry
