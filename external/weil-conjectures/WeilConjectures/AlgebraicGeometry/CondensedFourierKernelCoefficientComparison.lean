/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientConstantSectionMap
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPullbackIso
public import WeilConjectures.AlgebraicGeometry.CondensedProjectorCoefficientNaturality

/-! Coefficient comparison for a pulled-back Artin–Schreier kernel.

Source: the scalar-extension paragraph of the first-formula proof
(blueprint: lem-fd-unit-punctured-kernel-coefficient-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
set_option allowUnsafeReducibility true in
attribute [local reducible] condensedArtinSchreierPushforward Mod.extendScalars

private theorem coefficientCongr
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ t).obj
      (Mod.regular (condensedRingObj Λ X))) h)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} g).map (coefficientMap a X) =
      (ProEtale.lowerStar Ab.{u + 1} f).map (coefficientMap a X) ≫
        (eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ' t).obj
          (Mod.regular (condensedRingObj Λ' X))) h)).hom := by
  subst g
  simp only [eqToHom_refl, Mod.id_hom', Category.id_comp]
  erw [Category.comp_id]

private theorem unitUnderlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))).X = condensedRingObj Λ X := rfl

-- Keep the coefficient calculation independent of the affine-space constructions.
private theorem translationCoefficient_naturality
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}}
    (t : X ⟶ X) (f : X ⟶ Y) (h : t ≫ f = f) :
    ((CondensedRing.lowerStar Λ f).map
        (((CondensedRing.upperStarLowerStarAdjunction Λ t).homEquiv _ _)
          (Functor.Monoidal.εIso (CondensedRing.upperStar Λ t)).inv) ≫
      (CondensedRing.lowerStarComp Λ t f).hom.app _ ≫
      eqToHom (congrArg (fun g ↦ (CondensedRing.lowerStar Λ g).obj
        (Mod.regular (condensedRingObj Λ X))) h)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map (coefficientMap a X) =
    (ProEtale.lowerStar Ab.{u + 1} f).map (coefficientMap a X) ≫
      ((CondensedRing.lowerStar Λ' f).map
        (((CondensedRing.upperStarLowerStarAdjunction Λ' t).homEquiv _ _)
          (Functor.Monoidal.εIso (CondensedRing.upperStar Λ' t)).inv) ≫
      (CondensedRing.lowerStarComp Λ' t f).hom.app _ ≫
      eqToHom (congrArg (fun g ↦ (CondensedRing.lowerStar Λ' g).obj
        (Mod.regular (condensedRingObj Λ' X))) h)).hom := by
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom, Category.assoc]
  erw [CondensedRing.homEquiv_εIso_inv_hom Λ t,
    CondensedRing.homEquiv_εIso_inv_hom Λ' t]
  rw [coefficientCongr a h]
  rw [CondensedRing.lowerStarComp_hom_app_hom,
    CondensedRing.lowerStarComp_hom_app_hom]
  rw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc,
    condensedPushforwardHom_comp_map_coefficientMap a t, Functor.map_comp]
  simp only [Category.assoc, unitUnderlying]

-- Explicit coefficient and module-object coercions require additional elaboration.
private theorem translationCoefficient
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (k : Type u) [Field k] [Fintype k] (c : k) :
    (condensedArtinSchreierTranslationAction Λ k c).asHom.hom ≫
        (ProEtale.lowerStar Ab.{u + 1}
          (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
            (coefficientMap a (AffineSpace PUnit (Spec (.of k)))) =
      (ProEtale.lowerStar Ab.{u + 1}
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
          (coefficientMap a (AffineSpace PUnit (Spec (.of k)))) ≫
        (condensedArtinSchreierTranslationAction Λ' k c).asHom.hom := by
  unfold condensedArtinSchreierTranslationAction
  exact translationCoefficient_naturality a (Etale.artinSchreierTranslation k c)
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)

private theorem regularCoefficient
    {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [BraidedCategory C]
    {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (s : MonObj.Γ R) :
    (Mod.regularEndRingHom s).asHom.hom ≫ a =
      a ≫ (Mod.regularEndRingHom (MonObj.Γ.map a s)).asHom.hom := by
  have h : (Mod.regularEndRingHom s).asHom ≫ Mod.regularHomComap a =
      Mod.regularHomComap a ≫ (Mod.comap a).map
        (Mod.regularEndRingHom (MonObj.Γ.map a s)).asHom := by
    apply Mod.regular_hom_ext
    change (MonObj.one : 𝟙_ C ⟶ R) ≫ ((Mod.regularEndRingHom s).asHom.hom ≫ a) =
      (MonObj.one : 𝟙_ C ⟶ R) ≫
        (a ≫ (Mod.regularEndRingHom (MonObj.Γ.map a s)).asHom.hom)
    rw [← Category.assoc, ← Category.assoc, IsMonHom.one_hom (f := a)]
    erw [Mod.regularEndRingHom_apply, Mod.one_comp_regularLift_regular,
      Mod.regularEndRingHom_apply, Mod.one_comp_regularLift_regular]
    rfl
  exact congrArg Mod.Hom.hom h

private theorem mapRingInverse
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {r : R} (h : IsUnit r) :
    f (Ring.inverse r) = Ring.inverse (f r) := by
  obtain ⟨v, rfl⟩ := h
  have hi := Ring.inverse_unit (v.map f.toMonoidHom)
  rw [Ring.inverse_unit]
  exact hi.symm

private theorem coefficientSection
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) (s : MonObj.Γ Λ) :
    MonObj.Γ.map (coefficientMap a X)
        (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X) s) =
      MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X) (MonObj.Γ.map a s) := by
  ext
  simp only [MonObj.Γ.map_hom, MonObj.Γ.mapFunctorMonoidHom_hom,
    coefficientMap, Category.assoc, ← Functor.map_comp]

private theorem sumUnderlying
    {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {R : C} [MonObj R] {M N : Mod C R}
    {I : Type*} [Fintype I] (f : I → (M ⟶ N)) :
    (∑ i, f i).hom = ∑ i, (f i).hom :=
  (Mod.forget R).map_sum f Finset.univ

private def pushScalar (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1) f).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X))) ≅
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) f).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) := by
  letI := CondensedRing.isIso_pushHom_padicSubfieldRingObjToPadicAlgCl_app ℓ E f
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X))
    (fun F hF ↦ CondensedRing.isIso_pushHom_padicSubfieldRingObjMap_app ℓ hF f _)
  exact asIso ((CondensedRing.pushHom
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app _) ≪≫
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) f).mapIso
        (Mod.extendScalarsObjRegularIso
          (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))

private theorem pushScalar_unit (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    Mod.extendUnitHom (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1) f).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X))) ≫
          (pushScalar ℓ E f).hom.hom =
      (ProEtale.lowerStar Ab.{u + 1} f).map
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X) := by
  unfold pushScalar
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Mod.comp_hom']
  rw [CondensedRing.extendUnitHom_comp_pushHom_app_hom_assoc,
    CondensedRing.lowerStar_map_hom, ← Functor.map_comp]
  congr 1
  exact Mod.extendUnitHom_extendHom _ _

-- Explicit coefficient and module-object coercions require additional elaboration.
private theorem characterImageScalar (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (k : Type u) [Field k] [Fintype k]
    (ψ : AddChar k (MonObj.Γ (Profinite.continuousMapRingObj.{u} E.1)))
    (hq : IsUnit (Fintype.card k : MonObj.Γ (Profinite.continuousMapRingObj.{u} E.1))) :
    Nonempty ((Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        (AffineSpace PUnit (Spec (.of k))))).obj
          (condensedArtinSchreierSheaf (Profinite.continuousMapRingObj E.1) k ψ) ≅
      condensedArtinSchreierSheaf (Profinite.padicAlgClRingObj ℓ) k
        ((MonObj.Γ.map
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)).toMonoidHom.compAddChar ψ)) := by
  let A := AffineSpace PUnit (Spec (.of k))
  let f := AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E
  let F := Mod.extendScalars (coefficientMap a A)
  let : F.IsLeftAdjoint :=
    (Mod.extendRestrictAdjunction (coefficientMap a A)).isLeftAdjoint
  let : PreservesFiniteColimits F := by infer_instance
  let : PreservesFiniteLimits F :=
    CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl ℓ A E
  let P := (condensedArtinSchreierProjector (Profinite.continuousMapRingObj E.1) k ψ).asHom
  let Q := (condensedArtinSchreierProjector (Profinite.padicAlgClRingObj ℓ) k
    ((MonObj.Γ.map a).toMonoidHom.compAddChar ψ)).asHom
  let e := pushScalar ℓ E f
  have h : F.map P ≫ e.hom = e.hom ≫ Q := by
    apply Mod.extendScalarsObj_hom_ext'
    simp only [Mod.comp_hom']
    have hu := pushScalar_unit ℓ E f
    change Mod.extendUnitHom (coefficientMap a A) _ ≫
      ((F.map P).hom ≫ e.hom.hom) =
        Mod.extendUnitHom (coefficientMap a A) _ ≫ (e.hom.hom ≫ Q.hom)
    rw [Mod.extendUnitHom_naturality_assoc]
    rw [hu, ← Category.assoc, hu]
    exact condensed_projector_coefficient_naturality a k hq ψ
  let q : Arrow.mk (F.map P) ≅ Arrow.mk Q := Arrow.isoMk e e h.symm
  change Nonempty (F.obj (image P) ≅ image Q)
  exact ⟨(PreservesImage.iso F P).symm ≪≫ im.mapIso q⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Mod.extendScalars

private theorem artinFunctionScalar
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.continuousMapRingObj E.1)))
    (ψ' : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ℓ)))
    (b : Γ(X, ⊤))
    (e : (Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        (AffineSpace PUnit (Spec (.of k₀))))).obj
          (condensedArtinSchreierSheaf (Profinite.continuousMapRingObj E.1) k₀ ψ) ≅
      condensedArtinSchreierSheaf (Profinite.padicAlgClRingObj ℓ) k₀ ψ') :
    Nonempty ((Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).obj
        (condensedArtinSchreierSheafOf (Profinite.continuousMapRingObj E.1) k₀ X ψ b) ≅
      condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X ψ' b) := by
  let f := AffineSpace.homOfVector (X ↘ Spec (.of k₀)) fun _ : PUnit ↦ b
  exact condensed_coefficient_pullback_iso ℓ E f
    (condensedArtinSchreierSheaf (Profinite.continuousMapRingObj E.1) k₀ ψ)
    (condensedArtinSchreierSheaf (Profinite.padicAlgClRingObj ℓ) k₀ ψ') e

-- Keep the ordinary image and pullback calculation independent of derived localization.
private theorem ordinaryArtinScalar
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ E) (b : Γ(X, ⊤)) :
    Nonempty ((Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) X)).obj
        (condensedArtinSchreierSheafOf (Profinite.continuousMapRingObj E.1) k₀ X
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b) ≅
      condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
          (E.1.subtype.toMonoidHom.compAddChar ψ)) b) := by
  classical
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E
  let ψE := (Profinite.continuousMapConstRingHom.{u} E).toMonoidHom.compAddChar ψ
  have hq : IsUnit (Fintype.card k₀ : MonObj.Γ (Profinite.continuousMapRingObj.{u} E.1)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)) :
        IsUnit (Fintype.card k₀ : E)).map (Profinite.continuousMapConstRingHom E)
  have hψ : (MonObj.Γ.map a).toMonoidHom.compAddChar ψE =
      (Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ) := by
    apply DFunLike.ext
    intro x
    exact condensed_constant_section_coefficient_map ℓ E (ψ x)
  obtain ⟨e⟩ := characterImageScalar ℓ E k₀ ψE hq
  let e' := e ≪≫ eqToIso (congrArg
    (condensedArtinSchreierSheaf (Profinite.padicAlgClRingObj.{u} ℓ) k₀) hψ)
  exact artinFunctionScalar ℓ E k₀ X ψE _ b e'



/-- Scalar extension along `E → Q̄_ℓ` of the condensed Artin–Schreier sheaf of a global
function `b` is isomorphic to the Artin–Schreier sheaf of the induced `Q̄_ℓ`-character, also for
a trivial character.

Source: latest blueprint, lemma-fourier-transform-constant-sheaf proof, coefficient paragraph
(blueprint: lem-fd-unit-punctured-kernel-coefficient-comparison).
Proof. `#k₀` is a unit in `E`, and a ring map preserves `Ring.inverse` of a unit; the
constant-section ring maps commute with `E → Q̄_ℓ`. The regular Push comparison along the
finite (hence qcqs) Artin–Schreier map is invertible by the finite-subextension Push
comparisons of `condensedCoefficientCompatibility`; it intertwines deck translations
and multiplication by global sections, hence the two character projectors. Exact scalar
extension preserves images, so the images of the projectors correspond; the Pull comparison
along the morphism defined by `b` transports this isomorphism to `condensedArtinSchreierSheafOf`.
-/
theorem condensed_fourier_kernel_coefficient_comparison
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ψ : AddChar k₀ E)
    (X : Scheme.{u}) [X.Over (Spec (.of k₀))] (b : Γ(X, ⊤)) :
    Nonempty ((Mod.extendScalars
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).obj
      (condensedArtinSchreierSheafOf (Profinite.continuousMapRingObj E) k₀ X
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b) ≅
    condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X
      ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) b) := by
  exact ordinaryArtinScalar ℓ E k₀ X ψ b

end AlgebraicGeometry.ProEtale
