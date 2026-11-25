/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation
public import WeilConjectures.ConstructibleSheaf.EtaleLowerShriekNoetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Extensions by zero along étale maps of affine schemes are constructible

Stacks 03SA for an étale map of affine schemes `Spec B ⟶ Spec A`: the étale `A`-algebra `B` is
the base change of an étale algebra `B₀` over a finitely generated subring `A₀ ⊆ A`
(`AlgebraicGeometry.exists_finset_algEquiv_tensorProduct_of_etale`), so `v_! M` is the pullback of
`(v₀)_! M` along `Spec A ⟶ Spec A₀` (`AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeIso`),
which is constructible over the Noetherian `Spec A₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme

instance etale_SpecMap_algebraMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] : Etale (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

/-- **Stacks 03SA for étale maps of affine schemes.** For an étale `A`-algebra `B` and a finitely
generated `Λ`-module `M`, the extension by zero of the constant sheaf `M` along
`Spec B ⟶ Spec A` is constructible. -/
theorem isConstructibleSheaf_etaleLowerShriek_constantSheaf_SpecMap {Λ : Type (u + 1)}
    [CommRing Λ] (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsConstructibleSheaf ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) inferInstance).obj
        ((constantSheaf (Spec (.of B)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  obtain ⟨F, B₀, _, _, hB₀, ⟨e⟩⟩ := exists_finset_algEquiv_tensorProduct_of_etale (A := A) B
  let A₀ := Algebra.adjoin ℤ (F : Set A)
  have : Algebra.FiniteType ℤ A₀ :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset F)
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  -- the cartesian square of spectra
  have sq₀ := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A₀ A B₀)
  let eR : CommRingCat.of B ≅ CommRingCat.of (A ⊗[A₀] B₀) := e.toRingEquiv.symm.toCommRingCatIso
  let e₁ : Spec (.of (A ⊗[A₀] B₀)) ≅ Spec (.of B) := Scheme.Spec.mapIso eR.op
  have sq := sq₀.of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (fst' := Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (f' := Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)))
    (snd' := e₁.inv ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom))
    (by
      change _ ≫ 𝟙 _ = Spec.map eR.hom ≫ _
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext a
      change a ⊗ₜ 1 = e.symm (algebraMap A B a)
      rw [AlgEquiv.commutes]
      rfl)
    (by simp) (by simp) (by simp)
  have : IsConstructibleSheaf ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) inferInstance).obj
        ((constantSheaf (Spec (.of B₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
    isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_isNoetherian _ M
  have := IsConstructibleSheaf.upperStar (A := ModuleCat.{u + 1} Λ)
    (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) inferInstance).obj
        ((constantSheaf (Spec (.of B₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
  have : IsConstructibleSheaf ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) inferInstance ⋙
        Etale.upperStar _ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).obj
        ((constantSheaf (Spec (.of B₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := this
  exact IsConstructibleSheaf.of_iso (((Etale.etaleLowerShriekBaseChangeIso Λ sq).app _) ≪≫
    (Etale.etaleLowerShriek _ _ inferInstance).mapIso
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) _).app M))

/-- **Stacks 03SA for étale maps between affine schemes.** -/
theorem isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_isAffine {Λ : Type (u + 1)}
    [CommRing Λ] {V Y : Scheme.{u}} (v : V ⟶ Y) [Etale v] [IsAffine V] [IsAffine Y]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsConstructibleSheaf ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v inferInstance).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  let : Algebra Γ(Y, ⊤) Γ(V, ⊤) := v.appTop.hom.toAlgebra
  have : Algebra.Etale Γ(Y, ⊤) Γ(V, ⊤) := HasRingHomProperty.appTop @Etale v inferInstance
  have hv : Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(V, ⊤))) = Spec.map v.appTop := rfl
  have sq : IsPullback v V.isoSpec.hom Y.isoSpec.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(V, ⊤)))) :=
    IsPullback.of_vert_isIso ⟨by rw [hv, Scheme.isoSpec_hom_naturality]⟩
  have := isConstructibleSheaf_etaleLowerShriek_constantSheaf_SpecMap (Λ := Λ) Γ(Y, ⊤) Γ(V, ⊤) M
  have := IsConstructibleSheaf.upperStar (A := ModuleCat.{u + 1} Λ) Y.isoSpec.hom
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(V, ⊤)))) inferInstance).obj
        ((constantSheaf (Spec (.of Γ(V, ⊤))).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
  have : IsConstructibleSheaf ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(V, ⊤)))) inferInstance ⋙
        Etale.upperStar _ Y.isoSpec.hom).obj
        ((constantSheaf (Spec (.of Γ(V, ⊤))).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
    this
  exact IsConstructibleSheaf.of_iso (((Etale.etaleLowerShriekBaseChangeIso Λ sq).app _) ≪≫
    (Etale.etaleLowerShriek _ _ inferInstance).mapIso
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) _).app M))

end AlgebraicGeometry.Scheme
