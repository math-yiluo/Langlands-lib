/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Reconstruction of an affine quasi-coherent complex from its sections

Source: Stacks Project, Tag 01IB; Tag 06Z0, termwise associated sheaf construction.
(blueprint: lem-pc-affine-sections-complex-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def chartSectionsIso (Y : Scheme.{u}) [IsAffine Y] :
    SheafOfModules.evaluation.{u} Y.ringCatSheaf (op ⊤) ≅
      SheafOfModules.pushforward Y.isoSpec.hom.toRingCatSheafHom ⋙
        moduleSpecΓFunctor (R := Γ(Y, ⊤)) := by
  refine NatIso.ofComponents (fun N ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext x
    change (Y.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom r)) •
      (show Γ(N, ⊤) from x) = (show Γ(Y, ⊤) from r) • (show Γ(N, ⊤) from x)
    congr 1
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso Γ(Y, ⊤)).inv_hom_id_apply r
  · intro N N' f
    ext x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pushing the associated sheaf of the ordinary section complex back through the
canonical affine chart recovers a complex with quasi-coherent terms.
Source: Stacks Project, Tag 01IB (schemes-lemma-spec-sheaves), and Tag 06Z0.
(blueprint: lem-pc-affine-sections-complex-counit).

Proof: For A = Gamma(Y,O), push D forward along Y.isoSpec.hom. This preserves
quasi-coherence: inverse-chart restriction and chart pushforward are both left
adjoint to inverse-chart pushforward, hence naturally isomorphic; Mathlib's
restriction theorem preserves quasi-coherence. The global section comparison
identifies its A-module of sections, with scalars restricted through GammaSpecIso,
with the actual A-module D^n(Y). The identity
Y.isoSpec.hom.appTop composed with GammaSpecIso.inv is the identity, ensuring
agreement of the scalar actions.
Apply the affine quasi-coherent counit tilde(Gamma(-)) -> (-) in every degree.
Its naturality makes these maps commute with the differentials, and every component
is an isomorphism by Tag 01IB. Thus they form a complex isomorphism. Push it back
along Y.isoSpec.inv and compose with pushforwardComp, pushforwardCongr of the chart's
hom_inv_id, and pushforwardId. This yields the displayed isomorphism. This argument
works for unbounded complexes and the empty affine scheme; no projective replacement
or arbitrary choice of model is involved. -/
theorem affine_sections_complex_counit (Y : Scheme.{u}) [IsAffine Y]
    (D : CochainComplex Y.Modules ℤ)
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent) :
    Nonempty
      (((@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (Spec Γ(Y, ⊤)).ringCatSheaf)
        (SheafOfModules.{u} Y.ringCatSheaf) _ _ _ _
        (SheafOfModules.pushforward Y.isoSpec.inv.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)).obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Γ(Y, ⊤) : Type u))
          (SheafOfModules.{u} (Spec Γ(Y, ⊤)).ringCatSheaf) _ _ _ _
          (tilde.functor Γ(Y, ⊤)) ⟨fun _ _ ↦ tilde.map_zero⟩
          (ComplexShape.up ℤ)).obj
          (((SheafOfModules.evaluation.{u}
            Y.ringCatSheaf (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj D))) ≅ D) := by
  let F : SheafOfModules.{u} Y.ringCatSheaf ⥤
      SheafOfModules.{u} (Spec Γ(Y, ⊤)).ringCatSheaf :=
    SheafOfModules.pushforward Y.isoSpec.hom.toRingCatSheafHom
  let G : SheafOfModules.{u} (Spec Γ(Y, ⊤)).ringCatSheaf ⥤
      SheafOfModules.{u} Y.ringCatSheaf :=
    SheafOfModules.pushforward Y.isoSpec.inv.toRingCatSheafHom
  let e₀ : SheafOfModules.{u} Y.ringCatSheaf ≌
      SheafOfModules.{u} (Spec Γ(Y, ⊤)).ringCatSheaf :=
    CategoryTheory.Equivalence.mk F G
      (pushforwardComp Y.isoSpec.hom Y.isoSpec.inv ≪≫
        pushforwardCongr Y.isoSpec.hom_inv_id ≪≫ pushforwardId Y).symm
      (pushforwardComp Y.isoSpec.inv Y.isoSpec.hom ≪≫
        pushforwardCongr Y.isoSpec.inv_hom_id ≪≫ pushforwardId (Spec Γ(Y, ⊤)))
  let ψ : F ≅ restrictFunctor Y.isoSpec.inv :=
    e₀.toAdjunction.leftAdjointUniq (restrictAdjunction Y.isoSpec.inv)
  let S : SheafOfModules.{u} (Spec Γ(Y, ⊤)).ringCatSheaf ⥤
      ModuleCat.{u} (Γ(Y, ⊤) : Type u) := moduleSpecΓFunctor (R := Γ(Y, ⊤))
  let T : ModuleCat.{u} (Γ(Y, ⊤) : Type u) ⥤
      SheafOfModules.{u} (Spec Γ(Y, ⊤)).ringCatSheaf :=
    tilde.functor Γ(Y, ⊤)
  have : F.Additive := ⟨by intros; rfl⟩
  have : G.Additive := ⟨by intros; rfl⟩
  have : S.Additive := ⟨by intros; rfl⟩
  have : T.Additive := by
    change (tilde.functor Γ(Y, ⊤)).Additive
    constructor
    intro M N f g
    exact tilde.map_add (R := Γ(Y, ⊤)) f g
  have : (SheafOfModules.evaluation.{u}
      Y.ringCatSheaf (op ⊤)).Additive := ⟨by intros; rfl⟩
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let GC := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let SC := S.mapHomologicalComplex (ComplexShape.up ℤ)
  let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let K := FC.obj D
  let α := (Functor.mapHomologicalComplexCompIso
    (chartSectionsIso Y).symm (ComplexShape.up ℤ)).app D
  let ε := (NatTrans.mapHomologicalComplex (tilde.adjunction (R := Γ(Y, ⊤))).counit
    (ComplexShape.up ℤ)).app K
  have : ∀ n : ℤ, IsIso (ε.f n) := by
    intro n
    have : (D.X n).IsQuasicoherent := hDqc n
    have : ((restrictFunctor Y.isoSpec.inv).obj (D.X n)).IsQuasicoherent :=
      isQuasicoherent_restrictFunctor Y.isoSpec.inv (D.X n)
    have : (K.X n).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf).prop_of_iso
        (ψ.app (D.X n)).symm inferInstance
    exact isIso_fromTildeΓ_of_isQuasicoherent (K.X n)
  have : IsIso ε := HomologicalComplex.Hom.isIso_of_components ε
  let β : TC.obj (SC.obj K) ≅ K :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (S ⋙ T))
      (ComplexShape.up ℤ)).app K ≪≫ asIso ε ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K
  let γ := (NatIso.mapHomologicalComplex
    (pushforwardComp Y.isoSpec.hom Y.isoSpec.inv ≪≫
      pushforwardCongr Y.isoSpec.hom_inv_id ≪≫ pushforwardId Y)
    (ComplexShape.up ℤ)).app D
  exact ⟨GC.mapIso (TC.mapIso α.symm ≪≫ β) ≪≫ γ⟩

end AlgebraicGeometry.Scheme.Modules
