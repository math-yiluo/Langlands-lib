/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization

/-! # Coefficient endomorphisms on additive Čech complexes

Source: Stacks Project, Tags 01EQ and 01FD. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Apply global sections to the actual resolution comparison map.
Source: Stacks Project, Tag 01EQ, functoriality in coefficients.
(blueprint: new-q4-additive-cech-scalar-chain-action) -/
noncomputable def additiveCechGlobalMap {X : Scheme.{u}}
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (f : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf) :
    additiveCechGlobal I ⟶ additiveCechGlobal I :=
  ((Etale.etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
    (.up ℕ)).map (InjectiveResolution.desc f I I)

/-- Apply the open Čech functor, flip, and totalize the resolution comparison map.
Source: Stacks Project, Tag 01FD, functoriality of the double complex.
(blueprint: new-q4-additive-cech-scalar-chain-action) -/
noncomputable def additiveCechTotalMap {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf)
    (f : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf) :
    additiveCechTotal U I ⟶ additiveCechTotal U I :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{u + 1} (.up ℕ) (.up ℕ)).map
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (additiveCechOpenInclusion X).op ⋙ cechComplexFunctor U).mapHomologicalComplex
            (.up ℕ)).map (InjectiveResolution.desc f I I))) (.up ℕ)

/-- The global restriction augmentation is natural in a coefficient endomorphism.
Source: Stacks Project, Tag 01FD, right upper square of the augmented diagram.
(blueprint: new-q4-additive-cech-scalar-chain-action) -/
theorem additiveCech_alpha_natural
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (f : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf) (n : ℕ) :
    additiveCechAlpha U I n ≫ (additiveCechTotalMap U I f).f n =
      (additiveCechGlobalMap I f).f n ≫ additiveCechAlpha U I n := by
  dsimp only [additiveCechAlpha, additiveCechTotalMap]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  rw [← Category.assoc]
  apply congrArg (fun k ↦ k ≫ _)
  apply Pi.hom_ext
  intro y
  change (Pi.lift _ ≫ Limits.Pi.map (fun y : Fin 1 → ι ↦
      ((InjectiveResolution.desc f I I).f n).hom.app
        (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)))))) ≫ _ = _
  erw [Category.assoc, Limits.Pi.map_π, ← Category.assoc, Pi.lift_comp_π,
    Category.assoc, Pi.lift_comp_π]
  exact ((InjectiveResolution.desc f I I).f n).hom.naturality _

/-- The coefficient augmentation commutes with multiplication.
Source: Stacks Project, Tags 01EQ and 01FD, the augmented double-complex diagram.
(blueprint: new-q4-additive-cech-scalar-chain-action)

Proof: The total map on a summand is the Čech map of the resolution comparison
in that resolution degree. Use desc_commutes_zero to move the comparison
past I.ι in each tuple coordinate. Substitute hμ, and use naturality of
restrictFunctorΓ to identify the restricted structural section with the scalar
on the module coordinate. The base ring map is the identity by ΓSpecIso and
toSpecΓ, so this coordinate is r times the original coordinate. The product
maps are equal coordinatewise; applying ιTotal_map proves the beta identity.
These arguments include zero scalar, unit scalar, degree zero, and empty products. -/
theorem additiveCech_scalar_chain_action
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (μ : Γ(X, ⊤) → (X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf))
    (hμ : ∀ r (W : X.Etaleᵒᵖ) (x : X.etaleAdditiveSheaf.obj.obj W),
      (μ r).hom.app W x =
        ULift.up ((show Γ(W.unop.left, ⊤) from x.down) *
          (show Γ(W.unop.left, ⊤) from W.unop.hom.appTop r)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (n : ℕ) (r : Γ(X, ⊤)) :
    ∀ x : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n,
      (additiveCechTotalMap U I (μ r)).f n (additiveCechBeta U I n x) =
        additiveCechBeta U I n (r • x) := by
  intro x
  dsimp only [additiveCechBeta, additiveCechTotalMap]
  rw [← ConcreteCategory.comp_apply, HomologicalComplex₂.ιTotal_map,
    ConcreteCategory.comp_apply]
  congr 1
  apply Concrete.limit_ext (Discrete.functor (fun y : Fin (n + 1) → ι ↦
    (I.cocomplex.X 0).obj.obj
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))))
  intro ⟨y⟩
  change (Pi.π (fun y : Fin (n + 1) → ι ↦
      (I.cocomplex.X 0).obj.obj
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))) y)
    ((Limits.Pi.map (fun y : Fin (n + 1) → ι ↦
    ((InjectiveResolution.desc (μ r) I I).f 0).hom.app
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)))))) _) = _
  erw [← ConcreteCategory.comp_apply, Limits.Pi.map_π, ConcreteCategory.comp_apply]
  erw [Pi.lift_comp_π_apply, Pi.lift_comp_π_apply]
  let V := ∏ᶜ fun l ↦ U (y l)
  let W := op ((additiveCechOpenInclusion X).obj V)
  let π := TopCat.Presheaf.cechComplexFunctorπ U
    (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y
  let ρ := (X.restrictFunctorΓ.inv.app (op V)).hom
  change ((InjectiveResolution.desc (μ r) I I).f 0).hom.app W
    ((I.ι.f 0).hom.app W (ULift.up (ρ (π x)))) =
    (I.ι.f 0).hom.app W (ULift.up (ρ (π (r • x))))
  have hd := congrArg (fun g ↦ g.hom.app W)
    (InjectiveResolution.desc_commutes_zero (μ r) I I)
  change (I.ι.f 0).hom.app W ≫
    ((InjectiveResolution.desc (μ r) I I).f 0).hom.app W =
      (μ r).hom.app W ≫ (I.ι.f 0).hom.app W at hd
  rw [← ConcreteCategory.comp_apply, hd, ConcreteCategory.comp_apply]
  erw [hμ]
  apply congrArg ((I.ι.f 0).hom.app W)
  apply ULift.ext
  change (show Γ(V.toScheme, ⊤) from ρ (π x)) * V.ι.appTop r =
    (show Γ(V.toScheme, ⊤) from ρ (π (r • x)))
  rw [π.hom.map_smul]
  change (show Γ(V.toScheme, ⊤) from ρ (π x)) * V.ι.appTop r =
    ρ ((X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op)
      (((Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ X.toSpecΓ.appTop) r) * (show Γ(X, V) from π x))
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  change (show Γ(V.toScheme, ⊤) from ρ (π x)) * V.ι.appTop r =
    ρ ((X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op) r * (show Γ(X, V) from π x))
  rw [map_mul, mul_comm]
  congr 1
  have he : V.ι.appTop = X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
      X.restrictFunctorΓ.inv.app (op V) := by
    dsimp only [Scheme.restrictFunctorΓ]
    simp only [NatIso.ofComponents_inv_app, Scheme.Opens.ι_appTop, Functor.mapIso_inv]
    rw [← Functor.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom he r

end AlgebraicGeometry.Scheme.Modules
