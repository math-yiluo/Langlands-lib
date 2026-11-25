/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Pullback of the pro-étale cohomology of `C(-, A)` along an isomorphism

For a morphism of schemes `g : Z ⟶ Y` and a topological abelian group `A`, precomposition with
the projections `V ×_Y Z ⟶ V` defines a morphism `C(-, A) ⟶ g_* C(-, A)` of pro-étale sheaves on
`Y` (`AlgebraicGeometry.ProEtale.continuousSheafToLowerStar`), natural in `A`; it is an
isomorphism when `g` is.

For an isomorphism `e : X ≅ Y` the pullback `e^*` of pro-étale sheaves is the pushforward
`(e⁻¹)_*` (`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`); this is how the Frobenius
pullback of Weil sheaves is defined. Pushing `Ext`-classes forward along the exact functor
`(e⁻¹)_*` therefore defines the pullback
`e^* : Hⁿ(Y_proét, C(-, A)) ⟶ Hⁿ(X_proét, C(-, A))`
(`AlgebraicGeometry.ProEtale.continuousSheafHPullback`). It is natural in `A`
(`AlgebraicGeometry.ProEtale.continuousSheafHPullback_map`), hence `ℤ_ℓ`-linear on the integral
and finite-level cohomology groups `Hⁿ(-, ℤ_ℓ)`, `Hⁿ(-, ℤ/ℓᵐ)` and compatible with the
reductions `ρₘ : Hⁿ(-, ℤ_ℓ) ⟶ Hⁿ(-, ℤ/ℓᵐ)`
(`AlgebraicGeometry.ProEtale.reduction_integralAdicHPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme

section Map

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y) (A : Type) [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A]

/-- The projections `V ×_Y Z ⟶ V`, as a natural transformation of functors `Y_proét ⥤ Sch`. -/
@[simps]
noncomputable def overPullbackFstNatTrans :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙ ProEt.forget Z ⋙ Over.forget Z ⟶
      ProEt.forget Y ⋙ Over.forget Y where
  app V := pullback.fst V.hom g
  naturality V W f := by
    simp [MorphismProperty.Over.pullback]

/-- The morphism `C(-, A) ⟶ g_* C(-, A)` of pro-étale sheaves on `Y` given on `V` by
precomposition with the projection `V ×_Y Z ⟶ V`. -/
noncomputable def continuousSheafToLowerStar :
    continuousSheaf Y A ⟶ (g)_*[AddCommGrpCat.{u + 1}].obj (continuousSheaf Z A) :=
  ⟨Functor.whiskerRight (NatTrans.op (overPullbackFstNatTrans g))
    (continuousMapPresheafAbULift.{u} A)⟩

lemma continuousSheafToLowerStar_hom_app (V : Y.ProEtᵒᵖ) :
    (continuousSheafToLowerStar g A).hom.app V =
      (continuousMapPresheafAbULift.{u} A).map (pullback.fst V.unop.hom g).op :=
  rfl

instance [IsIso g] : IsIso (continuousSheafToLowerStar g A) := by
  have (V : Y.ProEtᵒᵖ) : IsIso ((continuousSheafToLowerStar g A).hom.app V) := by
    rw [continuousSheafToLowerStar_hom_app]
    infer_instance
  have : IsIso ((sheafToPresheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}).map
      (continuousSheafToLowerStar g A)) :=
    NatIso.isIso_of_isIso_app (continuousSheafToLowerStar g A).hom
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

variable {A} in
/-- `continuousSheafToLowerStar` is natural in the coefficients. -/
@[reassoc]
lemma continuousSheafToLowerStar_naturality {B : Type} [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] (φ : ContinuousAddMonoidHom A B) :
    continuousSheafMap Y φ ≫ continuousSheafToLowerStar g B =
      continuousSheafToLowerStar g A ≫
        (g)_*[AddCommGrpCat.{u + 1}].map (continuousSheafMap Z φ) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦
    ((continuousMapPresheafAbULiftMap φ).naturality _).symm))

end Map

section Pullback

variable {X Y : Scheme.{u}} (e : X ≅ Y) (A : Type) [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A]

/-- The isomorphism `C(-, A) ≅ (e⁻¹)_* C(-, A)` for an isomorphism of schemes `e : X ≅ Y`. -/
noncomputable def continuousSheafIsoLowerStar :
    continuousSheaf X A ≅ (e.inv)_*[AddCommGrpCat.{u + 1}].obj (continuousSheaf Y A) :=
  asIso (continuousSheafToLowerStar e.inv A)

/-- The isomorphism `ℤ ≅ (e⁻¹)_* ℤ` of constant pro-étale sheaves, through `ℤ ≅ C(-, ℤ)`. -/
noncomputable def constantIntIsoLowerStar :
    (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      (e.inv)_*[AddCommGrpCat.{u + 1}].obj
        ((constantSheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  constantSheafIsoContinuousSheaf X ℤ ≪≫ continuousSheafIsoLowerStar e ℤ ≪≫
    (e.inv)_*[AddCommGrpCat.{u + 1}].mapIso (constantSheafIsoContinuousSheaf Y ℤ).symm

/-- The pullback `e^* : Hⁿ(Y_proét, C(-, A)) ⟶ Hⁿ(X_proét, C(-, A))` along an isomorphism
`e : X ≅ Y`: an `Ext`-class is pushed forward along the exact functor `e^* = (e⁻¹)_*` and read
through `ℤ ≅ (e⁻¹)_* ℤ` and `(e⁻¹)_* C(-, A) ≅ C(-, A)`. -/
noncomputable def continuousSheafHPullback (n : ℕ) :
    Sheaf.H (continuousSheaf Y A) n →+ Sheaf.H (continuousSheaf X A) n :=
  (Sheaf.H.map (continuousSheafIsoLowerStar e A).inv n).comp
    (Sheaf.H.mapFunctor (e.inv)_*[AddCommGrpCat.{u + 1}] (constantIntIsoLowerStar e) _ n)

lemma continuousSheafHPullback_apply (n : ℕ) (x : Sheaf.H (continuousSheaf Y A) n) :
    continuousSheafHPullback e A n x =
      ((Ext.mk₀ (constantIntIsoLowerStar e).hom).comp
        (x.mapExactFunctor (e.inv)_*[AddCommGrpCat.{u + 1}]) (zero_add n)).comp
          (Ext.mk₀ (continuousSheafIsoLowerStar e A).inv) (add_zero n) :=
  rfl

variable {A} in
/-- The pullback on cohomology is natural in the coefficients. -/
lemma continuousSheafHPullback_map {B : Type} [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] (φ : ContinuousAddMonoidHom A B) (n : ℕ)
    (x : Sheaf.H (continuousSheaf Y A) n) :
    continuousSheafHPullback e B n (Sheaf.H.map (continuousSheafMap Y φ) n x) =
      Sheaf.H.map (continuousSheafMap X φ) n (continuousSheafHPullback e A n x) := by
  simp only [continuousSheafHPullback, AddMonoidHom.coe_comp, Function.comp_apply,
    Sheaf.H.mapFunctor_map, ← Sheaf.H.map_comp_apply]
  congr 2
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (continuousSheafToLowerStar_naturality e.inv φ).symm

end Pullback

section Adic

variable {X Y : Scheme.{u}} (e : X ≅ Y) (p : ℕ) [Fact p.Prime]

/-- The pullback `e^* : Hⁿ(Y, ℤ_p) ⟶ Hⁿ(X, ℤ_p)` on integral `p`-adic pro-étale cohomology along
an isomorphism `e : X ≅ Y`. -/
noncomputable def integralAdicHPullback (n : ℕ) :
    IntegralAdicH Y p n →ₗ[ℤ_[p]] IntegralAdicH X p n where
  toFun := continuousSheafHPullback e ℤ_[p] n
  map_add' := map_add _
  map_smul' c x := continuousSheafHPullback_map e (PadicInt.smulHom p c) n x

/-- The pullback `e^* : Hⁿ(Y, ℤ/pᵐ) ⟶ Hⁿ(X, ℤ/pᵐ)` along an isomorphism `e : X ≅ Y`. -/
noncomputable def finiteAdicHPullback (m n : ℕ) :
    FiniteAdicH Y p m n →ₗ[ℤ_[p]] FiniteAdicH X p m n where
  toFun := continuousSheafHPullback e _ n
  map_add' := map_add _
  map_smul' c x := continuousSheafHPullback_map e (PadicInt.quotientSmulHom p m c) n x

/-- The pullback commutes with the reductions `ρₘ : Hⁿ(-, ℤ_p) ⟶ Hⁿ(-, ℤ/pᵐ)`. -/
lemma reduction_integralAdicHPullback (m n : ℕ) (x : IntegralAdicH Y p n) :
    reduction X p m n (integralAdicHPullback e p n x) =
      finiteAdicHPullback e p m n (reduction Y p m n x) :=
  (continuousSheafHPullback_map e _ n x).symm

end Adic

end AlgebraicGeometry.ProEtale
