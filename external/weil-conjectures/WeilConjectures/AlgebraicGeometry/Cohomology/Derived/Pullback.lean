/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Derived.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.FlatResolution
public import WeilConjectures.AlgebraicGeometry.Modules.StalkExact
public import WeilConjectures.AlgebraicGeometry.Modules.StalkPullback
public import WeilConjectures.AlgebraicGeometry.Modules.StalkTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-!
# The derived pullback of `𝒪`-modules

For a morphism of schemes `g : T ⟶ S`, the pullback `g^* : S.Modules ⥤ T.Modules` is right
exact but not exact. Its total left derived functor `Lg^* : D(𝒪_S) ⥤ D(𝒪_T)`
(`AlgebraicGeometry.Scheme.Modules.derivedPullback`) is computed on K-flat complexes.

The K-flat machinery (`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`)
requires that `g^*` sends quasi-isomorphisms between K-flat complexes to quasi-isomorphisms,
equivalently that `g^* Z` is acyclic for an acyclic K-flat complex `Z`
(`AlgebraicGeometry.Scheme.Modules.acyclic_pullback_of_kFlat`). This is checked on stalks: with
`s = g t`, the stalk `(g^* Z)_t` is `𝒪_{T,t} ⊗_{𝒪_{S,s}} Z_s`, which is the stalk at `s` of the
complex `Z ⊗ s_* 𝒪_{T,t}` obtained by tensoring with the skyscraper module at `s` with value
`𝒪_{T,t}`; and `Z ⊗ s_* 𝒪_{T,t}` is acyclic as `Z` is acyclic and K-flat.

A bounded above complex of flat modules is K-flat, so on such complexes `Lg^*` is computed by
pulling back term by term (`AlgebraicGeometry.Scheme.Modules.isIso_derivedPullbackCounit_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} (g : T ⟶ S)

section Stalk

variable (t : T)

attribute [local instance] stalkAlgebra

/-- The skyscraper module at `g t` with value the local ring `𝒪_{T,t}`. -/
noncomputable abbrev skyscraperStalk : S.Modules :=
  skyscraper (g t) (T.presheaf.stalk t)

/-- The comparison map `(M ⊗ (g t)_* 𝒪_{T,t})_{g t} → (g^* M)_t`: the composite of
`(M ⊗ L)_s ≅ M_s ⊗ L_s ≅ M_s ⊗ 𝒪_{T,t} ≅ 𝒪_{T,t} ⊗ M_s → (g^* M)_t`. -/
noncomputable def tensorSkyscraperStalkToPullbackStalk (M : S.Modules) :
    (M ⊗ skyscraperStalk g t).presheaf.stalk (g t) →+ ((pullback g).obj M).presheaf.stalk t :=
  (pullbackStalkMap g t M).toAddMonoidHom.comp
    ((TensorProduct.comm _ _ _).toLinearMap.toAddMonoidHom.comp
      ((LinearMap.lTensor _ (skyscraperStalkLinearEquiv (g t) (T.presheaf.stalk t)).toLinearMap
        ).toAddMonoidHom.comp
        (stalkTensorEquiv M (skyscraperStalk g t) (g t)).toAddMonoidHom))

lemma bijective_tensorSkyscraperStalkToPullbackStalk (M : S.Modules) :
    Function.Bijective (tensorSkyscraperStalkToPullbackStalk g t M) := by
  simp only [tensorSkyscraperStalkToPullbackStalk, AddMonoidHom.coe_comp,
    LinearMap.toAddMonoidHom_coe, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_coe]
  exact (bijective_pullbackStalkMap g t M).comp ((LinearEquiv.bijective _).comp
    ((LinearEquiv.bijective (LinearEquiv.lTensor _
      (skyscraperStalkLinearEquiv (g t) (T.presheaf.stalk t)))).comp (AddEquiv.bijective _)))

lemma tensorSkyscraperStalkToPullbackStalk_naturality {M M' : S.Modules} (φ : M ⟶ M')
    (z : (M ⊗ skyscraperStalk g t).presheaf.stalk (g t)) :
    tensorSkyscraperStalkToPullbackStalk g t M' ((φ ▷ skyscraperStalk g t).stalkLinearMap (g t) z) =
      ((pullback g).map φ).stalkLinearMap t (tensorSkyscraperStalkToPullbackStalk g t M z) := by
  simp only [tensorSkyscraperStalkToPullbackStalk, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_coe,
    stalkTensorEquiv_naturality, ← pullbackStalkMap_naturality]
  congr 1
  induction stalkTensorEquiv M (skyscraperStalk g t) (g t) z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b => simp

/-- The natural transformation `(M ⊗ (g t)_* 𝒪_{T,t})_{g t} → (g^* M)_t`, an isomorphism. -/
noncomputable def tensorSkyscraperStalkNatTrans :
    tensorRight (skyscraperStalk g t) ⋙ stalkFunctor (g t) ⟶ pullback g ⋙ stalkFunctor t where
  app M := AddCommGrpCat.ofHom (tensorSkyscraperStalkToPullbackStalk g t M)
  naturality M M' φ := by
    ext z
    exact tensorSkyscraperStalkToPullbackStalk_naturality g t φ z

instance : IsIso (tensorSkyscraperStalkNatTrans g t) := by
  have (M : S.Modules) : IsIso ((tensorSkyscraperStalkNatTrans g t).app M) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_tensorSkyscraperStalkToPullbackStalk g t M
  exact NatIso.isIso_of_isIso_app _

end Stalk

/-- **The pullback of an acyclic K-flat complex is acyclic.** For `g : T ⟶ S` and an acyclic
K-flat complex `Z` of `𝒪_S`-modules, the complex `g^* Z` is acyclic: at a point `t` of `T`, with
`s = g t`, the stalk `(g^* Z)_t = 𝒪_{T,t} ⊗_{𝒪_{S,s}} Z_s` is the stalk at `s` of the acyclic
complex `Z ⊗ s_* 𝒪_{T,t}`. -/
theorem acyclic_pullback_of_kFlat (Z : CochainComplex S.Modules ℤ)
    (hZ : (HomologicalComplex.quasiIso S.Modules (.up ℤ)).kFlat Z) (hZ' : Z.Acyclic) :
    (((pullback g).mapHomologicalComplex _).obj Z).Acyclic := by
  rw [acyclic_iff_stalkFunctor]
  intro t
  have h := CochainComplex.acyclic_tensorRight_of_kFlat Z hZ hZ' (skyscraperStalk g t)
  rw [acyclic_iff_stalkFunctor] at h
  exact (h (g t)).of_iso
    ((NatIso.mapHomologicalComplex (asIso (tensorSkyscraperStalkNatTrans g t)) _).app Z)

instance : (pullback g).PreservesKFlatQuasiIso :=
  Functor.PreservesKFlatQuasiIso.mk' _ (acyclic_pullback_of_kFlat g)

/-- The **derived pullback** `Lg^* : D(𝒪_S) ⥤ D(𝒪_T)` along a morphism of schemes `g : T ⟶ S`:
the total left derived functor of the pullback `g^* : S.Modules ⥤ T.Modules`
(`CategoryTheory.Functor.leftDerivedFunctor`). It is computed on a complex `E` by applying `g^*`
termwise to a K-flat resolution `P ⟶ E`; this is the derived tensor product
`𝒪_T ⊗ᴸ_{g⁻¹𝒪_S} g⁻¹ E`, as `g^* P = 𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹ P` termwise.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--2`) -/
noncomputable def derivedPullback : DerivedCategory S.Modules ⥤ DerivedCategory T.Modules :=
  (pullback g).leftDerivedFunctor

/-- The counit `Lg^*(E) ⟶ g^* E` of the derived pullback, for complexes `E` of `𝒪_S`-modules. -/
noncomputable def derivedPullbackCounit :
    DerivedCategory.Qh ⋙ derivedPullback g ⟶
      (pullback g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (pullback g).leftDerivedFunctorCounit

instance : (derivedPullback g).IsLeftDerivedFunctor (derivedPullbackCounit g)
    (HomotopyCategory.quasiIso S.Modules (ComplexShape.up ℤ)) :=
  inferInstanceAs ((pullback g).leftDerivedFunctor.IsLeftDerivedFunctor
    (pullback g).leftDerivedFunctorCounit _)

/-- **Termwise derived pullback of a bounded above flat complex.** Let `E` be a complex of flat
`𝒪_S`-modules vanishing in large degrees. Then the derived pullback `Lg^* E` is represented by the
termwise pullback `g^* E`: the canonical map `Lg^* E ⟶ g^* E` is an isomorphism. Indeed a bounded
above complex of flat modules is K-flat.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--2`) -/
theorem isIso_derivedPullbackCounit_app (E : CochainComplex S.Modules ℤ) (b : ℤ)
    [E.IsStrictlyLE b] (hE : ∀ n, ObjectProperty.flat (E.X n)) :
    IsIso ((derivedPullbackCounit g).app ((HomotopyCategory.quotient _ _).obj E)) :=
  (pullback g).isIso_leftDerivedFunctorCounit_app_of_kFlat E
    (CochainComplex.kFlat_of_isStrictlyLE_of_flat E b hE)

/-- The derived pullback of a bounded above complex `E` of flat `𝒪_S`-modules is the termwise
pullback: `Lg^* E ≅ g^* E` in `D(𝒪_T)`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--2`) -/
noncomputable def derivedPullbackObjIsoOfFlat (E : CochainComplex S.Modules ℤ) (b : ℤ)
    [E.IsStrictlyLE b] (hE : ∀ n, ObjectProperty.flat (E.X n)) :
    (derivedPullback g).obj (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj (((pullback g).mapHomologicalComplex _).obj E) :=
  have := isIso_derivedPullbackCounit_app g E b hE
  (derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso S.Modules).symm.app E) ≪≫
    asIso ((derivedPullbackCounit g).app ((HomotopyCategory.quotient _ _).obj E)) ≪≫
    DerivedCategory.Qh.mapIso (((pullback g).mapHomotopyCategoryFactors _).app E) ≪≫
    (DerivedCategory.quotientCompQhIso T.Modules).app _

end AlgebraicGeometry.Scheme.Modules
