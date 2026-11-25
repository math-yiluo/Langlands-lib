/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalarsExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalarsComp
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import WeilConjectures.SixFunctors.Etale.Derived.SingleDelta
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit

/-!
# The Kummer classes

Let `Λ` be a commutative ring of positive characteristic `n` and `X` a scheme on which `n` is
invertible. A unit `u` of `X` is a morphism `ℤ ⟶ 𝔾ₘ` of étale sheaves
(`AlgebraicGeometry.Scheme.unitToGmSheaf`). Pulling the Kummer sequence
`0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` back along it gives the short exact sequence
`0 ⟶ μₙ ⟶ {(x, k) | xⁿ = uᵏ} ⟶ ℤ ⟶ 0` (the class of the `μₙ`-torsor of `n`-th roots of `u`),
and extending scalars to `Λ` keeps it exact, since `ℤ` is projective
(`AlgebraicGeometry.Etale.shortExact_kummerSequence_pullback_map_extendScalars`). Its connecting
morphism is the *Kummer class*

`κ(u) : Λ_X ⟶ (μₙ ⊗ Λ)[1] = Λ_X(1)[1]`

(`AlgebraicGeometry.Etale.kummerClassOf`): the boundary of `u` in the Kummer sequence, with
coefficients extended to `Λ`. It is additive in `u` (`AlgebraicGeometry.Etale.kummerClassOf_mul`).

## Main definitions

- `AlgebraicGeometry.Etale.kummerClassOf`: the Kummer class `κ(u) ∈ H¹(X, Λ(1))`.

Its naturality under pullback and the resulting Kummer class datum are in
`WeilConjectures.EtaleCohomology.TateTwist.KummerClass`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Scheme

/-- The constant étale sheaf `ℤ` (written `ℤ/0`, so as to reuse the lemmas on `ℤ/n`). -/
noncomputable abbrev constantSheafInt (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  X.constantZMod 0

variable {X : Scheme.{u}}

/-- The morphism `ℤ ⟶ 𝔾ₘ` of étale sheaves given by a unit `u` of `X`: `k ↦ uᵏ`. -/
noncomputable def unitToGmSheaf (u : Γ(X, ⊤)ˣ) : X.constantSheafInt ⟶ X.gmSheaf :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).homEquiv
    _ _).symm (zmodToGmSections 0 u (pow_zero u))

lemma zmodToGmSections_zero_mul (u v : Γ(X, ⊤)ˣ) :
    zmodToGmSections 0 (u * v) (pow_zero _) =
      zmodToGmSections 0 u (pow_zero u) + zmodToGmSections 0 v (pow_zero v) := by
  have key : ∀ {G : AddCommGrpCat.{u + 1}} (f g : AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)) ⟶ G),
      f.hom (ULift.up 1) = g.hom (ULift.up 1) → f = g := by
    intro G f g h
    ext ⟨a⟩
    have ha : (ULift.up a : ULift.{u + 1} (ZMod 0)) = (a : ℤ) • ULift.up 1 := by
      apply ULift.ext
      change a = (a : ℤ) • (1 : ZMod 0)
      simp
    rw [ha, map_zsmul, map_zsmul, h]
  apply key
  have h1 := zmodToGmSections_natCast 0 (u * v) (pow_zero _) 1
  have h2 := zmodToGmSections_natCast 0 u (pow_zero _) 1
  have h3 := zmodToGmSections_natCast 0 v (pow_zero _) 1
  simp only [Nat.cast_one, pow_one] at h1 h2 h3
  rw [AddCommGrpCat.hom_add, AddMonoidHom.add_apply, h1, h2, h3, gmSection_mul]

instance (U : (X.Etale)ᵒᵖ) :
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj U).Additive where
  map_add {_ _ _ _} := rfl

lemma unitToGmSheaf_mul (u v : Γ(X, ⊤)ˣ) :
    unitToGmSheaf (u * v) = unitToGmSheaf u + unitToGmSheaf v := by
  apply ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv _ _).injective
  rw [unitToGmSheaf, Equiv.apply_symm_apply, zmodToGmSections_zero_mul, Adjunction.homEquiv_unit,
    Functor.map_add, Preadditive.comp_add, ← Adjunction.homEquiv_unit, ← Adjunction.homEquiv_unit]
  simp only [unitToGmSheaf, Equiv.apply_symm_apply]

end Scheme

namespace Etale

open Scheme

/-- Homomorphisms out of `ℤ` are determined by the image of `1`. -/
lemma _root_.AddCommGrpCat.hom_ext_uliftInt {G : AddCommGrpCat.{u + 1}}
    {f g : AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)) ⟶ G}
    (h : f.hom (ULift.up 1) = g.hom (ULift.up 1)) : f = g := by
  ext ⟨a⟩
  have ha : (ULift.up a : ULift.{u + 1} (ZMod 0)) = (a : ℤ) • ULift.up 1 := by
    apply ULift.ext
    change a = (a : ℤ) • (1 : ZMod 0)
    simp
  rw [ha, map_zsmul, map_zsmul, h]

instance : Projective (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0))) where
  factors {E F} f e he := by
    rw [AddCommGrpCat.epi_iff_surjective] at he
    obtain ⟨x, hx⟩ := he (f.hom (ULift.up 1))
    refine ⟨AddCommGrpCat.ofHom ((zmultiplesHom E x).comp
      (AddEquiv.ulift.toAddMonoidHom : ULift.{u + 1} (ZMod 0) →+ ℤ)), ?_⟩
    apply AddCommGrpCat.hom_ext_uliftInt
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
      Function.comp_apply, zmultiplesHom_apply, AddEquiv.coe_toAddMonoidHom, map_zsmul, hx]
    exact one_smul ℤ _

variable {X : Scheme.{u}}

lemma projective_sheafFiber_constantSheafInt (P : X.smallEtaleTopology.Point.{u + 1}) :
    Projective (P.sheafFiber.obj X.constantSheafInt) :=
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  Projective.of_iso (P.sheafFiberConstantSheafIso _).symm inferInstance

variable (Λ : Type (u + 1)) [CommRing Λ] [HasInvertibleExponent Λ X]

/-- The Kummer sequence pulled back along a morphism `φ : C ⟶ 𝔾ₘ` from a sheaf with projective
stalks, with coefficients extended to `Λ`, is short exact. -/
lemma shortExact_kummerSequence_pullback_map_extendScalars
    {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    (((X.kummerSequence (ringChar Λ)).pullback φ).map (extendScalars Λ X)).ShortExact :=
  shortExact_map_extendScalars Λ ((X.kummerSequence_shortExact _
    (isUnit_ringChar_of_hasInvertibleExponent X)).pullback φ) hC

/-- The connecting morphism `Λ ⊗ C ⟶ (μₙ ⊗ Λ)[1]` of the Kummer sequence pulled back along
`φ : C ⟶ 𝔾ₘ`, with coefficients extended to `Λ`. -/
noncomputable def kummerδ {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    (DerivedCategory.singleFunctor _ 0).obj ((extendScalars Λ X).obj C) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))))⟦(1 : ℤ)⟧ :=
  (shortExact_kummerSequence_pullback_map_extendScalars Λ φ hC).singleδ

/-- The connecting morphisms of pulled back Kummer sequences are compatible with
precomposition by `ψ : C' ⟶ C`:
```
Λ ⊗ C' ──Λ ⊗ ψ──▶ Λ ⊗ C
    │                 │ ∂(φ)
    │ ∂(ψ ≫ φ)        ▼
    └──────────▶ (μₙ ⊗ Λ)[1]
```
-/
lemma kummerδ_comp {C C' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (ψ : C' ⟶ C)
    (φ : C ⟶ X.gmSheaf) (hC) (hC') :
    kummerδ Λ (ψ ≫ φ) hC' =
      (DerivedCategory.singleFunctor _ 0).map ((extendScalars Λ X).map ψ) ≫ kummerδ Λ φ hC := by
  have h := (ShortComplex.ShortExact.singleTriangle.map
    (shortExact_kummerSequence_pullback_map_extendScalars Λ (ψ ≫ φ) hC')
    (shortExact_kummerSequence_pullback_map_extendScalars Λ φ hC)
    ((extendScalars Λ X).mapShortComplex.map
      ((X.kummerSequence (ringChar Λ)).pullbackMap φ ψ))).comm₃
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃,
    ShortComplex.ShortExact.singleTriangle.map_hom₁,
    ShortComplex.ShortExact.singleTriangle.map_hom₃] at h
  simp only [Functor.mapShortComplex_map_τ₁, ShortComplex.pullbackMap_τ₁,
    CategoryTheory.Functor.map_id, Functor.mapShortComplex_map_τ₃,
    ShortComplex.pullbackMap_τ₃] at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id] at h
  delta kummerδ
  exact h

instance : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
  (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).left_adjoint_additive

variable [NeZero (ringChar Λ)]

variable (X) in
/-- The constant complex `Λ_X` is `Λ ⊗ ℤ` placed in degree zero: the identification through the
monoidal unit and `Λ ⊗ ℤ ≅ Λ`. -/
noncomputable def constantComplexIsoSingleFunctorExtendScalarsIntOfUnit :
    constantComplex Λ X ≅
      (DerivedCategory.singleFunctor _ 0).obj ((extendScalars Λ X).obj X.constantSheafInt) :=
  (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (extendScalarsConstantZModIso X (n := 0) (by simp)).symm

/-- For `π : X ⟶ S`, the identification `π^*(Λ ⊗ ℤ_S) ≅ Λ ⊗ ℤ_X`. -/
noncomputable def upperStarExtendScalarsConstantSheafIntIso {S : Scheme.{u}} (π : X ⟶ S) :
    (π)^*[ModuleCat.{u + 1} Λ].obj ((extendScalars Λ S).obj S.constantSheafInt) ≅
      (extendScalars Λ X).obj X.constantSheafInt :=
  (upperStarExtendScalarsIso Λ π).app _ ≪≫
    (extendScalars Λ X).mapIso ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} π).app _)

variable (X) in
/-- The constant complex `Λ_X` is `Λ ⊗ ℤ` placed in degree zero: the identification pulled back
from the base `Spec ℤ[1/n]`, so that it is compatible with the derived pullbacks. -/
noncomputable def constantComplexIsoSingleFunctorExtendScalarsInt :
    constantComplex Λ X ≅
      (DerivedCategory.singleFunctor _ 0).obj ((extendScalars Λ X).obj X.constantSheafInt) :=
  (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) X)).symm ≪≫
    L((toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ]).mapIso
      (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit (invertibleExponentBase.{u} Λ) Λ) ≪≫
    (singleFunctorCompLeftDerivedUpperStarIso _ (toInvertibleExponentBase (Λ := Λ) X)).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (upperStarExtendScalarsConstantSheafIntIso Λ (toInvertibleExponentBase (Λ := Λ) X))

omit [NeZero (ringChar Λ)] in
lemma isUnit_ringChar_invertibleExponentBase :
    IsUnit ((ringChar Λ : ℕ) : Γ(invertibleExponentBase.{u} Λ, ⊤)) := by
  simpa using (isUnit_ringChar_invertibleExponentRing Λ).map
    (Scheme.ΓSpecIso (CommRingCat.of (InvertibleExponentRing.{u} Λ))).inv.hom

variable (X) in
/-- The sheaf `Λ_X(1)` of the Tate twist datum is the Tate sheaf `μₙ ⊗ Λ` of `X`: the pullback of
the Tate sheaf of `Spec ℤ[1/n]`, through `(μₙ ⊗ Λ) ⊗ Λ ≅ μₙ ⊗ Λ`, the compatibility of extension
of scalars with pullback, and the identification of the pullback of `μₙ` with `μₙ`. -/
noncomputable def tateTwistSheafOneIso :
    tateTwistSheaf Λ X 1 ≅ (extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ)) :=
  haveI := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit (ringChar Λ)
    (toInvertibleExponentBase (Λ := Λ) X) (isUnit_ringChar_invertibleExponentBase Λ)
  (toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ].mapIso
      (ρ_ (tateSheaf Λ (invertibleExponentBase.{u} Λ))) ≪≫
    (upperStarExtendScalarsIso Λ (toInvertibleExponentBase (Λ := Λ) X)).app _ ≪≫
    (extendScalars Λ X).mapIso
      (asIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf _ (toInvertibleExponentBase X)))

variable (X) in
/-- The Tate twist `Λ_X(1)` is the Tate sheaf `μₙ ⊗ Λ` placed in degree zero. -/
noncomputable def tateTwistObjectOneIso :
    tateTwistObject Λ X 1 ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))) :=
  tateTwistObjectIsoSingleFunctor Λ X 1 ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (tateTwistSheafOneIso X Λ)

variable (X) in
/-- Blueprint `def-pur-affine-line-datum`: The affine-line datum.

The *Kummer class* `κ(u) ∈ H¹(X, Λ(1)) = Hom(Λ_X, Λ_X(1)[1])` of a unit `u` of `X`: the
connecting morphism of the Kummer sequence `0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` pulled back along
`u : ℤ ⟶ 𝔾ₘ`, with coefficients extended to `Λ`. -/
noncomputable def kummerClassOf (u : Γ(X, ⊤)ˣ) :
    constantComplex Λ X ⟶ (tateTwistObject Λ X 1)⟦(1 : ℤ)⟧ :=
  (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
    kummerδ Λ (unitToGmSheaf u)
      (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x)) ≫
    (tateTwistObjectOneIso X Λ).inv⟦(1 : ℤ)⟧'

variable (X) in
lemma kummerClassOf_def (u : Γ(X, ⊤)ˣ) :
    kummerClassOf X Λ u = (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
      kummerδ Λ (unitToGmSheaf u)
        (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x)) ≫
      (tateTwistObjectOneIso X Λ).inv⟦(1 : ℤ)⟧' :=
  rfl

variable (X) in
/-- The Kummer class is additive: `κ(uv) = κ(u) + κ(v)`. -/
lemma kummerClassOf_mul (u v : Γ(X, ⊤)ˣ) :
    kummerClassOf X Λ (u * v) = kummerClassOf X Λ u + kummerClassOf X Λ v := by
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  let A := AddCommGrpCat.of (ULift.{u + 1} (ZMod 0))
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let φ₂ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A ⊞ A) ⟶
      X.gmSheaf := (adj.homEquiv _ _).symm
    (biprod.desc (zmodToGmSections 0 u (pow_zero u)) (zmodToGmSections 0 v (pow_zero v)))
  have hC₂ : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A ⊞ A))) :=
    fun x ↦ Projective.of_iso ((X.uliftPointSmallEtale x).sheafFiberConstantSheafIso _).symm
      inferInstance
  have hu : unitToGmSheaf u =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map biprod.inl ≫ φ₂ := by
    rw [← Adjunction.homEquiv_naturality_left_symm, biprod.inl_desc]
    rfl
  have hv : unitToGmSheaf v =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map biprod.inr ≫ φ₂ := by
    rw [← Adjunction.homEquiv_naturality_left_symm, biprod.inr_desc]
    rfl
  have huv : unitToGmSheaf (u * v) =
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map biprod.inl +
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map biprod.inr) ≫ φ₂ := by
    rw [← Functor.map_add, ← Adjunction.homEquiv_naturality_left_symm, Preadditive.add_comp,
      biprod.inl_desc, biprod.inr_desc, ← zmodToGmSections_zero_mul]
    rfl
  simp only [kummerClassOf]
  rw [huv, hu, hv, kummerδ_comp Λ _ φ₂ hC₂, kummerδ_comp Λ _ φ₂ hC₂, kummerδ_comp Λ _ φ₂ hC₂,
    Functor.map_add, Functor.map_add, Preadditive.add_comp, Preadditive.add_comp,
    Preadditive.comp_add]

end Etale

end AlgebraicGeometry
